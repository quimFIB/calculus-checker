"""The .dx language server (app/LSP.md): LSP 3.17 over stdio, stdlib only.

Untrusted, and a client of the API like the page: it sends sentences to
the kernel through TIMEOUT.md's worker and reports what comes back. The
whole document is checked, incrementally: every answer is cached under
(parent node, sentence), so an edit sends only the sentences whose answer
is not known yet (LSP.md, review 1).

Threads: the reader answers requests from the cache and never waits on the
worker; one checker thread steps sentences; a hint gets a thread of its
own. One lock guards the documents, another the output.
"""

import json
import os
import re
import sys
import threading

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import api  # noqa: E402
import backend  # noqa: E402
import script  # noqa: E402
from assist import integrate  # noqa: E402

COMPACT_SLACK = 50  # LSP.md review 3: nodes > 2 * path + this -> rebuild
_LINE = re.compile(r"\r\n|\r|\n")


# ---------------------------------------------------------------- positions

class Lines:
    """Offsets <-> LSP positions for one text, in UTF-16 or UTF-32 units."""

    def __init__(self, text, encoding):
        self.text, self.wide = text, encoding == "utf-16"
        self.starts = [0] + [m.end() for m in _LINE.finditer(text)]

    def _units(self, s):
        if not self.wide:
            return len(s)
        return sum(2 if ord(c) > 0xFFFF else 1 for c in s)

    def position(self, off):
        lo, hi = 0, len(self.starts) - 1
        while lo < hi:  # the last line start <= off
            mid = (lo + hi + 1) // 2
            if self.starts[mid] <= off:
                lo = mid
            else:
                hi = mid - 1
        a = self.starts[lo]
        return {"line": lo, "character": self._units(self.text[a:off])}

    def offset(self, pos):
        line = min(max(pos.get("line", 0), 0), len(self.starts) - 1)
        a = self.starts[line]
        end = self.starts[line + 1] if line + 1 < len(self.starts) \
            else len(self.text)
        want, units, i = pos.get("character", 0), 0, a
        while i < end and units < want:
            units += 2 if self.wide and ord(self.text[i]) > 0xFFFF else 1
            i += 1
        return i

    def range(self, a, b):
        return {"start": self.position(a), "end": self.position(b)}


# ---------------------------------------------------------------- documents

class Doc:
    def __init__(self, uri, text, version):
        self.uri, self.text, self.version = uri, text, version
        self.gen = 0
        self.session = None       # the API session of the current header
        self.header = None        # its header sentence, stripped
        self.header_fail = None   # (header, payload) of a refused header
        self.root = None          # the rendered n0
        self.results = {}         # (parent, sentence) -> (kind, payload)
        self.nodes = 0            # nodes this session holds
        self.path = []            # [(start, end, node)] checked, in order
        self.failure = None       # (start, end, kind, payload)
        self.pending = None       # where the first unchecked sentence starts
        self.running = None       # (start, end, key) being checked
        self.closed = False


def _norm(sentence):
    return script.strip_sentence(sentence)


class Server:
    def __init__(self, inp, out, backend_, proposer=None):
        self.inp, self.out, self.backend = inp, out, backend_
        self.proposer = proposer or integrate.Proposer(None)
        self.evaluating = None    # the request id of the running dx/evaluate
        self.wlock = threading.Lock()
        self.dlock = threading.Lock()
        self.docs = {}
        self.dirty = []
        self.wake = threading.Condition(self.dlock)
        self.encoding = "utf-16"
        self.snippets = False
        self.ready = False        # after `initialized`
        self.shut = False
        self.cancelled = set()    # request ids of hints the client cancelled
        self.tactics = 0          # /tactic requests sent (dx/stats)
        self.templates = api.templates({})["templates"]

    # ------------------------------------------------ framing

    def read(self):
        n = None
        while True:
            line = self.inp.readline()
            if not line:
                return None
            line = line.strip()
            if not line:
                break
            k, _, v = line.decode("ascii", "replace").partition(":")
            if k.strip().lower() == "content-length":
                n = int(v.strip())
        body = self.inp.read(n or 0)
        return json.loads(body.decode("utf-8"))

    def send(self, obj):
        obj["jsonrpc"] = "2.0"
        data = json.dumps(obj).encode("utf-8")
        with self.wlock:
            self.out.write(b"Content-Length: %d\r\n\r\n" % len(data) + data)
            self.out.flush()

    def notify(self, method, params):
        if self.ready:
            self.send({"method": method, "params": params})

    # ------------------------------------------------ the loop

    def run(self):
        threading.Thread(target=self._checker, daemon=True).start()
        while True:
            msg = self.read()
            if msg is None:
                return 1
            method, rid = msg.get("method"), msg.get("id")
            if method == "exit":
                return 0 if self.shut else 1
            handler = getattr(self, "on_" + (method or "").replace("/", "_")
                              .replace("$", "S"), None)
            if handler is None:
                if rid is not None:
                    self.send({"id": rid, "error": {
                        "code": -32601, "message": f"no method {method}"}})
                continue
            try:
                result = handler(msg.get("params") or {}, rid)
            except Exception as e:  # never let one message stop the server
                if rid is not None:
                    self.send({"id": rid, "error": {
                        "code": -32603, "message": f"{type(e).__name__}: {e}"}})
                continue
            if rid is not None and result is not _LATER:
                self.send({"id": rid, "result": result})

    # ------------------------------------------------ lifecycle

    def on_initialize(self, p, _):
        caps = p.get("capabilities") or {}
        offered = (caps.get("general") or {}).get("positionEncodings") or []
        self.encoding = "utf-32" if "utf-32" in offered else "utf-16"
        item = (((caps.get("textDocument") or {}).get("completion") or {})
                .get("completionItem") or {})
        self.snippets = bool(item.get("snippetSupport"))
        return {"capabilities": {
                    "positionEncoding": self.encoding,
                    "textDocumentSync": {"openClose": True, "change": 1},
                    "completionProvider": {"resolveProvider": False},
                    "codeActionProvider": True},
                "serverInfo": {"name": "calc-dx", "version": "1"}}

    def on_initialized(self, p, _):
        self.ready = True

    def on_shutdown(self, p, _):
        self.shut = True
        return None

    def on_S_cancelRequest(self, p, _):
        self.cancelled.add(p.get("id"))
        if p.get("id") is not None and p.get("id") == self.evaluating:
            self.proposer.cancel()  # EVAL.md: kills SymPy, not the worker

    # ------------------------------------------------ documents

    def on_textDocument_didOpen(self, p, _):
        td = p["textDocument"]
        with self.dlock:
            self.docs[td["uri"]] = Doc(td["uri"], td["text"],
                                       td.get("version", 0))
            self._mark(td["uri"])

    def on_textDocument_didChange(self, p, _):
        td = p["textDocument"]
        changes = p.get("contentChanges") or []
        with self.dlock:
            doc = self.docs.get(td["uri"])
            if doc is None or not changes:
                return
            doc.text = changes[-1]["text"]  # full sync
            doc.version = td.get("version", doc.version)
            doc.gen += 1
            stale = doc.running is not None and self._walk(doc)[2] != \
                doc.running[2]
            self._mark(td["uri"])
        if stale:  # review 2: only what the edit made stale is cancelled
            self.backend.cancel()

    def on_textDocument_didClose(self, p, _):
        uri = p["textDocument"]["uri"]
        with self.dlock:
            doc = self.docs.pop(uri, None)
            if doc is None:
                return
            doc.closed = True
            doc.gen += 1
            sid = doc.session
        if doc.running is not None:
            self.backend.cancel()
        self.notify("textDocument/publishDiagnostics",
                    {"uri": uri, "diagnostics": []})
        if sid:
            threading.Thread(target=self._drop, args=(sid,),
                             daemon=True).start()

    def _mark(self, uri):
        if uri not in self.dirty:
            self.dirty.append(uri)
        self.wake.notify()

    def _drop(self, sid):
        self.backend.handle("POST", "/drop", {"session": sid})

    # ------------------------------------------------ checking

    def _walk(self, doc):
        """Through the cache: (path, failure, first miss key, miss span)
        for the document's current text. Holds dlock."""
        spans = script.spans(doc.text)
        if not spans or doc.session is None or \
                _norm(doc.text[spans[0][0]:spans[0][1]]) != doc.header:
            head = _norm(doc.text[spans[0][0]:spans[0][1]]) if spans else None
            return [], None, ("header", head), spans[0] if spans else None
        path = [(spans[0][0], spans[0][1], doc.root)]
        parent = doc.root["node"]
        for a, b in spans[1:]:
            sentence = _norm(doc.text[a:b])
            if not sentence:  # a comment alone checks nothing
                continue
            key = (parent, sentence)
            res = doc.results.get(key)
            if res is None:
                return path, None, key, (a, b)
            if res[0] != "node":
                return path, (a, b, res[0], res[1]), None, None
            path.append((a, b, res[1]))
            parent = res[1]["node"]
        return path, None, None, None

    def _checker(self):
        while True:
            with self.dlock:
                while not self.dirty:
                    self.wake.wait()
                uri = self.dirty.pop(0)
                doc = self.docs.get(uri)
            if doc is not None:
                try:
                    self._check(doc)
                except Exception as e:  # report it, keep serving
                    self.notify("window/logMessage", {
                        "type": 1, "message": f"dx: {type(e).__name__}: {e}"})

    def _check(self, doc):
        while not doc.closed:
            with self.dlock:
                text, version, gen = doc.text, doc.version, doc.gen
                path, failure, miss, span = self._walk(doc)
                doc.path, doc.failure = path, failure
                doc.pending = failure[0] if failure else \
                    span[0] if span else None
                doc.running = None
                if miss is not None and miss[0] == "header":
                    head = miss[1]
                    if head is None or (doc.header_fail and
                                        doc.header_fail[0] == head):
                        self._publish(doc, text, version)
                        return
                    old, doc.session = doc.session, None
                    header_span = span
                    doc.running = (span[0], span[1], miss)
                elif miss is not None:
                    doc.running = (span[0], span[1], miss)
                    sid = doc.session
                self._publish(doc, text, version)
            if miss is None:
                self._compact(doc)
                return
            if miss[0] == "header":
                self._open(doc, text, header_span, old, gen)
                continue
            parent, sentence = miss
            self.tactics += 1
            status, body = self.backend.handle(
                "POST", "/tactic", {"session": sid, "node": parent,
                                    "text": sentence})
            with self.dlock:
                doc.running = None
                if status != 200:
                    err = body.get("error", {})
                    if err.get("code") == "unknown-session":
                        doc.session, doc.header = None, None  # start over
                        doc.results.clear()
                        continue
                    doc.results[miss] = ("error", err)
                elif "timeout" in body:
                    if not body["timeout"].get("cancelled"):
                        doc.results[miss] = ("timeout", body["timeout"])
                elif "refusal" in body:
                    doc.results[miss] = ("refusal", body["refusal"])
                else:
                    doc.results[miss] = ("node", body)
                    doc.nodes += 1

    def _open(self, doc, text, span, old, gen):
        """Install the header's goal: a new session (LSP.md)."""
        if old:
            self._drop(old)
        header = text[span[0]:span[1]]
        status, body = self.backend.handle("POST", "/session",
                                           {"header": header})
        with self.dlock:
            doc.results.clear()
            doc.nodes = 0
            if status == 200 and "session" in body:
                if doc.gen != gen and _norm(doc.text[span[0]:span[1]]) != \
                        _norm(header) or doc.closed:
                    self._drop(body["session"])
                    return
                doc.session, doc.header, doc.root = \
                    body["session"], _norm(header), body
                doc.header_fail = None
            else:
                payload = body.get("refusal") or body.get("error") or \
                    {"code": "timeout", "message": "the header ran out of time"}
                doc.header, doc.header_fail = None, (_norm(header), payload)

    def _compact(self, doc):
        """Review 3: too many dead nodes -> a fresh session, the path
        replayed into it by the next check."""
        with self.dlock:
            if doc.nodes <= 2 * len(doc.path) + COMPACT_SLACK:
                return
            old, doc.session, doc.header = doc.session, None, None
            doc.results.clear()
            self._mark(doc.uri)
        self._drop(old)

    # ------------------------------------------------ reporting

    def _publish(self, doc, text, version):
        """Diagnostics and dx/progress for `text`. Holds dlock."""
        lines = Lines(text, self.encoding)
        diags = []
        spans = script.spans(text)
        if doc.header_fail and spans and \
                doc.header_fail[0] == _norm(text[spans[0][0]:spans[0][1]]):
            p = doc.header_fail[1]
            diags.append({"range": lines.range(*spans[0]), "severity": 1,
                          "source": "dx", "code": p.get("code"),
                          "message": f"{p.get('code')}: {p.get('message')}"})
        if doc.failure:
            a, b, kind, p = doc.failure
            if kind == "timeout":
                diags.append({"range": lines.range(a, b), "severity": 2,
                              "source": "dx", "code": "timeout",
                              "message": p.get("message", "stopped") +
                              "; it was not refused"})
            else:
                diags.append({"range": lines.range(a, b), "severity": 1,
                              "source": "dx", "code": p.get("code"),
                              "message": _refusal_text(p)})
        self.notify("textDocument/publishDiagnostics",
                    {"uri": doc.uri, "version": version,
                     "diagnostics": diags})
        self.notify("dx/progress", {
            "uri": doc.uri, "version": version,
            "checkedEnd": lines.position(doc.path[-1][1]) if doc.path
            else None,
            "running": lines.range(doc.running[0], doc.running[1])
            if doc.running else None})

    # ------------------------------------------------ requests

    def _node_at(self, doc, pos):
        """The checked node after the last sentence ending at or before
        pos, and whether pos is inside the checked prefix."""
        off = Lines(doc.text, self.encoding).offset(pos)
        best = doc.path[0][2]  # the header's node, even inside the header
        for a, b, node in doc.path[1:]:
            if b > off:
                break
            best = node
        return best, doc.pending is None or off <= doc.pending

    def on_dx_goals(self, p, _):
        with self.dlock:
            doc = self.docs.get(p["textDocument"]["uri"])
            if doc is None or not doc.path:
                return None
            node, checked = self._node_at(doc, p["position"])
            return None if node is None else dict(node, checked=checked)

    def on_dx_hint(self, p, rid):
        with self.dlock:
            doc = self.docs.get(p["textDocument"]["uri"])
            node, _ = self._node_at(doc, p["position"]) if doc and doc.path \
                else (None, None)
            sid = doc.session if doc else None
        if node is None:
            return {"refusal": {"code": "no-goal",
                                "message": "check the header first"}}
        rung = str(int(p.get("rung", 1)))

        def work():
            _, body = self.backend.handle("GET", "/hint", {
                "session": sid, "node": node["node"], "rung": rung})
            if rid in self.cancelled:
                self.cancelled.discard(rid)
                self.send({"id": rid, "error": {"code": -32800,
                                                "message": "cancelled"}})
            else:
                self.send({"id": rid, "result": dict(body, node=node["node"])})
        threading.Thread(target=work, daemon=True).start()
        return _LATER

    def on_dx_evaluate(self, p, rid):
        """EVAL.md: {textDocument, position} evaluates the goal there;
        {textDocument?, term} a typed integral. Answered on a thread."""
        if "term" in p:
            uri = (p.get("textDocument") or {}).get("uri")
            with self.dlock:
                doc = self.docs.get(uri)
                sig = (doc.root or {}).get("functions") if doc else None
            body = {"term": p["term"], "functions": sig or {}}
        else:
            with self.dlock:
                doc = self.docs.get(p["textDocument"]["uri"])
                node, _ = self._node_at(doc, p["position"]) \
                    if doc and doc.path else (None, None)
                sid = doc.session if doc else None
            if node is None:
                return {"status": "no-goal",
                        "message": "check the header first"}
            body = {"session": sid, "node": node["node"]}

        def work():
            self.evaluating = rid
            try:
                _, out = integrate.evaluate(self.backend.handle,
                                            self.proposer, body)
            finally:
                self.evaluating = None
            if rid in self.cancelled:
                self.cancelled.discard(rid)
                self.send({"id": rid, "error": {"code": -32800,
                                                "message": "cancelled"}})
            else:
                self.send({"id": rid, "result": out})
        threading.Thread(target=work, daemon=True).start()
        return _LATER

    def on_dx_stats(self, p, _):
        with self.dlock:
            doc = self.docs.get(p["textDocument"]["uri"])
            return {"tactics": self.tactics,
                    "nodes": doc.nodes if doc else 0,
                    "path": len(doc.path) if doc else 0,
                    "session": doc.session if doc else None}

    def on_textDocument_completion(self, p, _):
        items = []
        for t in self.templates:
            tpl = t["template"]
            if self.snippets:
                k = iter(range(1, 100))
                text = re.sub(r"(?<![A-Za-z0-9_])_(?![A-Za-z0-9_])",
                              lambda m: "${%d:_}" % next(k), tpl)
                fmt = 2
            else:
                text, fmt = tpl, 1
            items.append({"label": t["move"], "kind": 15, "detail": tpl,
                          "documentation": t["usage"], "insertText": text,
                          "insertTextFormat": fmt, "filterText": t["move"]})
        return {"isIncomplete": False, "items": items}

    def on_textDocument_codeAction(self, p, _):
        with self.dlock:
            doc = self.docs.get(p["textDocument"]["uri"])
            if doc is None or not doc.failure or doc.failure[2] != "refusal":
                return []
            a, b, _, ref = doc.failure
            sug = (ref.get("stuck") or {}).get("suggest")
            if not sug:
                return []
            lines = Lines(doc.text, self.encoding)
            r = p.get("range") or {}
            lo = lines.offset(r.get("start", {}))
            hi = lines.offset(r.get("end", {}))
            if hi < a or lo > b:
                return []
            new = "\n".join(sug)
            return [{"title": f"Use this: {new}", "kind": "quickfix",
                     "isPreferred": True,
                     "edit": {"changes": {doc.uri: [
                         {"range": lines.range(a, b), "newText": new}]}}}]


_LATER = object()  # a request answered later, from another thread


def _refusal_text(r):
    out = f"{r.get('code')}: {r.get('message')}"
    if r.get("residual"):
        out += f"\nresidual: {r['residual']}"
    st = r.get("stuck")
    if st:
        out += "\n" + st.get("headline", "")
        out += "".join("\n - " + ln for ln in st.get("lines", []))
        if st.get("suggest"):
            out += "\nsuggestion: " + " ".join(st["suggest"])
    return out


def main(step_timeout=10.0, sympy=None, eval_timeout=5.0):
    api.WORK_DIR = None  # the buffer is the work; nothing is saved
    out = os.fdopen(os.dup(1), "wb")
    os.dup2(2, 1)
    sys.stdout = sys.stderr
    worker = backend.Worker(step_timeout, None)
    try:
        proposer = integrate.Proposer(integrate.find_python(sympy),
                                      eval_timeout)
        code = Server(sys.stdin.buffer, out, worker, proposer).run()
    finally:
        worker.close()
    sys.exit(code)


if __name__ == "__main__":
    main()
