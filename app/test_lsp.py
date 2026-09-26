"""LSP.md's Done-when: `./calc --lsp` driven over stdio, and the Emacs
eglot suite when emacs is installed."""

import json
import os
import queue
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)

import api  # noqa: E402
import script  # noqa: E402
from session import loader  # noqa: E402

URI = "file:///work/a.dx"
S1 = "problem stage0.S1.\nftc x^3 + x^2 by ring.\nclose 2.\n"
SLOW = ("close pi*sqrt 3/9 + (x + y + z + w + 1)^24 "
        "- (x + y + z + w + 1)^24.")


def p3_text():
    prob = loader.load(os.path.join(ROOT, "kernel", "problems", "taylor",
                                    "P3_LOWER.json"))
    return "problem taylor.P3_LOWER.\n\n" + "\n".join(
        script.show(st["move"], st["args"])
        for st in prob.proofs["reference"]) + "\n"


class Client:
    def __init__(self, timeout=10, encodings=None, snippets=False):
        self.p = subprocess.Popen(
            [os.path.join(ROOT, "calc"), "--lsp", "--step-timeout",
             str(timeout)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL)
        self.q, self.n, self.version = queue.Queue(), 0, 0
        self.replies, self.notes = {}, []
        threading.Thread(target=self._read, daemon=True).start()
        caps = {"textDocument": {"completion": {"completionItem": {
            "snippetSupport": snippets}}}}
        if encodings:
            caps["general"] = {"positionEncodings": encodings}
        self.init = self.ask("initialize", {"capabilities": caps})
        self.tell("initialized", {})

    def _read(self):
        out = self.p.stdout
        while True:
            n = None
            while True:
                line = out.readline()
                if not line:
                    self.q.put(None)
                    return
                line = line.strip()
                if not line:
                    break
                k, _, v = line.partition(b":")
                if k.lower() == b"content-length":
                    n = int(v)
            self.q.put(json.loads(out.read(n)))

    def _send(self, obj):
        obj["jsonrpc"] = "2.0"
        data = json.dumps(obj).encode()
        self.p.stdin.write(b"Content-Length: %d\r\n\r\n" % len(data) + data)
        self.p.stdin.flush()

    def _pump(self, until, timeout):
        end = time.time() + timeout
        while not until():
            left = end - time.time()
            if left <= 0:
                raise AssertionError("timed out waiting for the server")
            try:
                m = self.q.get(timeout=left)
            except queue.Empty:
                continue
            if m is None:
                raise AssertionError("the server exited")
            if "id" in m and "method" not in m:
                self.replies[m["id"]] = m
            else:
                self.notes.append(m)

    def request(self, method, params):
        self.n += 1
        self._send({"id": self.n, "method": method, "params": params})
        return self.n

    def reply(self, rid, timeout=30):
        self._pump(lambda: rid in self.replies, timeout)
        return self.replies.pop(rid)

    def ask(self, method, params, timeout=30):
        r = self.reply(self.request(method, params), timeout)
        if "error" in r:
            raise AssertionError(r["error"])
        return r["result"]

    def tell(self, method, params):
        self._send({"method": method, "params": params})

    # ------------------------------------------------ documents

    def open(self, text, uri=URI):
        self.version += 1
        self.text = text
        self.tell("textDocument/didOpen", {"textDocument": {
            "uri": uri, "languageId": "dx", "version": self.version,
            "text": text}})

    def change(self, text, uri=URI):
        self.version += 1
        self.text = text
        self.tell("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": self.version},
            "contentChanges": [{"text": text}]})

    def last(self, method, version=None):
        for m in reversed(self.notes):
            if m["method"] == method and (version is None or
                                          m["params"].get("version") ==
                                          version):
                return m["params"]
        return None

    def settled(self, timeout=120):
        """Wait until the current version is checked as far as it goes;
        its diagnostics."""
        v = self.version

        def done():
            p = self.last("dx/progress", v)
            return p is not None and p["running"] is None
        self._pump(done, timeout)
        return self.last("textDocument/publishDiagnostics", v)["diagnostics"]

    def running(self, line, timeout=60):
        v = self.version

        def busy():
            p = self.last("dx/progress", v)
            return p is not None and p["running"] is not None and \
                p["running"]["start"]["line"] == line
        self._pump(busy, timeout)
        return self.last("dx/progress", v)["running"]

    def goals(self, line, character=0, uri=URI):
        return self.ask("dx/goals", {"textDocument": {"uri": uri},
                                     "position": {"line": line,
                                                  "character": character}})

    def stats(self, uri=URI):
        return self.ask("dx/stats", {"textDocument": {"uri": uri}})

    def close(self):
        try:
            self.ask("shutdown", None, timeout=10)
            self.tell("exit", None)
            return self.p.wait(10)
        finally:
            if self.p.poll() is None:
                self.p.kill()


class Lsp(unittest.TestCase):
    def client(self, **kw):
        c = Client(**kw)
        self.addCleanup(lambda: c.p.poll() is None and c.p.kill())
        return c

    def test_s1_checks_to_proved(self):
        c = self.client()
        caps = c.init["capabilities"]
        self.assertEqual(caps["positionEncoding"], "utf-16")
        self.assertEqual(caps["textDocumentSync"]["change"], 1)
        c.open(S1)
        self.assertEqual(c.settled(), [])
        self.assertEqual(c.last("dx/progress", c.version)["checkedEnd"],
                         {"line": 2, "character": 8})
        g = c.goals(3)
        self.assertEqual((g["report"], g["checked"]), ("Proved.", True))
        # inside the first tactic: the header's goal, still unproved
        g = c.goals(1, 3)
        self.assertEqual(g["node"], "n0")
        self.assertEqual(c.close(), 0)

    def test_a_refusal_is_an_error_and_its_code_action_fixes_it(self):
        c = self.client()
        c.open("goal Int[t = 0 .. pi] 2*t*sin t == ?A.\n"
               "ftc sin t - t*cos t.\n")
        diags = c.settled()
        self.assertEqual(len(diags), 1, diags)
        d = diags[0]
        self.assertEqual((d["severity"], d["code"]), (1, "ftc-check-failed"))
        self.assertEqual(d["range"], {"start": {"line": 1, "character": 0},
                                      "end": {"line": 1, "character": 20}})
        self.assertIn("1/2 times the integrand", d["message"])
        # the checked prefix stops at the header
        self.assertEqual(c.last("dx/progress", c.version)["checkedEnd"],
                         {"line": 0, "character": 38})
        acts = c.ask("textDocument/codeAction", {
            "textDocument": {"uri": URI}, "range": d["range"],
            "context": {"diagnostics": diags}})
        self.assertEqual(len(acts), 1)
        edit = acts[0]["edit"]["changes"][URI][0]
        self.assertEqual(edit["newText"], "ftc 2*(sin t - t*cos t) by ring.")
        lines = c.text.split("\n")
        lines[1] = edit["newText"]
        c.change("\n".join(lines))
        self.assertEqual(c.settled(), [])
        self.assertEqual(c.last("dx/progress", c.version)["checkedEnd"],
                         {"line": 1, "character": 32})
        self.assertTrue(c.goals(2)["checked"])
        # no refusal, no action
        self.assertEqual(c.ask("textDocument/codeAction", {
            "textDocument": {"uri": URI}, "range": d["range"],
            "context": {"diagnostics": []}}), [])

    def test_an_edit_in_the_middle_resends_only_what_changed(self):
        c = self.client()
        text = p3_text()
        c.open(text)
        self.assertEqual(c.settled(), [])
        self.assertEqual(c.goals(text.count("\n"))["report"], "Proved.")
        sent = c.stats()["tactics"]
        spans = script.spans(text)
        self.assertEqual(sent, len(spans) - 1)
        mid = spans[len(spans) // 2]
        # a comment and spacing change nothing: nothing is re-sent
        c.change(text[:mid[0]] + "(* why *)  " + text[mid[0]:])
        self.assertEqual(c.settled(), [])
        self.assertEqual(c.stats()["tactics"], sent)
        # a wrong sentence: that sentence only, then nothing after it
        c.change(text[:mid[0]] + "close 0." + text[mid[1]:])
        diags = c.settled()
        self.assertEqual([d["severity"] for d in diags], [1])
        self.assertEqual(c.stats()["tactics"], sent + 1)
        # back to the old text: every answer is known
        c.change(text)
        self.assertEqual(c.settled(), [])
        self.assertEqual(c.stats()["tactics"], sent + 1)
        self.assertEqual(c.goals(text.count("\n"))["report"], "Proved.")

    def test_a_slow_sentence_edited_below_runs_on_and_times_out_once(self):
        c = self.client(timeout=4)
        head = ("goal pi*sqrt 3/9 == ?A.\n"
                "fact h := sqrt_sq_val with a := 3.\n")
        c.open(head + SLOW + "\n")
        c.running(2)
        sent = c.stats()["tactics"]
        # an edit below the running sentence: its answer still counts
        c.change(head + SLOW + "\n(* next *) close 1.\n")
        diags = c.settled()
        self.assertEqual([(d["severity"], d["code"]) for d in diags],
                         [(2, "timeout")])
        self.assertEqual(diags[0]["range"]["start"]["line"], 2)
        self.assertEqual(c.stats()["tactics"], sent)
        # the timeout is remembered until that sentence changes
        c.change(head + SLOW + "\n(* next *) close 2.\n")
        c.settled()
        self.assertEqual(c.stats()["tactics"], sent)
        # an edit of the running sentence cancels it; the final text wins
        c.change(head + SLOW.replace("^24", "^23") + "\n")
        c.running(2)
        c.change(head + "close pi/(3*sqrt 3) by field using h.\n")
        self.assertEqual(c.settled(), [])
        self.assertEqual(c.goals(3)["report"], "Proved.")

    def test_many_edits_keep_the_session_bounded(self):
        c = self.client()
        c.open(S1)
        c.settled()
        first = c.stats()["session"]
        for k in range(60):
            c.change(f"problem stage0.S1.\nftc x^3 + x^2 + {k} by ring.\n"
                     "close 2.\n")
            c.settled()
        c.change(S1)
        self.assertEqual(c.settled(), [])
        st = c.stats()
        self.assertLessEqual(st["nodes"], 2 * st["path"] + 50, st)
        self.assertNotEqual(st["session"], first)  # a compaction happened
        self.assertEqual(c.goals(3)["report"], "Proved.")

    def test_completion_offers_every_template(self):
        c = self.client(snippets=True)
        c.open(S1)
        items = c.ask("textDocument/completion", {
            "textDocument": {"uri": URI},
            "position": {"line": 3, "character": 0}})["items"]
        want = api.templates({})["templates"]
        self.assertEqual(len(items), len(want))
        self.assertEqual(len(items), 10)
        sub = next(i for i in items if i["label"] == "int_subst")
        self.assertEqual(sub["insertTextFormat"], 2)
        self.assertEqual(sub["insertText"], "int_subst x := ${1:_} as t "
                         "from ${2:_} to ${3:_} by ring.")
        plain = self.client().ask("textDocument/completion", {
            "textDocument": {"uri": URI},
            "position": {"line": 0, "character": 0}})["items"]
        sub = next(i for i in plain if i["label"] == "int_subst")
        self.assertEqual((sub["insertTextFormat"], sub["insertText"]),
                         (1, "int_subst x := _ as t from _ to _ by ring."))

    def test_positions_after_an_astral_character(self):
        text = "problem stage0.S1.\n(* \U0001d465 *) ftc x^3 by ring.\n"
        got = {}
        for enc in (None, ["utf-32", "utf-16"]):
            c = self.client(encodings=enc)
            c.open(text)
            d = c.settled()[0]["range"]
            got[c.init["capabilities"]["positionEncoding"]] = d
            # goals at the start of that sentence: the header's node
            self.assertEqual(c.goals(1, d["start"]["character"])["node"],
                             "n0")
        self.assertEqual(got["utf-32"]["start"], {"line": 1, "character": 8})
        self.assertEqual(got["utf-16"]["start"], {"line": 1, "character": 9})
        self.assertEqual(got["utf-16"]["end"]["character"],
                         got["utf-32"]["end"]["character"] + 1)

    def test_a_bad_header_is_the_only_diagnostic(self):
        c = self.client()
        c.open("problem no.such.\nftc x.\n")
        diags = c.settled()
        self.assertEqual([(d["severity"], d["range"]["start"]["line"])
                          for d in diags], [(1, 0)])
        self.assertIn("unknown-problem", diags[0]["message"])
        self.assertIsNone(c.goals(1))
        c.change(S1)
        self.assertEqual(c.settled(), [])

    def test_close_clears_and_protocol_edges(self):
        c = self.client()
        c.open(S1)
        c.settled()
        c.tell("textDocument/didClose", {"textDocument": {"uri": URI}})
        c._pump(lambda: c.notes[-1]["method"] ==
                "textDocument/publishDiagnostics" and
                c.notes[-1]["params"]["diagnostics"] == [], 30)
        r = c.reply(c.request("no/such", {}))
        self.assertEqual(r["error"]["code"], -32601)
        c.tell("exit", None)  # without shutdown
        self.assertEqual(c.p.wait(10), 1)

    def test_hint_answers_for_the_node_at_point(self):
        c = self.client()
        c.open(S1)
        c.settled()
        h = c.ask("dx/hint", {"textDocument": {"uri": URI},
                              "position": {"line": 1, "character": 0},
                              "rung": 1})
        self.assertEqual(h["node"], "n0")
        self.assertNotIn("error", h)


@unittest.skipIf(shutil.which("emacs") is None, "emacs is not installed")
class Emacs(unittest.TestCase):
    def test_ert_suite(self):
        d = tempfile.mkdtemp()
        for name, text in (("s1.dx", S1), ("p3.dx", p3_text())):
            with open(os.path.join(d, name), "w") as f:
                f.write(text)
        env = dict(os.environ, DX_DIR=d)
        r = subprocess.run(
            ["emacs", "--batch", "-Q", "-L", ".", "-l", "dx-mode.el", "-l",
             "test-dx-mode.el", "-f", "ert-run-tests-batch-and-exit"],
            cwd=os.path.join(ROOT, "emacs"), env=env, capture_output=True,
            text=True, timeout=900)
        self.assertEqual(r.returncode, 0, r.stdout[-3000:] + r.stderr[-3000:])
        self.assertIn("0 unexpected", r.stdout + r.stderr)


if __name__ == "__main__":
    unittest.main()
