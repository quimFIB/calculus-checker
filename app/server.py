"""http.server over api.handle (app/API.md). Binds 127.0.0.1 only.

Untrusted, and holds nothing: it decodes a request, calls api.handle, and
encodes the answer.
"""

import argparse
import json
import os
import sys
from http.server import (BaseHTTPRequestHandler, HTTPServer,
                         ThreadingHTTPServer)
from urllib.parse import parse_qsl, urlsplit

import api
import backend
from assist import integrate

# TIMEOUT.md: where API requests run. In-process unless serve() (or a test)
# installs a backend.Worker.
BACKEND = backend.Backend()
# EVAL.md review 5: SymPy runs here, outside the worker; serve() sets it
PROPOSER = integrate.Proposer(None)

MAX_BODY = 1 << 20  # a move is a few hundred bytes
PAGE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "page",
                    "index.html")  # PAGE.md: the page
KATEX = os.path.join(os.path.dirname(PAGE), "katex")  # UI.md: vendored
MATHLIVE = os.path.join(os.path.dirname(PAGE), "mathlive")  # PRETTY.md
# PRETTY.md review 4: routes that only parse, answered in this process so
# that a keystroke never waits behind a step (or is hit by its Cancel)
LOCAL = {("POST", "/layout"), ("POST", "/untex"), ("GET", "/templates")}
TYPES = {".js": "text/javascript", ".css": "text/css", ".woff2": "font/woff2"}


def katex_file(path, root=KATEX):
    """The vendored file for /katex/<name> or /katex/fonts/<name> (or
    /mathlive/..., with root MATHLIVE), or None: one fixed directory,
    names only, no traversal."""
    parts = path.split("/")[2:]
    if not 1 <= len(parts) <= 2 or (len(parts) == 2 and parts[0] != "fonts"):
        return None
    name = parts[-1]
    ext = os.path.splitext(name)[1]
    if ext not in TYPES or not name or name.startswith(".") or "\\" in name:
        return None
    full = os.path.join(root, *parts)
    return (full, TYPES[ext]) if os.path.isfile(full) else None


class Handler(BaseHTTPRequestHandler):
    server_version = "calc/0"

    def _send(self, status, obj):
        data = json.dumps(obj).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _file(self, path, ctype):
        with open(path, "rb") as f:
            data = f.read()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        url = urlsplit(self.path)
        if url.path in ("/", "/index.html"):
            return self._file(PAGE, "text/html; charset=utf-8")
        if url.path.startswith(("/katex/", "/mathlive/")):
            found = katex_file(url.path, KATEX if url.path.startswith(
                "/katex/") else MATHLIVE)
            if found is None:
                return self._send(404, {"error": {
                    "code": "unknown-route",
                    "message": f"no file {url.path}"}})
            return self._file(*found)
        if ("GET", url.path) in LOCAL:
            return self._send(*api.handle("GET", url.path,
                                          dict(parse_qsl(url.query))))
        self._send(*BACKEND.handle("GET", url.path,
                                   dict(parse_qsl(url.query))))

    def do_POST(self):
        url = urlsplit(self.path)
        if url.path == "/cancel":  # TIMEOUT.md: never waits for the step
            killed = PROPOSER.cancel()  # EVAL.md: a proposal is stopped too
            out = BACKEND.cancel()
            return self._send(200, {"cancelled": out["cancelled"] or killed})
        try:
            n = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            n = -1
        if not 0 <= n <= MAX_BODY:  # a negative length would read to EOF
            return self._send(400, {"error": {"code": "bad-request",
                                              "message": "bad Content-Length"}})
        try:
            body = json.loads(self.rfile.read(n) or b"{}")
        except (ValueError, UnicodeDecodeError) as e:
            return self._send(400, {"error": {"code": "bad-json",
                                              "message": str(e)}})
        if ("POST", url.path) in LOCAL:
            return self._send(*api.handle("POST", url.path, body))
        if url.path == "/evaluate":  # EVAL.md: propose here, check there
            if not isinstance(body, dict):
                return self._send(400, {"error": {
                    "code": "bad-request",
                    "message": "the body is a JSON object"}})
            return self._send(*integrate.evaluate(BACKEND.handle, PROPOSER,
                                                  body))
        self._send(*BACKEND.handle("POST", url.path, body))

    def log_message(self, fmt, *args):
        if self.server.verbose:
            super().log_message(fmt, *args)


def serve(port=8765, verbose=False, step_timeout=10.0, work_dir=None,
          sympy=None, eval_timeout=5.0):
    """Serve until interrupted. Requests are taken on threads, so that
    /cancel is heard while a step runs, but reach the kernel one at a
    time, on purpose: the kernel's module-level tables (handles, lineages,
    memo caches) were not written for concurrent steps, and there is one
    learner. The kernel runs in a worker process (TIMEOUT.md)."""
    global BACKEND, PROPOSER
    BACKEND = backend.Worker(step_timeout, work_dir)
    PROPOSER = integrate.Proposer(integrate.find_python(sympy), eval_timeout)
    srv = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    srv.verbose = verbose
    print(f"calc: http://127.0.0.1:{srv.server_address[1]}/ (the check-mode "
          "page; PAGE.md)", flush=True)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        srv.server_close()
        BACKEND.close()


def main(argv=None):
    p = argparse.ArgumentParser(description="the calculus checker's API")
    p.add_argument("--port", type=int, default=8765)
    p.add_argument("-v", "--verbose", action="store_true")
    p.add_argument("--work", default="calc-work",
                   help="where work files are saved (PERSIST.md); "
                        "relative to the current directory")
    p.add_argument("--step-timeout", type=float, default=10.0,
                   help="seconds a request may run before it is stopped "
                        "(TIMEOUT.md); 0 for none")
    p.add_argument("--sympy", default=None,
                   help="a Python that has SymPy, for evaluating integrals "
                        "(EVAL.md); default $CALC_SYMPY, else python3")
    p.add_argument("--eval-timeout", type=float, default=5.0,
                   help="seconds SymPy may take to propose (EVAL.md)")
    p.add_argument("--lsp", action="store_true",
                   help="run the .dx language server on stdin and stdout "
                        "(LSP.md), for editors; nothing is saved")
    a = p.parse_args(argv)
    if a.lsp:
        import lsp
        return lsp.main(a.step_timeout, a.sympy, a.eval_timeout)
    serve(a.port, a.verbose, a.step_timeout, os.path.abspath(a.work),
          a.sympy, a.eval_timeout)


if __name__ == "__main__":
    sys.exit(main())
