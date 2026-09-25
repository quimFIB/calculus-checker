"""http.server over api.handle (app/API.md). Binds 127.0.0.1 only.

Untrusted, and holds nothing: it decodes a request, calls api.handle, and
encodes the answer.
"""

import argparse
import json
import os
import sys
from http.server import BaseHTTPRequestHandler, HTTPServer
from urllib.parse import parse_qsl, urlsplit

import api

MAX_BODY = 1 << 20  # a move is a few hundred bytes
PAGE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "page",
                    "index.html")  # PAGE.md: the page
KATEX = os.path.join(os.path.dirname(PAGE), "katex")  # UI.md: vendored
TYPES = {".js": "text/javascript", ".css": "text/css", ".woff2": "font/woff2"}


def katex_file(path):
    """The vendored KaTeX file for /katex/<name> or /katex/fonts/<name>,
    or None: one fixed directory, names only, no traversal."""
    parts = path.split("/")[2:]
    if not 1 <= len(parts) <= 2 or (len(parts) == 2 and parts[0] != "fonts"):
        return None
    name = parts[-1]
    ext = os.path.splitext(name)[1]
    if ext not in TYPES or not name or name.startswith(".") or "\\" in name:
        return None
    full = os.path.join(KATEX, *parts)
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
        if url.path.startswith("/katex/"):
            found = katex_file(url.path)
            if found is None:
                return self._send(404, {"error": {
                    "code": "unknown-route",
                    "message": f"no file {url.path}"}})
            return self._file(*found)
        self._send(*api.handle("GET", url.path, dict(parse_qsl(url.query))))

    def do_POST(self):
        url = urlsplit(self.path)
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
        self._send(*api.handle("POST", url.path, body))

    def log_message(self, fmt, *args):
        if self.server.verbose:
            super().log_message(fmt, *args)


def serve(port=8765, verbose=False):
    """Serve until interrupted. One request at a time, on purpose: the
    kernel's module-level tables (handles, lineages, memo caches) were not
    written for concurrent steps, and there is one learner."""
    srv = HTTPServer(("127.0.0.1", port), Handler)
    srv.verbose = verbose
    print(f"calc: http://127.0.0.1:{srv.server_address[1]}/ (the check-mode "
          "page; PAGE.md)", flush=True)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        srv.server_close()


def main(argv=None):
    p = argparse.ArgumentParser(description="the calculus checker's API")
    p.add_argument("--port", type=int, default=8765)
    p.add_argument("-v", "--verbose", action="store_true")
    p.add_argument("--work", default="calc-work",
                   help="where work files are saved (PERSIST.md); "
                        "relative to the current directory")
    a = p.parse_args(argv)
    api.WORK_DIR = os.path.abspath(a.work)
    serve(a.port, a.verbose)


if __name__ == "__main__":
    sys.exit(main())
