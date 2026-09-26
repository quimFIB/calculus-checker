"""The API over stdin and stdout, one JSON object per line (app/DX.md).

Untrusted, and a transport only, like server.py: requests go to TIMEOUT.md's
worker, so a slow step can be stopped, and nothing is saved (the .dx buffer
is the learner's work). A reader thread takes stdin: /cancel is answered at
once, every other request in order by one runner thread.
"""

import json
import os
import queue
import sys
import threading

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import api  # noqa: E402
import backend  # noqa: E402

PROTOCOL = 1
# parse-only routes, answered here and never queued behind a step
# (PRETTY.md review 4, DX.md review 5)
LOCAL = {("POST", "/layout"), ("POST", "/untex"), ("POST", "/parse"),
         ("GET", "/templates")}


class Repl:
    def __init__(self, out, step_timeout=10.0):
        self.out = out
        self.lock = threading.Lock()
        self.backend = backend.Worker(step_timeout, None)
        self.jobs = queue.Queue()
        self.running = None  # the id of the request the backend has

    def write(self, obj):
        with self.lock:
            self.out.write(json.dumps(obj) + "\n")
            self.out.flush()

    def run(self, lines):
        runner = threading.Thread(target=self._runner, daemon=True)
        runner.start()
        self.write({"ready": True, "protocol": PROTOCOL})
        for line in lines:
            if not line.strip():
                continue
            try:
                req = json.loads(line)
                if not isinstance(req, dict):
                    raise ValueError("a request is a JSON object")
            except ValueError as e:
                self.write({"id": None, "status": 400, "body": {"error": {
                    "code": "bad-json", "message": str(e)}}})
                continue
            if req.get("path") == "/cancel":
                self.write({"id": req.get("id"), "status": 200,
                            "body": self.cancel(req.get("body") or {})})
                continue
            self.jobs.put(req)
        self.jobs.put(None)
        runner.join()
        self.backend.close()

    def cancel(self, body):
        """Stop the running request; with {"id": N}, only request N."""
        target = body.get("id") if isinstance(body, dict) else None
        if target is not None and target != self.running:
            return {"cancelled": False}
        return self.backend.cancel()

    def _runner(self):
        while True:
            req = self.jobs.get()
            if req is None:
                return
            rid = req.get("id")
            method = req.get("method", "POST")
            path = req.get("path")
            body = req.get("body")
            body = {} if body is None else body
            if not isinstance(path, str) or method not in ("GET", "POST"):
                self.write({"id": rid, "status": 400, "body": {"error": {
                    "code": "bad-request",
                    "message": "a request has method GET or POST and a path"}}})
                continue
            if (method, path) in LOCAL:
                status, answer = api.handle(method, path, body)
            else:
                self.running = rid
                try:
                    status, answer = self.backend.handle(method, path, body)
                finally:
                    self.running = None
            self.write({"id": rid, "status": status, "body": answer})


def main(step_timeout=10.0):
    api.WORK_DIR = None  # DX.md: the buffer is the work; nothing is saved
    # the protocol keeps its own copy of stdout; stray prints go to stderr
    out = os.fdopen(os.dup(1), "w", encoding="utf-8")
    os.dup2(2, 1)
    sys.stdout = sys.stderr
    sys.stdin.reconfigure(encoding="utf-8")
    Repl(out, step_timeout).run(sys.stdin)


if __name__ == "__main__":
    main()
