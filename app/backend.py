"""Where API requests run (app/TIMEOUT.md).

`Backend` calls api.handle in this process, as the tests do. `Worker` runs
it in a child process (worker.py) so that a step that runs too long, or
that the learner cancels, can be stopped: the child is killed, a new one
started, and every session rebuilt from its latest work document, which
is moves, never verdicts (PERSIST.md). Untrusted, like all of app/.
"""

import json
import os
import queue
import subprocess
import sys
import threading

import api

WORKER = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                      "worker.py")


class Backend:
    """In-process: api.handle, no timeout, nothing to cancel."""

    def handle(self, method, path, args):
        return api.handle(method, path, args)

    def cancel(self):
        return {"cancelled": False}

    def close(self):
        pass


class Worker:
    def __init__(self, timeout=10.0, work_dir=None):
        self.timeout = timeout or None  # 0 turns it off
        self.work_dir = work_dir
        self.lock = threading.Lock()  # one request at a time, as before
        self.docs = {}  # session id -> latest document
        self.saved = {}  # session id -> its last save outcome
        self.owner = {}  # api.OWNER as the worker last reported it
        self.live = set()  # sessions the current child holds
        self.rid = 0  # the request running, when self.busy
        self.busy = False
        self.restarts = 0
        self._start()

    # ------------------------------------------------ the child

    def _start(self):
        self._sweep()
        self.live = set()
        cmd = [sys.executable, WORKER]
        if self.work_dir:
            cmd += ["--work", self.work_dir]
        self.proc = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, text=True,
                                     encoding="utf-8", bufsize=1)
        self.q = queue.Queue()
        threading.Thread(target=self._read, args=(self.proc, self.q),
                         daemon=True).start()

    def _sweep(self):
        """Remove temporary files a killed child left in the work
        directory (work.write's, before its os.replace)."""
        if not self.work_dir or not os.path.isdir(self.work_dir):
            return
        for name in os.listdir(self.work_dir):
            if name.startswith(".") and name.endswith(".tmp"):
                try:
                    os.unlink(os.path.join(self.work_dir, name))
                except OSError:
                    pass

    @staticmethod
    def _read(proc, q):
        for line in proc.stdout:
            q.put(("reply", line))
        q.put(("dead", None))

    def _send(self, obj):
        self.proc.stdin.write(json.dumps(obj) + "\n")
        self.proc.stdin.flush()

    def _wait(self, rid, timeout):
        """The child's answer to request rid: ("reply", dict), ("dead",),
        ("cancel",) or ("timeout",)."""
        while True:
            try:
                kind, v = self.q.get(timeout=timeout)
            except queue.Empty:
                return ("timeout",)
            if kind == "reply":
                return ("reply", json.loads(v))
            if kind == "dead":
                return ("dead",)
            if kind == "cancel" and v == rid:
                return ("cancel",)
            # a cancel aimed at an earlier request that already finished

    def _restart(self):
        """Kill the child and start another. Sessions come back lazily, each
        on the first request that names it (_restore)."""
        try:
            self.proc.kill()
            self.proc.wait(timeout=5)
        except Exception:
            pass
        self.restarts += 1
        self._start()

    def _restore(self, sid, rid):
        """Rebuild session sid in the child, under the request's timeout.
        None when it is there (or cannot come back: it is then dropped, its
        requests answer unknown-session, and its work file is untouched);
        else the outcome that stopped it, "cancel", "timeout" or "dead"."""
        self._send({"restore": {"sessions": {sid: self.docs[sid]},
                                "owner": self.owner,
                                "saved": {sid: self.saved.get(sid)}}})
        got = self._wait(rid, self.timeout)
        if got[0] == "reply":
            if sid in got[1].get("restored", ()):
                self.live.add(sid)
            else:
                self.docs.pop(sid, None)
            return None
        if got[0] == "timeout":  # it would run out of time again
            self.docs.pop(sid, None)
        return got[0]

    # ------------------------------------------------ the API

    def handle(self, method, path, args):
        with self.lock:
            self.rid += 1
            rid, self.busy = self.rid, True
            try:
                try:
                    if self.proc.poll() is not None:  # it died between
                        self._restart()               # requests: start over
                    sid = args.get("session") if isinstance(args, dict) \
                        else None
                    stop = None
                    if sid in self.docs and sid not in self.live:
                        stop = self._restore(sid, rid)
                    if stop is None:
                        self._send({"method": method, "path": path,
                                    "args": args})
                        got = self._wait(rid, self.timeout)
                    else:
                        got = (stop,)
                except (OSError, ValueError):
                    got = ("dead",)
                if got[0] == "reply":
                    a = got[1]
                    for s, doc in a.get("docs", {}).items():
                        self.docs[s] = doc
                        self.live.add(s)
                    self.saved.update(a.get("saved", {}))
                    self.owner = a.get("owner", self.owner)
                    return a["status"], a["body"]
                self._restart()
                message = {
                    "timeout": "the step ran out of time; nothing changed",
                    "cancel": "cancelled; nothing changed",
                    "dead": "the worker stopped; nothing changed"}[got[0]]
                return 200, {"timeout": {
                    "seconds": self.timeout if got[0] == "timeout" else None,
                    "cancelled": got[0] == "cancel", "message": message}}
            finally:
                self.busy = False

    def cancel(self):
        """Stop the running request, if any. Does not take the lock."""
        if not self.busy:
            return {"cancelled": False}
        self.q.put(("cancel", self.rid))
        return {"cancelled": True}

    def close(self):
        try:
            self.proc.kill()
        except Exception:
            pass
