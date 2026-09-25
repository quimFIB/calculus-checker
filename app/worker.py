"""The worker process (app/TIMEOUT.md): the API and the kernel, one request
per JSON line on stdin, one answer per line on stdout.

Untrusted, and a transport only: it calls api.handle and api.restore. The
protocol owns the real stdout; anything else that prints (the kernel, a
library) goes to stderr, so it cannot corrupt an answer. The server kills
this process to stop a step that runs too long; it holds nothing the
server cannot rebuild from the work documents it returns.
"""

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import api  # noqa: E402

# routes that can change a session, after which its document is returned
CHANGES = {("POST", "/session"), ("POST", "/import"), ("POST", "/step"),
           ("POST", "/tactic"), ("POST", "/retract"), ("POST", "/script"),
           ("GET", "/hint")}


def answer(req):
    if "restore" in req:
        r = req["restore"]
        done, failed = api.restore(r["sessions"], r.get("owner"),
                                   r.get("saved"))
        return {"restored": done, "failed": failed}
    method, path, args = req["method"], req["path"], req["args"]
    status, body = api.handle(method, path, args)
    docs, saved = {}, {}
    if (method, path) in CHANGES:  # a refusal too: /hint saves first
        sid = (body.get("session") if isinstance(body, dict) else None) \
            or (args.get("session") if isinstance(args, dict) else None)
        if isinstance(sid, str) and sid in api.SESSIONS:
            try:
                docs[sid] = api.work.document(api.SESSIONS[sid])
                saved[sid] = getattr(api.SESSIONS[sid], "saved", None)
            except Exception:  # never fail the request over the copy
                pass
    return {"status": status, "body": body, "docs": docs, "saved": saved,
            "owner": dict(api.OWNER)}


def main(argv=None):
    p = argparse.ArgumentParser(description="the calculus checker's worker")
    p.add_argument("--work", default=None)
    a = p.parse_args(argv)
    api.WORK_DIR = a.work
    # the protocol keeps its own copy of stdout; fd 1 and sys.stdout then
    # point at stderr, so a stray print, from Python or C, cannot reach it
    out = os.fdopen(os.dup(1), "w", encoding="utf-8")
    os.dup2(2, 1)
    sys.stdout = sys.stderr
    for line in sys.stdin:
        if not line.strip():
            continue
        try:
            reply = answer(json.loads(line))
        except Exception as e:  # a bad line: answer it, keep serving
            reply = {"status": 500, "body": {"error": {
                "code": "worker-error", "message": f"{type(e).__name__}: {e}"}},
                "docs": {}}
        out.write(json.dumps(reply) + "\n")
        out.flush()


if __name__ == "__main__":
    main()
