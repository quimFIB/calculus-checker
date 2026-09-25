"""TIMEOUT.md Done-when 1: the worker, the timeout, cancel and restore."""

import json
import os
import tempfile
import threading
import time
import unittest

import backend
import work

SLOW_GOAL = "(x + y + z + w + 1)^24 == ?A @ x in [0, 1]"  # close 0.: ~9 s
QUICK_GOAL = "pi*sqrt 3/9 == ?A"
# a value whose ring normal form takes seconds, though it is the answer
SLOW_VALUE = ("close pi*sqrt 3/9 + (x + y + z + w + 1)^24 "
              "- (x + y + z + w + 1)^24.")


class Worker(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp()
        cls.w = backend.Worker(timeout=1.0, work_dir=cls.dir)

    @classmethod
    def tearDownClass(cls):
        cls.w.close()

    def call(self, method, path, args):
        status, body = self.w.handle(method, path, args)
        self.assertEqual(status, 200, body)
        return body

    def tac(self, sid, node, text):
        return self.call("POST", "/tactic", {"session": sid, "node": node,
                                             "text": text})

    def tree(self, sid):
        return self.call("GET", "/tree", {"session": sid})["nodes"]

    def test_a_slow_step_times_out_and_changes_nothing(self):
        s = self.call("POST", "/session", {"goal": QUICK_GOAL})
        sid = s["session"]
        f = self.tac(sid, "n0", "fact h := sqrt_sq_val with a := 3.")["node"]
        before = self.tree(sid)
        restarts = self.w.restarts
        t = time.monotonic()
        r = self.tac(sid, f, SLOW_VALUE)
        self.assertLess(time.monotonic() - t, 3.0)
        self.assertEqual(r["timeout"]["cancelled"], False)
        self.assertEqual(r["timeout"]["seconds"], 1.0)
        self.assertEqual(self.w.restarts, restarts + 1)
        self.assertEqual(self.tree(sid), before)
        # the fact bound before the timeout is still usable after it
        again = self.tac(sid, f, "close pi/(3*sqrt 3) by field using h.")
        self.assertNotIn("refusal", again)
        self.assertNotIn("timeout", again)

    def test_cancel_from_another_thread(self):
        w = backend.Worker(timeout=0, work_dir=None)
        try:
            sid = w.handle("POST", "/session", {"goal": SLOW_GOAL})[1][
                "session"]
            out = {}
            th = threading.Thread(target=lambda: out.update(
                r=w.handle("POST", "/tactic", {"session": sid, "node": "n0",
                                               "text": "close 0."})))
            th.start()
            time.sleep(0.5)
            self.assertEqual(w.cancel(), {"cancelled": True})
            th.join(5)
            self.assertFalse(th.is_alive())
            status, body = out["r"]
            self.assertTrue(body["timeout"]["cancelled"])
            self.assertEqual(w.cancel(), {"cancelled": False})
        finally:
            w.close()

    def test_restart_keeps_every_session_and_ownership(self):
        a = self.call("POST", "/session", {"problem": "stage0.S1"})["session"]
        b = self.call("POST", "/session", {"goal": "Int[x = 0 .. 1] 2*x "
                                           "== ?A"})["session"]
        self.tac(b, "n0", "ftc x^2.")
        a2 = self.call("POST", "/session", {"problem": "stage0.S1",
                                            "resume": True})["session"]
        n = self.tac(a2, "n0", "ftc x^3 + x^2 by ring.")["node"]
        self.call("POST", "/script", {"session": a2, "script": "ftc x^3 + "
                                      "x^2 by ring.", "path": ["n0", n]})
        p = work.path_of(self.dir, "stage0.S1")
        stamp = os.stat(p).st_mtime_ns
        trees = {s: self.tree(s) for s in (a, b, a2)}
        slow = self.call("POST", "/session", {"goal": SLOW_GOAL})["session"]
        self.assertIn("timeout", self.tac(slow, "n0", "close 0."))
        self.assertEqual({s: self.tree(s) for s in (a, b, a2)}, trees)
        self.assertEqual(os.stat(p).st_mtime_ns, stamp)  # restore wrote none
        # the newer S1 session still owns the file, the older is superseded
        self.assertEqual(self.call("POST", "/script", {
            "session": a2, "script": "x.", "path": ["n0"]}), {"saved": True})
        self.assertEqual(self.call("POST", "/script", {
            "session": a, "script": "", "path": ["n0"]}), {"saved": False})
        with open(p, encoding="utf-8") as f:
            self.assertEqual(json.load(f)["script"], "x.")

    def test_routes_answer_as_in_process(self):
        """S1's flow through the worker and in-process, compared."""
        import api
        flow = [("POST", "/tactic", {"node": "n0",
                                     "text": "ftc x^3 + x^2 by ring."}),
                ("POST", "/tactic", {"node": "n1", "text": "close 3."}),
                ("GET", "/palette", {"node": "n1"}),
                ("GET", "/hint", {"node": "n0", "rung": "2"}),
                ("POST", "/tactic", {"node": "n1", "text": "close 2."}),
                ("GET", "/node", {"node": "n2"})]

        def run(handle):
            s = handle("POST", "/session", {"problem": "stage0.S1"})[1]
            out = []
            for m, path, args in flow:
                args = dict(args, session=s["session"])
                if m == "GET":
                    args = {k: str(v) for k, v in args.items()}
                body = handle(m, path, args)[1]
                out.append(json.loads(json.dumps(body).replace(
                    s["session"], "SID")))
            return out
        saved, api.WORK_DIR = api.WORK_DIR, None
        try:
            here = run(api.handle)
        finally:
            api.WORK_DIR = saved
        w = backend.Worker(timeout=10, work_dir=None)
        try:
            there = run(w.handle)
        finally:
            w.close()
        self.assertEqual(there, here)

    def test_a_stray_print_cannot_corrupt_an_answer(self):
        w = backend.Worker(timeout=10, work_dir=None)
        try:
            w.proc.stdin.write(json.dumps({"method": "GET", "path": "/moves",
                                           "args": {}}) + "\n")
            w.proc.stdin.flush()
            got = w._wait(None, 10)
            self.assertEqual(got[0], "reply")
        finally:
            w.close()


if __name__ == "__main__":
    unittest.main()


class Crash(unittest.TestCase):
    def test_a_dead_worker_is_replaced_and_sessions_come_back(self):
        w = backend.Worker(timeout=5, work_dir=None)
        try:
            s = w.handle("POST", "/session", {"problem": "stage0.S1"})[1]
            n = w.handle("POST", "/tactic", {"session": s["session"],
                                             "node": "n0", "text":
                                             "ftc x^3 + x^2 by ring."})[1]
            w.proc.kill()
            w.proc.wait()
            status, body = w.handle("GET", "/node", {"session": s["session"],
                                                     "node": n["node"]})
            self.assertEqual((status, body["node"]), (200, "n1"))
            self.assertEqual(w.restarts, 1)
        finally:
            w.close()

    def test_a_session_that_cannot_come_back_is_unknown(self):
        w = backend.Worker(timeout=5, work_dir=None)
        try:
            s = w.handle("POST", "/session", {"problem": "stage0.S1"})[1]
            sid = s["session"]
            w.handle("POST", "/tactic", {"session": sid, "node": "n0",
                                         "text": "ftc x^3 + x^2 by ring."})
            w.docs[sid]["nodes"][0]["args"]["F"] = "x^4"  # will not replay
            w._restart()
            status, body = w.handle("GET", "/tree", {"session": sid})
            self.assertEqual((status, body["error"]["code"]),
                             (400, "unknown-session"))
        finally:
            w.close()
