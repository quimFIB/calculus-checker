"""app/API.md's Done-when item 1: every route, every error and refusal code,
every problem file through the API against loader.replay, forking,
retraction, handle scoping, and plain-JSON responses.

Run: python3 -m unittest discover -s app
"""

import json
import os
import sys
import threading
import unittest
import urllib.error
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import api  # noqa: E402
import server  # noqa: E402
from session import K, loader  # noqa: E402
from terms import show  # noqa: E402

PLAIN = (str, int, float, bool, type(None))


def plain(x):
    """x is built from JSON types only, all the way down."""
    if isinstance(x, dict):
        return all(isinstance(k, str) and plain(v) for k, v in x.items())
    if isinstance(x, list):
        return all(plain(v) for v in x)
    return isinstance(x, PLAIN)


class Api(unittest.TestCase):
    def call(self, method, path, args=None, status=200):
        s, r = api.handle(method, path, {} if args is None else args)
        self.assertEqual(s, status, r)
        self.assertTrue(plain(r), r)
        json.dumps(r)  # and serialisable
        return r

    def refused(self, r, code):
        self.assertIn("refusal", r, r)
        self.assertEqual(r["refusal"]["code"], code, r)

    def error(self, r, code):
        self.assertEqual(r["error"]["code"], code, r)

    def s1(self):
        return self.call("POST", "/session", {"problem": "stage0.S1"})

    def step(self, n, move, args, **kw):
        return self.call("POST", "/step", {"session": n["session"],
                                           "node": n["node"], "move": move,
                                           "args": args}, **kw)


class Routes(Api):
    def test_problems_lists_every_file_without_proofs(self):
        r = self.call("GET", "/problems")
        ids = {p["id"] for p in r["problems"]}
        self.assertEqual(ids, set(api._problem_files()))
        self.assertIn("stage0.S1", ids)
        self.assertTrue(len(ids) >= 7)
        for p in r["problems"]:
            self.assertEqual(set(p), {"id", "title", "statement"})

    def test_session_from_problem(self):
        n = self.s1()
        self.assertEqual(n["node"], "n0")
        self.assertIsNone(n["parent"])
        self.assertEqual(n["move"], "install")
        self.assertEqual(n["goal"], "Int[x = 0 .. 1] 3*x^2 + 2*x == ?A")
        self.assertTrue(n["report"].startswith("Open: "))

    def test_session_from_goal_text_with_functions(self):
        n = self.call("POST", "/session", {"goal": "f(x) - f(x) == ?A",
                                           "functions": {"f": 1}})
        n = self.step(n, "close", {"value": "0", "check": "ring",
                                   "facts": []})
        self.assertEqual(n["report"], "Proved.")
        self.assertEqual(n["theorem"], "f(x) - f(x) == 0")
        self.assertIsNone(n["goal"])

    def test_install_refusal_makes_no_session(self):
        before = len(api.SESSIONS)
        r = self.call("POST", "/session", {"goal": "x > 0"})
        self.refused(r, "goal-shape")
        r = self.call("POST", "/session", {"goal": "sinx == ?A"})
        self.assertIn("refusal", r)
        self.assertEqual(len(api.SESSIONS), before)

    def test_proves_s1(self):
        n = self.s1()
        n1 = self.step(n, "ftc", {"F": "x^3 + x^2", "check": "ring",
                                  "facts": []})
        self.assertEqual(n1["parent"], "n0")
        self.assertTrue(all(o["new"] for o in n1["obligations"]
                            if o["key"] not in
                            {p["key"] for p in n["obligations"]}))
        n2 = self.step(n1, "close", {"value": "2", "check": "ring",
                                     "facts": []})
        self.assertEqual(n2["report"], "Proved.")
        self.assertEqual(n2["theorem"], "Int[x = 0 .. 1] 3*x^2 + 2*x == 2")

    def test_wrong_answer_carries_residual_and_adds_no_node(self):
        n = self.s1()
        n1 = self.step(n, "ftc", {"F": "x^3 + x^2", "check": "ring",
                                  "facts": []})
        r = self.step(n1, "close", {"value": "3", "check": "ring",
                                    "facts": []})
        self.assertIn("refusal", r)
        self.assertIsNotNone(r["refusal"]["residual"])
        t = self.call("GET", "/tree", {"session": n["session"]})
        self.assertEqual([x["node"] for x in t["nodes"]], ["n0", "n1"])

    def test_node_route(self):
        n = self.s1()
        self.assertEqual(self.call("GET", "/node", {"session": n["session"],
                                                    "node": "n0"}), n)

    def test_parse(self):
        r = self.call("POST", "/parse", {"text": "sin x^2"})
        self.assertEqual(r, {"term": "sin(x^2)", "katex": None})
        r = self.call("POST", "/parse", {"text": "Int[x = 0 .. 1] x == ?A"})
        self.assertEqual(r["term"], "Int[x = 0 .. 1] x == ?A")
        self.refused(self.call("POST", "/parse", {"text": "e"}),
                     "D3-bare-e")
        r = self.call("POST", "/parse", {"text": "g(x)", "functions":
                                         {"g": 1}})
        self.assertEqual(r["term"], "g(x)")
        self.assertIn("refusal", self.call("POST", "/parse",
                                           {"text": "g(x)"}))

    def test_hint_and_palette_not_built(self):
        n = self.s1()
        q = {"session": n["session"], "node": "n0", "rung": "1"}
        self.refused(self.call("GET", "/hint", q), "not-built")
        self.refused(self.call("GET", "/palette", q), "not-built")


class Errors(Api):
    def test_codes(self):
        n = self.s1()
        self.error(self.call("GET", "/nope", status=404), "unknown-route")
        self.error(self.call("GET", "/step", status=404), "unknown-route")
        self.error(self.call("POST", "/session", {"problem": "zzz"},
                             status=400), "unknown-problem")
        self.error(self.call("POST", "/step", {"session": "zzz"},
                             status=400), "unknown-session")
        self.error(self.call("POST", "/step", {"session": n["session"],
                                               "node": "n99"}, status=400),
                   "unknown-node")
        self.error(self.call("POST", "/step", {"session": n["session"],
                                               "node": "n0", "move": "ftc"},
                             status=400), "bad-request")
        self.error(self.call("POST", "/step", {"session": n["session"],
                                               "node": 0, "move": "ftc",
                                               "args": {}}, status=400),
                   "bad-request")
        self.error(self.call("POST", "/session", {"goal": "x == ?A",
                                                  "functions": {"f": 0}},
                             status=400), "bad-request")
        s, r = api.handle("POST", "/step", ["not", "an", "object"])
        self.assertEqual(s, 400)

    def test_step_refusals(self):
        n = self.s1()
        self.refused(self.step(n, "auto", {}), "bad-move")
        self.refused(self.step(n, "ftc", {"F": 3, "check": "ring",
                                          "facts": []}), "bad-args")
        self.refused(self.step(n, "ftc", {"F": "x^3", "check": "ring",
                                          "facts": [["handle", "h"]]}),
                     "unknown-handle")
        self.refused(self.step(n, "ftc", {"F": "x^3", "check": "ring",
                                          "facts": ["h"]}), "bad-args")
        r = self.step(n, "ftc", {"F": "sinx", "check": "ring", "facts": []})
        self.assertIn("refusal", r)  # the parser's own code
        self.refused(self.step(n, "ftc", {"F": "x^3", "check": "ring"}),
                     "bad-args")

    def test_kernel_exception_is_500_and_changes_nothing(self):
        n = self.s1()
        real = K.step

        def boom(*a):
            raise RuntimeError("planted")
        K.step = boom
        try:
            r = self.step(n, "ftc", {"F": "x^3 + x^2", "check": "ring",
                                     "facts": []}, status=500)
        finally:
            K.step = real
        self.error(r, "kernel-error")
        t = self.call("GET", "/tree", {"session": n["session"]})
        self.assertEqual(len(t["nodes"]), 1)


class Tree(Api):
    def test_fork_retract_and_keep(self):
        n = self.s1()
        a = self.step(n, "ftc", {"F": "x^3 + x^2", "check": "ring",
                                 "facts": []})
        b = self.step(n, "ftc", {"F": "x^3 + x^2 + 1", "check": "ring",
                                 "facts": []})  # a fork from n0
        self.assertEqual((a["node"], b["node"]), ("n1", "n2"))
        a2 = self.step(a, "close", {"value": "2", "check": "ring",
                                    "facts": []})
        back = self.call("POST", "/retract", {"session": n["session"],
                                              "node": a["node"]})
        self.assertEqual(back["node"], "n0")
        t = {x["node"]: x for x in
             self.call("GET", "/tree", {"session": n["session"]})["nodes"]}
        self.assertEqual(set(t), {"n0", "n1", "n2", "n3"})
        self.assertTrue(t["n1"]["retracted"] and t["n3"]["retracted"])
        self.assertFalse(t["n0"]["retracted"] or t["n2"]["retracted"])
        self.assertEqual(t[a2["node"]]["report"], "Proved.")
        self.assertEqual(t["n1"]["summary"], "ftc F := x^3 + x^2")
        # stepping from a retracted node is allowed; only the new node is live
        c = self.step(a, "close", {"value": "2", "check": "ring",
                                   "facts": []})
        self.assertFalse(c["retracted"])
        self.refused(self.call("POST", "/retract", {"session": n["session"],
                                                    "node": "n0"}),
                     "retract-root")

    def test_proof_finished(self):
        n = self.s1()
        n1 = self.step(n, "ftc", {"F": "x^3 + x^2", "check": "ring",
                                  "facts": []})
        n2 = self.step(n1, "close", {"value": "2", "check": "ring",
                                     "facts": []})
        self.refused(self.step(n2, "int_flip", {}), "proof-finished")


def _files():
    return {p.id: p for p, _, _ in api._problem_files().values()}


class ProblemFiles(Api):
    """Every proof in every problem file, through the API, against
    loader.replay: same report, goal and obligation keys and statuses at
    every step."""

    def test_every_proof_matches_the_loader(self):
        self.assertEqual(sum(len(p.proofs) for p in _files().values()), 8)
        for pid, p in _files().items():
            for name, steps in p.proofs.items():
                with self.subTest(problem=pid, proof=name):
                    self._one(pid, p, name, steps)

    def _one(self, pid, p, name, steps):
        results, _ = loader.replay(p, name)
        n = self.call("POST", "/session", {"problem": pid})
        self._same(n, results[0][1])
        for s, (sid, want) in zip(steps, results[1:]):
            self.assertEqual(s["id"], sid)
            r = self.step(n, s["move"], s["args"])
            if isinstance(want, K.Refusal):
                self.refused(r, want.code)
                return
            self._same(r, want)
            n = r
        self.assertEqual(n["report"], K.report(results[-1][1]))

    def _same(self, n, st):
        self.assertEqual(n["report"], K.report(st))
        self.assertEqual(n["goal"],
                         None if st.goal is None else show(st.goal))
        self.assertEqual([(o["key"], o["status"]) for o in n["obligations"]],
                         [(show(o.key), o.status) for o in st.obligations()])

    def test_fact_handles_are_path_scoped(self):
        # find a proof with a fact step, and check its bind is visible
        # below the fact and not on a sibling branch
        for pid, p in _files().items():
            for steps in p.proofs.values():
                k = next((i for i, s in enumerate(steps)
                          if s["move"] == "fact"), None)
                if k is None:
                    continue
                n = self.call("POST", "/session", {"problem": pid})
                root = n
                for s in steps[:k + 1]:
                    n = self.step(n, s["move"], s["args"])
                bind = steps[k]["args"]["bind"]
                self.assertIn(bind, n["handles"])
                self.assertNotIn(bind, root["handles"])
                later = next((s for s in steps[k + 1:]
                              if ["handle", bind] in s["args"].get("facts",
                                                                  [])), None)
                if later is None:
                    continue
                self.refused(self.step(root, later["move"], later["args"]),
                             "unknown-handle")
                return
        self.fail("no problem file uses a fact handle")


class Http(unittest.TestCase):
    """The server end to end: Done-when item 3's S1 proof, over HTTP."""

    @classmethod
    def setUpClass(cls):
        cls.srv = server.HTTPServer(("127.0.0.1", 0), server.Handler)
        cls.srv.verbose = False
        cls.base = f"http://127.0.0.1:{cls.srv.server_address[1]}"
        cls.t = threading.Thread(target=cls.srv.serve_forever, daemon=True)
        cls.t.start()

    @classmethod
    def tearDownClass(cls):
        cls.srv.shutdown()
        cls.srv.server_close()

    def req(self, method, path, body=None, raw=None):
        data = raw if raw is not None else (
            None if body is None else json.dumps(body).encode())
        rq = urllib.request.Request(self.base + path, data=data,
                                    method=method)
        try:
            with urllib.request.urlopen(rq) as r:
                return r.status, json.load(r)
        except urllib.error.HTTPError as e:
            return e.code, json.load(e)

    def test_s1_over_http(self):
        s, n = self.req("POST", "/session", {"problem": "stage0.S1"})
        self.assertEqual(s, 200)
        sid = n["session"]
        s, n = self.req("POST", "/step", {"session": sid, "node": "n0",
                                          "move": "ftc", "args": {
                                              "F": "x^3 + x^2",
                                              "check": "ring", "facts": []}})
        s, n = self.req("POST", "/step", {"session": sid, "node": n["node"],
                                          "move": "close", "args": {
                                              "value": "2", "check": "ring",
                                              "facts": []}})
        self.assertEqual((s, n["report"]), (200, "Proved."))
        s, t = self.req("GET", f"/tree?session={sid}")
        self.assertEqual(len(t["nodes"]), 3)

    def test_bad_json(self):
        s, r = self.req("POST", "/step", raw=b"{nope")
        self.assertEqual((s, r["error"]["code"]), (400, "bad-json"))


if __name__ == "__main__":
    unittest.main()
