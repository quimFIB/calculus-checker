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
import script  # noqa: E402
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
    def test_moves_lists_every_kernel_move_typed(self):
        r = self.call("GET", "/moves")
        self.assertEqual([m["name"] for m in r["moves"]], list(K.MOVES))
        for m in r["moves"]:
            required = [a["name"] for a in m["args"] if not a["optional"]]
            self.assertEqual(required, list(K._ARGS[m["name"]]), m)
            for a in m["args"]:
                self.assertEqual(a["type"],
                                 loader.ARG_TYPES[a["name"]].__name__)
                self.assertEqual(a["term"], a["name"] in loader.TERM_ARGS)

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
        r = self.call("POST", "/session", {"goal": "x # 0"})
        self.refused(r, "goal-shape")  # an order goal installs (E96)
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
        st = r["refusal"]["stuck"]  # STUCK.md: 2 - 3 is off by -1
        self.assertEqual((st["kind"], st["headline"]),
                         ("algebra", "The goal's side − your value = -1"))
        self.assertIsNone(st["suggest"])
        self.assertIsNone(n1["stuck"])
        t = self.call("GET", "/tree", {"session": n["session"]})
        self.assertEqual([x["node"] for x in t["nodes"]], ["n0", "n1"])

    def test_node_route(self):
        n = self.s1()
        for k in ("resumed", "problem", "key", "functions"):  # /session's own
            n.pop(k)
        self.assertEqual(self.call("GET", "/node", {"session": n["session"],
                                                    "node": "n0"}), n)

    def test_drop_forgets_the_session(self):
        n = self.s1()
        body = {"session": n["session"]}
        self.assertEqual(self.call("POST", "/drop", body), {"dropped": True})
        self.assertEqual(self.call("POST", "/drop", body), {"dropped": False})
        self.error(self.call("GET", "/node", dict(body, node="n0"),
                             status=400), "unknown-session")

    def test_parse(self):
        r = self.call("POST", "/parse", {"text": "sin x^2"})
        self.assertEqual(r, {"term": "sin(x^2)",
                             "katex": r"\sin\left(x^{2}\right)"})
        r = self.call("POST", "/parse", {"text": "Int[x = 0 .. 1] x == ?A"})
        self.assertEqual(r["term"], "Int[x = 0 .. 1] x == ?A")
        self.refused(self.call("POST", "/parse", {"text": "e"}),
                     "D3-bare-e")
        r = self.call("POST", "/parse", {"text": "g(x)", "functions":
                                         {"g": 1}})
        self.assertEqual(r["term"], "g(x)")
        self.assertIn("refusal", self.call("POST", "/parse",
                                           {"text": "g(x)"}))

    def test_palette(self):
        n = self.s1()
        pl = self.call("GET", "/palette", {"session": n["session"],
                                           "node": "n0"})
        self.assertIn("ftc", [m["move"] for m in pl["moves"]])
        self.assertEqual([c["id"] for c in pl["card"] if c["matches"]],
                         ["power"])
        n = self.call("POST", "/session", {"problem": "improper.P5"})
        pl = self.call("GET", "/palette", {"session": n["session"],
                                           "node": "n0"})
        moves = [m["move"] for m in pl["moves"]]
        self.assertIn("int_improper", moves)
        self.assertNotIn("ftc", moves)

    def test_progress_probe_tex_on_nodes(self):
        n = self.call("POST", "/session", {"problem": "parts.P1_PARTS"})
        self.assertIsNone(n["progress"])
        self.assertIsNone(n["probe"])
        self.assertTrue(n["goal_tex"].startswith(r"\int_{0}"))
        self.assertEqual((n["admissions"], n["steps"]), (0, 0))
        m = self.call("POST", "/tactic", {
            "session": n["session"], "node": "n0",
            "text": "int_subst x := t^2 as t from 0 to pi/2."})
        self.assertEqual(m["progress"]["signal"], "rule now matches")
        self.assertIn("sqrt_sq", m["progress"]["detail"])
        self.assertTrue(m["probe"]["agree"])
        self.assertEqual(m["probe"]["digits"], 12)
        self.assertEqual(m["steps"], 1)

    def test_max_rung(self):
        n = self.s1()
        q = {"session": n["session"]}
        self.assertEqual(self.call("GET", "/tree", q)["max_rung"], 0)
        self.call("GET", "/hint", {**q, "node": "n0", "rung": "2"})
        self.call("GET", "/hint", {**q, "node": "n0", "rung": "1"})
        self.assertEqual(self.call("GET", "/tree", q)["max_rung"], 2)

    def test_hint_rungs(self):
        n = self.call("POST", "/session", {"problem": "parts.P1_PARTS"})
        q = {"session": n["session"], "node": "n0"}
        got = [self.call("GET", "/hint", {**q, "rung": r}) for r in "123"]
        self.assertEqual([g["rung"] for g in got], [1, 2, 3])
        self.assertEqual({g["row"] for g in got}, {"root substitution"})
        self.assertEqual({g["integral"] for g in got},
                         {"Int[x = 0 .. pi^2/4] sin(sqrt x)"})
        self.assertEqual(got[0]["text"], "A substitution.")
        self.assertEqual(got[2]["text"], "Put x = t² inside sin(…).")
        self.assertEqual(got[1]["cost"], "u ≥ 0")

    def test_hint_refusals(self):
        n = self.s1()
        q = {"session": n["session"], "node": "n0"}
        self.refused(self.call("GET", "/hint", {**q, "rung": "4"}),
                     "not-built")
        self.error(self.call("GET", "/hint", {**q, "rung": "5"}, status=400),
                   "bad-request")
        n = self.call("POST", "/session", {"goal": "sin(2) == ?A"})
        self.refused(self.call("GET", "/hint", {"session": n["session"],
                                                "node": "n0", "rung": "1"}),
                     "no-integral")
        n = self.call("POST", "/session",
                      {"goal": "Int[x = 0 .. 1] abs(x) == ?A"})
        self.refused(self.call("GET", "/hint", {"session": n["session"],
                                                "node": "n0", "rung": "2"}),
                     "no-row")


class Pretty(Api):
    """PRETTY.md: /layout, /untex, /templates."""

    def test_layout_covers_the_script(self):
        text = ("(* S1 *)\nftc x^3 + x^2 by ring.\n\nclose 2.\n"
                "  rewrite sin_pi at sin(")
        r = self.call("POST", "/layout", {"text": text})
        kinds = [p["kind"] for p in r["pieces"]]
        self.assertEqual(kinds, ["gap", "sentence", "gap", "sentence", "gap",
                                 "open"])
        self.assertEqual("".join(g.get("text", g.get("term", ""))
                                 for p in r["pieces"] for g in p["segments"]
                                 if "choice" not in g and "name" not in g)
                         .replace(" by .", " by ring."), text)
        at = 0
        for p in r["pieces"]:
            self.assertEqual(p["start"], at)
            at = p["end"]
        self.assertEqual(at, len(text))
        ftc = r["pieces"][1]["segments"]
        self.assertEqual(ftc[1], {"term": "x^3 + x^2",
                                  "tex": "x^{3} + x^{2}"})

    def test_layout_holes_and_unparsable_terms(self):
        r = self.call("POST", "/layout", {"text": "ftc _. close 2x."})
        self.assertEqual(r["pieces"][0]["segments"][1]["tex"], "")
        self.assertIsNone(r["pieces"][2]["segments"][1]["tex"])

    def test_layout_uses_the_functions(self):
        r = self.call("POST", "/layout", {"text": "close f(1).",
                                          "functions": {"f": 1}})
        self.assertIn("operatorname", r["pieces"][0]["segments"][1]["tex"])

    def test_untex(self):
        r = self.call("POST", "/untex", {"latex": r"\frac{1}{1+x^2}"})
        self.assertEqual(r, {"term": "1/(1 + x^2)",
                             "tex": r"\frac{1}{1 + x^{2}}"})
        self.refused(self.call("POST", "/untex", {"latex": "ab"}), "bad-tex")
        self.refused(self.call("POST", "/untex", {"latex": "e"}),
                     "D3-bare-e")
        self.error(self.call("POST", "/untex", {}, status=400), "bad-request")

    def test_templates(self):
        r = self.call("GET", "/templates")
        self.assertEqual([t["move"] for t in r["templates"]],
                         list(script.FORMS))


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
        self.assertEqual(sum(len(p.proofs) for p in _files().values()), 14)  # + P3 part 1
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

    def test_page_at_root(self):
        with urllib.request.urlopen(self.base + "/") as r:
            self.assertEqual(r.status, 200)
            self.assertTrue(r.headers["Content-Type"].startswith("text/html"))
            self.assertIn(b"<title>Calculus checker</title>", r.read())

    def test_mathlive_is_served_and_nothing_else(self):
        """PRETTY.md Done-when 2: the vendored MathLive, one directory."""
        with urllib.request.urlopen(self.base + "/mathlive/mathlive.min.js") as r:
            self.assertEqual(r.headers["Content-Type"], "text/javascript")
        with urllib.request.urlopen(
                self.base + "/mathlive/fonts/KaTeX_Main-Regular.woff2") as r:
            self.assertEqual(r.headers["Content-Type"], "font/woff2")
        for bad in ("/mathlive/../server.py", "/mathlive/SOURCE",
                    "/mathlive/x/y/z.js", "/mathlive/LICENSE.txt"):
            with self.assertRaises(urllib.error.HTTPError, msg=bad):
                urllib.request.urlopen(self.base + bad)

    def test_parse_only_routes_skip_the_backend(self):
        """PRETTY.md review 4: /layout, /untex and /templates never reach
        the step backend, so they cannot queue behind a step."""
        calls = []

        class Spy:
            def handle(self, *a):
                calls.append(a)
                return 200, {}
        saved, server.BACKEND = server.BACKEND, Spy()
        try:
            s, r = self.req("POST", "/untex", {"latex": "\\frac{1}{2}"})
            self.assertEqual((s, r["term"]), (200, "1/2"))
            s, r = self.req("POST", "/layout", {"text": "close 2."})
            self.assertEqual(s, 200)
            s, r = self.req("GET", "/templates")
            self.assertEqual(len(r["templates"]), 10)
        finally:
            server.BACKEND = saved
        self.assertEqual(calls, [])

    def test_bad_json(self):
        s, r = self.req("POST", "/step", raw=b"{nope")
        self.assertEqual((s, r["error"]["code"]), (400, "bad-json"))


if __name__ == "__main__":
    unittest.main()
