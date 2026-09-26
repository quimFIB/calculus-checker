"""SCRIPT.md: the tactic syntax against every problem file, and /tactic."""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import api  # noqa: E402
import script  # noqa: E402
from session import K, loader  # noqa: E402


def _steps():
    """(problem id, proof name, step) for every step of every file."""
    for pid, (p, _, _) in api._problem_files().items():
        for name, steps in p.proofs.items():
            for s in steps:
                yield pid, name, s


class RoundTrip(unittest.TestCase):
    def test_every_step_round_trips(self):
        n = 0
        for pid, name, s in _steps():
            text = script.show(s["move"], s["args"])
            with self.subTest(pid=pid, proof=name, step=s["id"], text=text):
                self.assertEqual(script.parse(text), (s["move"], s["args"]))
            n += 1
        self.assertGreater(n, 40)

    def test_every_proof_replays_through_tactic(self):
        for pid, (p, _, _) in api._problem_files().items():
            for name, steps in p.proofs.items():
                with self.subTest(pid=pid, proof=name):
                    results, _ = loader.replay(p, name)
                    want = K.report(results[-1][1]) \
                        if not isinstance(results[-1][1], K.Refusal) else None
                    s, n = api.handle("POST", "/session", {"problem": pid})
                    for st in steps:
                        s, n = api.handle("POST", "/tactic", {
                            "session": n["session"], "node": n["node"],
                            "text": script.show(st["move"], st["args"])})
                        self.assertEqual(s, 200, n)
                        if "refusal" in n:
                            break
                    got = None if "refusal" in n else n["report"]
                    self.assertEqual(got, want)


class Syntax(unittest.TestCase):
    def test_defaults_and_comments(self):
        self.assertEqual(
            script.parse("(* the control *) ftc x^3 + x^2."),
            ("ftc", {"F": "x^3 + x^2", "check": "ring", "facts": []}))
        self.assertEqual(
            script.parse("close pi/4 by field using h1, h2"),
            ("close", {"value": "pi/4", "check": "field",
                       "facts": [["handle", "h1"], ["handle", "h2"]]}))

    def test_keywords_inside_brackets_stay_terms(self):
        m, a = script.parse("ftc f(to) + (x by y) by field.")
        self.assertEqual(a["F"], "f(to) + (x by y)")
        self.assertEqual(a["check"], "field")

    def test_ranges_do_not_end_a_sentence(self):
        m, a = script.parse("rewrite pyth with u := Int[t = 0 .. 1] t at "
                            "(sin(Int[t = 0 .. 1] t))^2 + (cos(Int[t = 0 .. "
                            "1] t))^2.")
        self.assertEqual(a["inst"], {"u": "Int[t = 0 .. 1] t"})

    def test_verify(self):
        """p1_expected E112: verify takes only by and using."""
        self.assertEqual(script.parse("verify by field using h, k"),
                         ("verify", {"check": "field",
                                     "facts": [["handle", "h"],
                                               ["handle", "k"]]}))
        self.assertEqual(script.parse("verify"),
                         ("verify", {"check": "ring", "facts": []}))
        self.assertEqual(script.show("verify", {"check": "field",
                                                 "facts": []}),
                         "verify by field.")
        with self.assertRaises(script.TacticError):
            script.parse("verify x^2")

    def test_bad_tactics(self):
        for text in ("", "prove it.", "ftc.", "ftc x by magic.",
                     "rewrite sin_pi.", "fact sqrt_sq_val.",
                     "int_subst x := t^2 as t from 0.",
                     "int_parts in t with u := t.", "int_flip now.",
                     "ftc x occurrence one.", "ftc x by ring by field.",
                     "close 1 using 2x."):
            with self.subTest(text=text), self.assertRaises(script.TacticError):
                script.parse(text)

    def test_route_refuses_bad_tactic_and_adds_nothing(self):
        s, n = api.handle("POST", "/session", {"problem": "stage0.S1"})
        s, r = api.handle("POST", "/tactic", {"session": n["session"],
                                              "node": "n0", "text": "ftc."})
        self.assertEqual((s, r["refusal"]["code"]), (200, "bad-tactic"))
        s, t = api.handle("GET", "/tree", {"session": n["session"]})
        self.assertEqual(len(t["nodes"]), 1)
        s, r = api.handle("POST", "/tactic", {"session": n["session"],
                                              "node": "n0",
                                              "text": "ftc x^3 + x^2 by ring."})
        s, r = api.handle("POST", "/tactic", {"session": n["session"],
                                              "node": r["node"],
                                              "text": "close 2."})
        self.assertEqual(r["report"], "Proved.")


if __name__ == "__main__":
    unittest.main()
