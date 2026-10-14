"""Complex arithmetic in the app (p1_expected E174, COMPLEX.md stage K1):
declarations, simpl and auto-simpl over C, parts by hand, the TeX forms
and a complex session saved and replayed."""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import api  # noqa: E402
import dx  # noqa: E402
import tex  # noqa: E402
import untex  # noqa: E402
import work  # noqa: E402
from terms import parse_term  # noqa: E402


def run(header, sentences, **extra):
    s, n = api.handle("POST", "/session", {"header": header, **extra})
    assert s == 200, n
    if "refusal" in n:
        return n
    node, r = "n0", n
    for text in sentences:
        s, r = api.handle("POST", "/tactic", {"session": n["session"],
                                              "node": node, "text": text})
        assert s == 200, r
        if "refusal" in r:
            return r
        node = r["node"]
    return r


class Declarations(unittest.TestCase):
    def test_a_header_declares_complex_variables(self):
        h = dx.header("goal z*conj z == ?A complex z, w functions f/1.")
        self.assertEqual(h["functions"], {"f": 1, "z": "complex",
                                          "w": "complex"})
        self.assertEqual(dx.show_header(h),
                         "goal z*conj z == ?A complex z, w functions f/1.")

    def test_a_complex_variable_is_complex_everywhere_after(self):
        r = run("goal z*conj z == ?A complex z.",
                ["close (re z)^2 + (im z)^2."], auto_simpl=False)
        self.assertEqual(r["report"], "Proved.")

    def test_an_order_on_a_complex_term_is_refused(self):
        r = run("goal z < 1 complex z.", [])
        self.assertEqual(r["refusal"]["code"], "sort-order-on-complex")

    def test_the_api_takes_a_complex_list(self):
        s, n = api.handle("POST", "/session", {"goal": "conj(w) == ?A",
                                               "complex": ["w"]})
        self.assertEqual(n["functions"], {"w": "complex"})


class Simpl(unittest.TestCase):
    """E174: simpl computes a complex value as its two parts, and
    auto-simpl names `parts` where E27 (c) does."""

    CASES = [
        ("(1 + i)^8 == ?A", "Proved.", "close 16 by ring."),
        ("exp(i*pi) == ?A", "Proved.", "close -1 by ring."),
        ("Log(-1) == ?A", "Proved.", "close pi*i by ring."),
        ("(2 + i)*(1 - 3*i) == ?A", "Proved.", "close 5 - 5*i by ring."),
        ("abs(3 + 4*i) == ?A", "Proved.", "close 5 by ring."),
        ("Log(i) == ?A", "Proved.", "close (1/2)*pi*i by ring."),
    ]

    def test_one_simpl_closes_each(self):
        for goal, report, last in self.CASES:
            with self.subTest(goal=goal):
                r = run(f"goal {goal}.", ["simpl."])
                self.assertEqual(r["report"], report, r)
                self.assertEqual(r["auto"][-1], last)
                self.assertEqual(r["admissions"], 0)

    def test_by_hand_parts_and_the_entries(self):
        r = run("goal Log(-1) == ?A.",
                ["rewrite parts at Log(-1).", "rewrite ln_one at ln 1.",
                 "rewrite arg_neg with u := -1 at Arg(-1).",
                 "close i*pi."], auto_simpl=False)
        self.assertEqual(r["report"], "Proved.")

    def test_e27_names_parts(self):
        r = run("goal (1 + i)^8 == ?A.", ["close (1 + i)^8."],
                auto_simpl=False)
        self.assertEqual(r["refusal"]["code"], "close-not-evaluated")
        self.assertIn("(parts)", r["refusal"]["message"])

    def test_by_hand_simpl_does_the_arithmetic_only(self):
        r = run("goal (2 + i)*(1 - 3*i) == ?A.", ["simpl."],
                auto_simpl=False)
        self.assertEqual(r["report"], "Proved.")
        r = run("goal exp(i*pi) == ?A.", ["simpl."], auto_simpl=False)
        self.assertEqual(r["refusal"]["code"], "close-not-evaluated")

    def test_a_false_value_is_refused(self):
        r = run("goal (1 + i)^8 == ?A.", ["close 17."], auto_simpl=False)
        self.assertEqual(r["refusal"]["code"], "close-check-failed")


class RealVariable(unittest.TestCase):
    """K2 (E176-E181): integrals of complex-valued functions of a real
    variable, closed by auto-simpl."""

    def test_integrals(self):
        import p1_expected as X
        for goal, move, value in X.K2_CASES["integrals"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal}.", [move])
                self.assertEqual(r["report"], "Proved.", r)
                self.assertEqual(r["auto"][-1], f"close {value} by ring.")
                self.assertEqual(r["admissions"], 0)

    def test_periodicity(self):
        r = run("goal sin(4*pi) + cos(-3*pi) == ?A.", ["simpl."])
        self.assertEqual((r["report"], r["auto"][-1]),
                         ("Proved.", "close -1 by ring."))


class TeX(unittest.TestCase):
    def test_round_trips(self):
        sig = {"z": "complex"}
        for text in ("3 + 4*i", "re z + im z", "conj(z - 1)", "Log z",
                     "log[2*pi](z + 1)", "Arg(-1)", "abs(z - i)",
                     "Sqrt(z + 1)", "exp(i*Arg z)"):
            with self.subTest(text=text):
                t = parse_term(text, sig)
                self.assertEqual(untex.read(tex._t(t), sig), t)

    def test_i_is_drawn_as_i(self):
        self.assertEqual(tex._t(parse_term("i")), "i")


class Persistence(unittest.TestCase):
    def test_a_complex_session_saves_and_replays(self):
        s, n = api.handle("POST", "/session", {
            "header": "goal z*conj z == ?A complex z.", "auto_simpl": False})
        s, r = api.handle("POST", "/tactic", {
            "session": n["session"], "node": "n0",
            "text": "close (re z)^2 + (im z)^2."})
        doc = work.document(api.SESSIONS[n["session"]])
        self.assertEqual(doc["functions"], {"z": "complex"})
        s, out = api.handle("POST", "/import", {"document": doc})
        self.assertEqual(out["resumed"]["dropped"], [])
        s, t = api.handle("GET", "/tree", {"session": out["session"]})
        self.assertEqual(t["nodes"][-1]["report"], "Proved.")


if __name__ == "__main__":
    unittest.main()
