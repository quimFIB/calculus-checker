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


class ComplexVariable(unittest.TestCase):
    """K3 (E183-E189) through the app."""

    def test_d_z_verifies_and_refuses_what_is_not_holomorphic(self):
        r = run("goal D[z] Log z == 1/z @ re z > 0 complex z.",
                ["verify by field."])
        self.assertEqual(r["report"], "Proved.")
        r = run("goal D[z] conj z == 1 complex z.", [])
        self.assertEqual(r["refusal"]["code"], "deriv-not-holomorphic")


class Contours(unittest.TestCase):
    """K4a (E190-E198): contour integrals, parametrised by cint_param and
    closed by ftc and auto-simpl."""

    def test_integrals(self):
        import p1_expected as X
        for goal, sentences, value in X.K4A_CASES["integrals"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal} complex w.", sentences)
                self.assertEqual(r["report"], "Proved.", r)
                self.assertEqual(r["auto"][-1], f"close {value} by ring.")
                self.assertEqual(r["admissions"], 0)

    def test_move_refusals(self):
        import p1_expected as X
        for goal, sentence, code in X.K4A_CASES["move_refusals"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal} complex w.", [f"{sentence}."])
                self.assertEqual(r["refusal"]["code"], code, r)

    def test_review_rows(self):  # E199
        import p1_expected as X
        for header, sentences, want in X.K4A_CASES["review"]:
            with self.subTest(header=header):
                r = run(header, sentences)
                if "refusal" in r:
                    self.assertEqual(r["refusal"]["code"], want, r)
                    continue
                self.assertEqual((r["report"], r["admissions"]),
                                 ("Proved.", 0), r)
                self.assertEqual(r["auto"][-1], f"close {want} by ring.")

    def test_tex_and_2d_draw_a_contour_integral(self):  # E199
        import pretty2d
        import tex
        from terms import parse_term
        t = parse_term("CInt[z on circle(0, 1)] 1/z", {"z": "complex"})
        self.assertEqual(tex._t(t), r"\int_{\operatorname{circle}"
                         r"\left(0, 1\right)} {\frac{1}{z}} \,\mathrm{d}{z}")
        self.assertEqual(pretty2d.pretty(t).splitlines()[-1].strip(),
                         "circle(0, 1)")

    def test_cint_param_names_a_fresh_variable(self):
        # t is taken by the goal, so the parameter is t_1
        r = run("goal CInt[w on seg(0, t)] w == ?A complex w.",
                ["cint_param."])
        self.assertIn("Int[t_1 = 0 .. 1]", r["goal"], r)


class Residues(unittest.TestCase):
    """K4b (E200-E210): the residue theorem by one move, closed by
    auto-simpl."""

    def test_integrals(self):
        import p1_expected as X
        for goal, sentences, value in X.K4B_CASES["integrals"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal} complex w.", sentences)
                self.assertEqual(r["report"], "Proved.", r)
                self.assertEqual(r["auto"][-1], f"close {value} by ring.")
                self.assertEqual(r["admissions"], 0)

    def test_course(self):
        import p1_expected as X
        for goal, sentences in X.K4B_CASES["course"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal} complex w.", sentences)
                self.assertEqual((r["report"], r["admissions"]),
                                 ("Proved.", 0), r)

    def test_move_refusals(self):
        import p1_expected as X
        for goal, sentence, code in X.K4B_CASES["move_refusals"]:
            with self.subTest(goal=goal, sentence=sentence):
                r = run(f"goal {goal} complex w.", [f"{sentence}."])
                self.assertEqual(r["refusal"]["code"], code, r)

    def test_never_proved(self):
        import p1_expected as X
        for goal, sentence in X.K4B_CASES["never_proved"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal} complex w.", [f"{sentence}."])
                self.assertNotEqual(r.get("report"), "Proved.", r)

    def test_review_rows(self):  # E211
        import p1_expected as X
        for header, sentences, want in X.K4B_CASES["review"]:
            with self.subTest(header=header):
                r = run(header, sentences)
                if "refusal" in r:
                    self.assertEqual(r["refusal"]["code"], want, r)
                    continue
                self.assertEqual((r["report"], r["admissions"]),
                                 ("Proved.", 0), r)
                self.assertEqual(r["auto"][-1], f"close {want} by ring.")

    def test_the_sentence_round_trips(self):
        import script
        for text in ("residues.", "residues in re w > 0.",
                     "residues in re w > 0, abs(w - 1) < 2 occurrence 1."):
            with self.subTest(text=text):
                move, args = script.parse(text)
                self.assertEqual(script.show(move, args), text)

    def test_palette_offers_residues(self):
        from assist import palette
        from terms import parse_goal
        g = parse_goal("CInt[w on circle(0, 1)] 1/w == ?A", {"w": "complex"})
        self.assertIn("residues", [m["move"] for m in palette.moves(g)])


class LineIntegrals(unittest.TestCase):
    """K4c-i (E212-E220): Z10, a line integral closed in a half-plane,
    and int_even, through the app."""

    def test_integrals(self):
        import p1_expected as X
        from proof_of_life import _k1_eval
        for goal, sentences, value in X.K4C_CASES["integrals"]:
            with self.subTest(goal=goal, sentences=sentences):
                r = run(f"goal {goal}.", sentences)
                self.assertEqual((r["report"], r["admissions"]),
                                 ("Proved.", 0), r)
                v = r["auto"][-1].split("close ", 1)[1].rsplit(" by ", 1)[0]
                self.assertAlmostEqual(
                    complex(_k1_eval(parse_term(v), {})),
                    complex(_k1_eval(parse_term(value), {})), places=9)

    def test_symbolic(self):
        import p1_expected as X
        for header, sentences in X.K4C_CASES["symbolic"]:
            with self.subTest(header=header):
                r = run(header, sentences)
                self.assertEqual((r["report"], r["admissions"]),
                                 ("Proved.", 0), r)

    def test_move_refusals(self):
        import p1_expected as X
        for goal, sentence, code in X.K4C_CASES["move_refusals"]:
            with self.subTest(goal=goal, sentence=sentence):
                r = run(f"goal {goal}.", [f"{sentence}."])
                self.assertEqual(r["refusal"]["code"], code, r)

    def test_never_proved(self):
        import p1_expected as X
        for goal, sentence in X.K4C_CASES["never_proved"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal}.", [f"{sentence}."])
                self.assertNotEqual(r.get("report"), "Proved.", r)

    def test_review_rows(self):  # E221
        import p1_expected as X
        from proof_of_life import _k1_eval
        for header, sentence, want in X.K4C_CASES["review"]:
            with self.subTest(header=header):
                r = run(header, [f"{sentence}."])
                if "refusal" in r:
                    self.assertEqual(r["refusal"]["code"], want, r)
                    continue
                self.assertEqual((r["report"], r["admissions"]),
                                 ("Proved.", 0), r)
                v = r["auto"][-1].split("close ", 1)[1].rsplit(" by ", 1)[0]
                self.assertNotIn("0/", v)  # fully evaluated (E221 (3))
                self.assertAlmostEqual(
                    complex(_k1_eval(parse_term(v), {})),
                    complex(_k1_eval(parse_term(want), {})), places=9)

    def test_sentences_round_trip(self):
        import script
        for text in ("residues upper.", "residues lower occurrence 1.",
                     "int_even.", "int_even occurrence 2."):
            with self.subTest(text=text):
                move, args = script.parse(text)
                self.assertEqual(script.show(move, args), text)

    def test_palette_offers_the_closings(self):
        from assist import palette
        from terms import parse_goal
        names = [m["sentence"] for m in palette.moves(parse_goal(
            "Int[x = 0 .. oo] 1/(x^2 + 1) == ?A"))]
        self.assertIn("int_even.", names)
        names = [m["sentence"] for m in palette.moves(parse_goal(
            "Int[x = -oo .. oo] 1/(x^2 + 1) == ?A"))]
        self.assertIn("residues upper.", names)


class Keyhole(unittest.TestCase):
    """K4c-ii (E232-E240): residues keyhole, through the app."""

    def test_integrals(self):
        import p1_expected as X
        from proof_of_life import _k1_eval
        for goal, sentences, value in X.K4D_CASES["integrals"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal}.", sentences)
                self.assertEqual((r["report"], r["admissions"]),
                                 ("Proved.", 0), r)
                v = r["auto"][-1].split("close ", 1)[1].rsplit(" by ", 1)[0]
                self.assertNotIn("arg[", v)  # fully evaluated (E239)
                self.assertAlmostEqual(
                    complex(_k1_eval(parse_term(v), {})),
                    complex(_k1_eval(parse_term(value), {})), places=9)

    def test_symbolic(self):
        import p1_expected as X
        for header, sentences, report in X.K4D_CASES["symbolic"]:
            with self.subTest(header=header):
                self.assertEqual(run(header, sentences)["report"], report)

    def test_move_refusals(self):
        import p1_expected as X
        for goal, sentence, code in X.K4D_CASES["move_refusals"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal}.", [f"{sentence}."])
                self.assertEqual(r["refusal"]["code"], code, r)

    def test_sentence_round_trips(self):
        import script
        move, args = script.parse("residues keyhole occurrence 1.")
        self.assertEqual(script.show(move, args),
                         "residues keyhole occurrence 1.")


class Sector(unittest.TestCase):
    """Z12 and 20 P9 (E242-E248), through the app."""

    def test_integrals(self):
        import p1_expected as X
        from proof_of_life import _k1_eval
        for goal, sentences, value in (X.SECTOR_CASES["integrals"]
                                       + X.SECTOR_CASES["review"]):
            with self.subTest(goal=goal):
                r = run(f"goal {goal}.", sentences)
                self.assertEqual((r["report"], r["admissions"]),
                                 ("Proved.", 0), r)
                v = r["auto"][-1].split("close ", 1)[1].rsplit(" by ", 1)[0]
                self.assertAlmostEqual(
                    complex(_k1_eval(parse_term(v), {})),
                    complex(_k1_eval(parse_term(value), {})), places=9)

    def test_symbolic(self):
        import p1_expected as X
        for header, sentences, report in X.SECTOR_CASES["symbolic"]:
            with self.subTest(header=header):
                self.assertEqual(run(header, sentences)["report"], report)

    def test_move_refusals(self):
        import p1_expected as X
        for goal, sentence, code in X.SECTOR_CASES["move_refusals"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal}.", [f"{sentence}."])
                self.assertEqual(r["refusal"]["code"], code, r)


class Upgrade(unittest.TestCase):
    """E250-E252: a later discharge upgrades an admission."""

    def test_reports(self):
        import p1_expected as X
        for header, sentences, report in X.UPGRADE_CASES["reports"]:
            with self.subTest(header=header):
                self.assertEqual(run(header, sentences)["report"], report)

    def test_the_tracker_takes_a_later_discharge(self):
        import kernel as K
        old = K.Obligation("k", frozenset(("a",)), K.ADMITTED, ("none", ()))
        new = K.Obligation("k", frozenset(("b",)), K.DISCHARGED,
                           ("norm_num", ()))
        t = K._Tracker()
        t.add(old)
        t.add(new)
        (ob,) = t.entries()
        self.assertEqual((ob.status, ob.sources), (K.DISCHARGED,
                                                   frozenset(("a", "b"))))
        t.add(old)  # a DISCHARGED key is never touched again
        self.assertEqual(t.entries()[0].status, K.DISCHARGED)


class ReIm(unittest.TestCase):
    """E257-E262: re and im through an Int, parity in int_even."""

    def test_integrals(self):
        import p1_expected as X
        from proof_of_life import _k1_eval
        for goal, sentences, value in (X.REIM_CASES["integrals"] + X.P7_CASES
                                       + X.REIM_CASES["review"]):
            with self.subTest(goal=goal):
                r = run(f"goal {goal}.", sentences)
                self.assertEqual((r["report"], r["admissions"]),
                                 ("Proved.", 0), r)
                v = r["auto"][-1].split("close ", 1)[1].rsplit(" by ", 1)[0]
                self.assertAlmostEqual(
                    complex(_k1_eval(parse_term(v), {})),
                    complex(_k1_eval(parse_term(value), {})), places=9)

    def test_move_refusals(self):
        import p1_expected as X
        for goal, sentence, code in X.REIM_CASES["move_refusals"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal}.", [f"{sentence}."])
                self.assertEqual(r["refusal"]["code"], code, r)

    def test_sentences_round_trip(self):
        import script
        for text in ("int_re exp(i*x)/(x^2 + 1).", "int_im x occurrence 1."):
            move, args = script.parse(text)
            self.assertEqual(script.show(move, args), text)


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
