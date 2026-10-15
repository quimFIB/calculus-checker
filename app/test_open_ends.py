"""Improper integrals at a finite end (kernel/p1_expected E222-E230),
through the app."""

import unittest

import session  # noqa: F401  puts kernel/ on the path

from terms import parse_term  # noqa: E402
from test_complex import run  # noqa: E402


class OpenEnds(unittest.TestCase):

    def test_integrals(self):
        import p1_expected as X
        from proof_of_life import _k1_eval
        for goal, sentences, value in X.OPEN_END_CASES["integrals"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal}.", sentences)
                self.assertEqual((r["report"], r["admissions"]),
                                 ("Proved.", 0), r)
                v = r["auto"][-1].split("close ", 1)[1].rsplit(" by ", 1)[0]
                self.assertAlmostEqual(
                    complex(_k1_eval(parse_term(v), {})),
                    complex(_k1_eval(parse_term(value), {})), places=9)

    def test_refusals(self):
        import p1_expected as X
        for text, code in X.OPEN_END_CASES["refusals"]:
            with self.subTest(text=text):
                r = run(f"goal {text}.", [])
                self.assertEqual(r["refusal"]["code"], code, r)

    def test_move_refusals(self):
        import p1_expected as X
        for goal, sentence, code in X.OPEN_END_CASES["move_refusals"]:
            with self.subTest(goal=goal, sentence=sentence):
                r = run(f"goal {goal}.", [f"{sentence}."])
                self.assertEqual(r["refusal"]["code"], code, r)

    def test_review_rows(self):  # E231
        import p1_expected as X
        from proof_of_life import _k1_eval
        for goal, sentence, want in X.OPEN_END_CASES["review"]:
            with self.subTest(goal=goal):
                r = run(f"goal {goal}.", [f"{sentence}."])
                if "refusal" in r:
                    self.assertEqual(r["refusal"]["code"], want, r)
                    continue
                self.assertEqual((r["report"], r["admissions"]),
                                 ("Proved.", 0), r)
                v = r["auto"][-1].split("close ", 1)[1].rsplit(" by ", 1)[0]
                self.assertAlmostEqual(
                    complex(_k1_eval(parse_term(v), {})),
                    complex(_k1_eval(parse_term(want), {})), places=9)

    def test_tex_and_2d(self):
        import pretty2d
        import tex
        t = parse_term("Int[x = 0+ .. 1] 1/sqrt x")
        self.assertIn("{0}^{+}", tex._t(t))
        self.assertIn("0+", pretty2d.pretty(t))

    def test_palette_offers_int_improper(self):
        from assist import palette
        from terms import parse_goal
        names = [m["move"] for m in palette.moves(parse_goal(
            "Int[x = 0+ .. 1] 1/sqrt x == ?A"))]
        self.assertIn("int_improper", names)
        self.assertNotIn("ftc", names)


if __name__ == "__main__":
    unittest.main()
