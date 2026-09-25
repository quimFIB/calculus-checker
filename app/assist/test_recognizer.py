"""The recognizer (RECOGNIZER.md, Done when 1): each row on its own
examples, and both scores pinned. The held-out score is pinned so a change
to the table shows up here; it is never a target (Scoring)."""

import unittest

from assist import corpus, recognizer as R, score
from terms import parse_term

# row family -> integrands in x that it must be the first match for
EXAMPLES = {
    "identity first": ["(cos x)^2", "sin(2*x)*cos(2*x)",
                       "sin x*(-sin x) + (-cos x)*cos x"],
    "standard": ["5", "3*x^2 + 2*x", "x^n", "1/x^2", "7/(2*x + 1)^3",
                 "F0*exp(-x/tau)", "sinh(2*x) + 3", "1/(x^2 + a^2)",
                 "M/(M*g - c*x^2)", "1/sqrt(4 - x^2)", "x^(-1/2)"],
    "log": ["1/(x + v)", "x/(x^2 + 1)", "tan(3*x)", "tanh(g*x/v)",
            "1/(x*ln(1/x))"],
    "parameter differentiation": ["1/(x^2 + a^2)^2",
                                  "1/(1 + e1*cos x)^2"],
    "chain-rule substitution": ["x*exp(x^2)", "x/sqrt(1 - x^2)"],
    "parts cycle": ["exp(2*x)*sin(3*x)", "exp(-x)*cos x"],
    "parts": ["x*sin x", "(x + 1)*exp(x)", "x^2*ln x", "atan x"],
    "split numerator": ["(x - 2)/(x^2 - x + 1)",
                        "(x + sqrt 2)/(x^2 + sqrt(2)*x + 1)"],
    "partial fractions": ["1/(1 + x^3)", "1/(x^2 - 3*x + 2)",
                          "1/(x*(x + 1))", "1/(x^2 + 1)^2"],
    "trig substitution": ["1/sqrt(x*(1 - x))", "sqrt(1 - x^2)*x^2"],
    "hyperbolic substitution": ["1/sqrt(x^2 - s1^2)",
                                "sqrt(x^2 + 4*x + 13)"],
    "Weierstrass": ["1/(1 + e1*cos x)", "1/(1 + cos x)^2"],
    "root substitution": ["sin(sqrt x)", "x*sqrt(x + 1)", "exp(sqrt x)"],
    "Beta substitution": ["1/sqrt(E - k*x^n)", "sqrt(1 - x^n)"],
    "orthogonality": ["sin(m*x)*cos(n*x)", "sin(m*x)*sin(n*x)"],
}
SILENT = ["abs(x)", "1/(x + ln x)", "exp(x^2)"]


class Rows(unittest.TestCase):
    def test_every_row_has_examples(self):
        self.assertEqual(set(EXAMPLES), set(R.FAMILIES))

    def test_examples(self):
        for fam, xs in EXAMPLES.items():
            for s in xs:
                with self.subTest(s):
                    hit = R.first(parse_term(s), "x")
                    self.assertIsNotNone(hit)
                    self.assertEqual(hit[0].family, fam)
                    for rung in (1, 2, 3):
                        self.assertTrue(R.ladder(parse_term(s), "x")[rung])

    def test_silent(self):
        for s in SILENT:
            with self.subTest(s):
                self.assertIsNone(R.first(parse_term(s), "x"))

    def test_other_variable(self):
        hit = R.first(parse_term("x*t*sin t"), "t")
        self.assertEqual(hit[0].family, "parts")


class Scores(unittest.TestCase):
    def test_development(self):
        s = score.score(corpus.DEVELOPMENT)
        self.assertEqual((s["strict"], s["lenient"], s["rowed"]),
                         (28, 28, 30))

    def test_heldout(self):
        """Scored once for table version 1 (WHAT.md). Not tuned on."""
        s = score.score(score.heldout())
        self.assertEqual((s["strict"], s["lenient"], s["rowed"]),
                         (18, 20, 28))


if __name__ == "__main__":
    unittest.main()
