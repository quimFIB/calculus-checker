"""Tests for the recognizer spike. Run: python3 -m unittest -v (in this directory).

The scores are pinned deliberately. They are the spike's result, so a change
to a row that moves one has to be a decision, not a side effect.
"""

import unittest

import rows
from corpus import CORPUS, HELD_OUT
from report import score, verdict
from shapes import completed_constant_sign, poly_in, quadratic, rational_in, sign
from terms import parse


class Shapes(unittest.TestCase):
    def test_polynomials_are_seen_through_spelling(self):
        a, b = poly_in(parse("x*(x + 1)"), "x"), poly_in(parse("x^2 + x"), "x")
        self.assertEqual(a.coeffs, b.coeffs)
        self.assertEqual(a.degree, 2)

    def test_x_inside_an_atom_is_not_a_polynomial(self):
        self.assertIsNone(poly_in(parse("x + sin x"), "x"))
        self.assertIsNone(poly_in(parse("1/(1 + x)"), "x"))
        self.assertIsNotNone(poly_in(parse("sin(a)*x"), "x"))

    def test_rational_functions(self):
        num, den = rational_in(parse("1/(1 + x^3)"), "x")
        self.assertEqual((num.degree, den.degree), (0, 3))
        self.assertIsNone(rational_in(parse("1/(1 + exp x)"), "x"))

    def test_signs_take_symbols_as_positive(self):
        q = quadratic(parse("E - k*x^2"), "x")
        self.assertEqual((sign(q.coeff(2)), sign(q.coeff(0))), (-1, 1))
        q = quadratic(parse("(a + e) + (a - e)*t^2"), "t")
        self.assertEqual(sign(q.coeff(2)), 0)  # a − e: unknown, not negative

    def test_completing_the_square(self):
        self.assertEqual(completed_constant_sign(quadratic(parse("x^2 - x + 1"), "x")), 1)
        self.assertEqual(completed_constant_sign(quadratic(parse("x^2 - 3*x + 1"), "x")), -1)


class Scores(unittest.TestCase):
    """The spike's result, as numbers."""

    def test_v1_on_the_corpus(self):
        s, l, n, rest = score(CORPUS, rows.V1)
        self.assertEqual((s, l, n), (15, 16, 22))
        self.assertEqual(rest, {"wrong": 2, "silent": 2, "gap": 2})

    def test_v2_on_the_corpus_it_was_fitted_to(self):
        self.assertEqual(score(CORPUS, rows.V2)[:3], (22, 22, 22))

    def test_held_out_v2_is_no_better_than_v1(self):
        self.assertEqual(score(HELD_OUT, rows.V1)[:3], (3, 4, 9))
        self.assertEqual(score(HELD_OUT, rows.V2)[:3], (3, 4, 9))


class Findings(unittest.TestCase):
    """Each finding in README.md, as a test that fails if it stops being true."""

    def by_id(self, i):
        return next(e for e in CORPUS + HELD_OUT if e["id"] == i)

    def test_parts_row_misses_its_own_canonical_example(self):
        # §8.5 says the P(x)·e^{ax} row 'knows about' ∫ eˣ sin x, but its
        # pattern needs a polynomial factor, and eˣ sin x has none.
        hits = rows.recognize(parse("exp(x) * sin(x)"), "x", rows.V1)
        self.assertNotIn("parts", [r.name for r, _ in hits])

    def test_no_row_for_the_chain_rule(self):
        # f′(x)·g(f(x)): the commonest substitution of all has no row.
        for t, x in (("x * exp(x^2)", "x"), ("sin x * (cos x)^2", "x"),
                     ("w/sqrt(1 - w^2)", "w")):
            families = {r.family for r, _ in rows.recognize(parse(t), x, rows.V2)}
            self.assertNotIn("chain-rule substitution", families, t)

    def test_matching_is_on_the_written_form(self):
        # sin²t + cos²t is −1 after pyth, but the rows see the raw term, so
        # the Weierstrass row fires on a constant.
        v, top, _ = verdict(self.by_id("U04-P3"), rows.V2)
        self.assertEqual((v, top.name), ("wrong", "Weierstrass"))

    def test_f_prime_over_f_reads_the_syntactic_denominator(self):
        # 1/(u ln(1/u)) is −(ln(1/u))′/ln(1/u), but the row takes the whole
        # denominator u·ln(1/u) as f, and its derivative is not ∝ 1.
        self.assertEqual(verdict(self.by_id("U01-P2"), rows.V2)[0], "silent")

    def test_every_hit_renders_a_rung_3(self):
        for e in CORPUS + HELD_OUT:
            for table in (rows.V1, rows.V2):
                for row, p in rows.recognize(parse(e["integrand"]), e["x"], table):
                    self.assertTrue(row.detail(p), (e["id"], row.name))


if __name__ == "__main__":
    unittest.main()
