"""GOALS2D.md: the 2D drawings of fixed shapes, and every problem's goals
and a generated family of terms laid out as rectangles."""

import os
import random
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import pretty2d  # noqa: E402
from session import K, loader  # noqa: E402
from terms import parse_goal, parse_term  # noqa: E402
from test_tex import gen  # noqa: E402
import api  # noqa: E402


def draw(s):
    return [r.rstrip() for r in pretty2d.pretty(parse_term(s)).split("\n")]


class Shapes(unittest.TestCase):
    def test_fraction(self):
        self.assertEqual(draw("(1 + x)/2"), ["1 + x", "─────", "  2"])

    def test_root(self):
        self.assertEqual(draw("sqrt(1 - x)"), ["  ______", "╲╱ 1 - x"])

    def test_tall_root(self):
        self.assertEqual(draw("sqrt(1/x)"),
                     ["    __", "   ╱ 1", "  ╱  ─", "╲╱   x"])

    def test_integral(self):
        self.assertEqual(draw("Int[x = 0 .. pi/2] (cos x)^2"),
                         ["π", "─", "2", "⌠", "⎮ (cos x)² dx", "⌡", "0"])

    def test_powers(self):
        self.assertEqual(draw("x^(-1) + t^12"), ["x⁻¹ + t¹²"])
        self.assertEqual(draw("x^(1/2)"), [" 1", " ─", " 2", "x"])

    def test_derivative_and_tall_parens(self):
        self.assertEqual(draw("D[x] (x/2)"), ["d ⎛x⎞", "──⎜─⎟", "dx⎝2⎠"])

    def test_goal_relation_sits_on_the_bar(self):
        rows = pretty2d.pretty(parse_goal("1/2 == ?A", {})).split("\n")
        self.assertEqual([r.rstrip() for r in rows], ["1", "─ = ?A", "2"])


class Rectangles(unittest.TestCase):
    def rect(self, x):
        rows = pretty2d.pretty(x).split("\n")
        self.assertEqual(len({len(r) for r in rows}), 1, rows)

    def test_problem_goals_and_proof_nodes(self):
        n = 0
        for pid, (p, _, _) in api._problem_files().items():
            with self.subTest(pid):
                self.rect(parse_goal(p.goal_text, p.sig))
            for name in p.proofs:
                results, _ = loader.replay(p, name)
                for _, st in results:
                    if isinstance(st, K.Refusal):
                        continue
                    for x in (st.goal, st.theorem):
                        if x is not None:
                            with self.subTest(pid=pid, proof=name):
                                self.rect(x)
                                n += 1
        self.assertGreater(n, 40)

    def test_generated(self):
        rng = random.Random(20260926)
        for _ in range(2000):
            t = gen(rng, 4)
            self.rect(t)


if __name__ == "__main__":
    unittest.main()
