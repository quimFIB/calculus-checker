"""UI.md §1: read(tex(t)) == t over the corpus, every reference proof's
goals and a generated family of terms."""

import os
import random
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import tex  # noqa: E402
from session import K, loader  # noqa: E402
from terms import (NEG_INF, POS_INF, Add, App, BUILTINS, Call, Const,  # noqa: E402
                   Deriv, Div, Integral, Mul, Neg, Num, Pow, RPow, Var,
                   parse_goal, parse_term, show)
import api  # noqa: E402

NAMES = ["x", "t", "a", "k1", "v_0", "theta", "sigma_2", "w1_b"]
SIG = {"f": 1, "g": 2}


def gen(rng, depth, bound=()):
    """A random term, every node type reachable."""
    if depth == 0 or rng.random() < 0.2:
        c = rng.randrange(4)
        if c == 0:
            return Num(rng.randrange(0, 13))
        if c == 1:
            return Const(rng.choice(["pi", "e_const"]))
        return Var(rng.choice(NAMES))
    d = depth - 1
    c = rng.randrange(13)
    if c == 0:
        return Add(gen(rng, d, bound), gen(rng, d, bound))
    if c == 1:
        return Add(gen(rng, d, bound), Neg(gen(rng, d, bound)))
    if c == 2:
        return Mul(gen(rng, d, bound), gen(rng, d, bound))
    if c == 3:
        return Div(gen(rng, d, bound), gen(rng, d, bound))
    if c == 4:
        return Neg(gen(rng, d, bound))
    if c == 5:
        return Pow(gen(rng, d, bound), rng.choice([-3, -1, 0, 2, 5]))
    if c == 6:
        e = gen(rng, d, bound)
        if isinstance(e, Num) or isinstance(e, Neg) and isinstance(e.a, Num):
            e = Var("n")
        return RPow(gen(rng, d, bound), e)
    if c in (7, 8):
        return App(rng.choice(sorted(BUILTINS)), gen(rng, d, bound))
    if c == 9:
        return Deriv(rng.choice(["x", "t"]), gen(rng, d, bound))
    if c == 10:
        return Call("f", (gen(rng, d, bound),)) if rng.random() < 0.5 else \
            Call("g", (gen(rng, d, bound), gen(rng, d, bound)))
    v = rng.choice([n for n in ("u", "s", "phi") if n not in bound])
    ends = [gen(rng, 1, bound), gen(rng, 1, bound), POS_INF, NEG_INF]
    return Integral(v, rng.choice(ends[:1] + ends[3:]),
                    rng.choice(ends[1:3]), gen(rng, d, bound + (v,)))


class RoundTrip(unittest.TestCase):
    def check(self, x, kind, sig=None):
        t = tex.tex(x)
        self.assertEqual(tex.read(t, kind, sig), x, t)

    def test_problem_goals_and_proof_nodes(self):
        n = 0
        for pid, (p, _, _) in api._problem_files().items():
            goal = parse_goal(p.goal_text, p.sig)
            with self.subTest(pid):
                self.check(goal, "goal", p.sig)
            for name in p.proofs:
                results, _ = loader.replay(p, name)
                for _, st in results:
                    if isinstance(st, K.Refusal):
                        continue
                    for x in (st.goal, st.theorem):
                        if x is not None:
                            with self.subTest(pid=pid, proof=name):
                                self.check(x, "goal", p.sig)
                                n += 1
        self.assertGreater(n, 40)

    def test_generated(self):
        rng = random.Random(20260925)
        kept = 0
        for _ in range(3000):
            t = gen(rng, 4)
            try:  # only terms the grammar itself round-trips
                if parse_term(show(t), SIG) != t:
                    continue
            except Exception:
                continue
            kept += 1
            with self.subTest(show(t)):
                self.check(t, "term", SIG)
        self.assertGreater(kept, 1000)

    def test_shapes(self):
        for s, want in [
                ("x^2", "x^{2}"),
                ("(sin x)^2", r"\left(\sin x\right)^{2}"),
                ("1/2", r"\frac{1}{2}"),
                ("sqrt(1 - x^2)", r"\sqrt{1 - x^{2}}"),
                ("Int[x = 0 .. oo] exp(-x)",
                 r"\int_{0}^{\infty} {\exp\left(-x\right)} \,\mathrm{d}{x}"),
                ("theta1 * v_0", r"\theta 1 \cdot v_{0}")]:
            with self.subTest(s):
                self.assertEqual(tex.tex(parse_term(s)), want)


if __name__ == "__main__":
    unittest.main()
