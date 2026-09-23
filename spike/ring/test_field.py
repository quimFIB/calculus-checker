"""Tests for the stage 0c spike. Run: python3 -m unittest -v (in this directory).

Three kinds. The worked cases are DESIGN.md's own examples. The refusals are
the fragment's edges. The property tests are the ones that matter: `field` is
the component whose bug is a false `Proved` (§17), so they check its verdicts
against exact evaluation, which shares no code with the normaliser.
"""

import random
import unittest
from fractions import Fraction

from deriv import deriv
from field import Refused, field, ring
from terms import evaluate, parse, replace, show, subterms

# Any rational function is a model of an opaque atom, so exact evaluation
# with this standing in for the declared symbol f is an honest oracle.
FUNCS = {"f": lambda v: 3 * v * v - v + Fraction(7, 2)}


def open_divisors(result):
    return sorted(o.divisor for o in result.open_obligations)


class Ring(unittest.TestCase):
    def test_commutative_ring_facts(self):
        self.assertTrue(ring("sin x + cos x", "cos x + sin x").holds)
        self.assertTrue(ring("(x + 1)^2", "x^2 + 2*x + 1").holds)
        self.assertTrue(ring("(a - b)*(a + b)", "a^2 - b^2").holds)
        self.assertTrue(ring("x/3 + x/6", "x/2").holds)

    def test_atoms_are_opaque(self):
        # §6.2: sin²x + cos²x ≐ 1 needs `pyth`; ring must not know it.
        self.assertFalse(ring("(sin x)^2 + (cos x)^2", "1").holds)

    def test_atoms_identified_up_to_their_arguments(self):
        self.assertTrue(ring("sin(x + 1) - sin(1 + x)", "0").holds)
        self.assertTrue(ring("f(2*x) * g(x, y)", "g(x, y) * f(x + x)").holds)
        self.assertFalse(ring("f(x)", "f(y)").holds)

    def test_division_is_not_a_ring_operation(self):
        # STAGE0.md gap 2: m·(1/m) cancels only in a field.
        r = ring("m * (1/m)", "1")
        self.assertFalse(r.holds)
        self.assertEqual(r.residual, "m*(1 / m) - 1")

    def test_residual_names_the_missing_term(self):
        # §11.1's factor of 2: F := sin t − t cos t is short by t·sin t.
        wrong = deriv(parse("sin t - t*cos t"), "t")
        r = ring(wrong, "sin t * (2*t)")
        self.assertFalse(r.holds)
        self.assertEqual(r.residual, "-t*sin(t)")
        right = deriv(parse("2*sin t - 2*t*cos t"), "t")
        self.assertTrue(ring(right, "sin t * (2*t)").holds)


class Field(unittest.TestCase):
    def test_cancelling_emits_the_obligation(self):
        r = field("m * (1/m)", "1")
        self.assertTrue(r.holds)
        self.assertEqual(open_divisors(r), ["m"])

    def test_both_spellings_emit_the_same_obligation(self):
        # §5.1: x^(-1) and 1/x must not differ in what they owe.
        a, b = field("x * x^(-1)", "1"), field("x * (1/x)", "1")
        self.assertTrue(a.holds and b.holds)
        self.assertEqual(open_divisors(a), open_divisors(b))
        self.assertEqual(open_divisors(a), ["x"])

    def test_nested_divisors_each_owe(self):
        r = field("1/(1 + 1/x)", "x/(x + 1)")
        self.assertTrue(r.holds)
        self.assertEqual(open_divisors(r), ["1 + 1 / x", "x", "x + 1"])

    def test_divisors_inside_atoms_owe(self):
        r = field("sin(x/x)", "sin(x/x)")
        self.assertTrue(r.holds)
        self.assertEqual(open_divisors(r), ["x"])

    def test_literal_divisors_are_discharged(self):
        r = field("x/3", "(1/3)*x")
        self.assertTrue(r.holds)
        self.assertEqual(r.open_obligations, ())
        self.assertTrue(all(o.discharged_by == "norm_num" for o in r.obligations))

    def test_common_denominator_is_not_squared(self):
        r = field("1/(x+1) + 1/(x+1)", "2/(1+x)")
        self.assertTrue(r.holds)
        self.assertEqual(r.denominator_factors, 1)

    def test_telescoping_partial_fractions(self):
        lhs = " + ".join(f"1/((x + {k})*(x + {k + 1}))" for k in range(1, 9))
        self.assertTrue(field(lhs, "1/(x + 1) - 1/(x + 9)").holds)
        self.assertFalse(field(lhs, "1/(x + 1) - 1/(x + 10)").holds)

    def test_linear_drag_ode(self):
        # §6.5 / STAGE0.md gap 2: m·v' = −b·v, v = v0·exp(−b·t/m).
        v = parse("v0 * exp(-b*t/m)")
        lhs = ("mul", parse("m"), deriv(v, "t"))
        rhs = ("mul", parse("-b"), v)
        self.assertFalse(ring(lhs, rhs).holds)
        r = field(lhs, rhs)
        self.assertTrue(r.holds)
        self.assertIn("m", open_divisors(r))


class Facts(unittest.TestCase):
    F = "(1/3)*ln(1+x) - (1/6)*ln(x^2 - x + 1) + (1/sqrt 3)*atan((2*x - 1)/sqrt 3)"

    def test_flagship_needs_the_fact(self):
        # §11.2: with sqrt 3 opaque, D[x]F ≐ 1/(1+x³) is false in ℚ(x, s).
        dF = deriv(parse(self.F), "x")
        self.assertFalse(field(dF, "1/(1 + x^3)").holds)
        r = field(dF, "1/(1 + x^3)", facts=[("(sqrt 3)^2", "3")])
        self.assertTrue(r.holds)
        # All open until §5.3 discharges them. The last is not among §11.2's:
        # it is d_atan's own denominator, and needs method 4 to read it as
        # written — 1 + u^2 — rather than after ring-normalising u.
        self.assertEqual(open_divisors(r), sorted([
            "1 + x", "x^2 - x + 1", "sqrt(3)", "1 + x^3",
            "1 + ((2 * x - 1) / sqrt(3))^2",
        ]))

    def test_flagship_residual_matches_the_design(self):
        # §11.2 states the residual as (3/2 − s²/2)/(s²x² − s²x + s² + 4x⁴
        # − 8x³ + 9x² − 5x + 1). The spike's must be the same rational function.
        dF = deriv(parse(self.F), "x")
        stated = parse("(3/2 - sqrt(3)^2/2) / (sqrt(3)^2*x^2 - sqrt(3)^2*x"
                       " + sqrt(3)^2 + 4*x^4 - 8*x^3 + 9*x^2 - 5*x + 1)")
        lhs = ("add", dF, ("neg", parse("1/(1 + x^3)")))
        self.assertTrue(field(lhs, stated).holds)

    def test_rewriting_before_field_is_not_enough(self):
        # §11.2's script said `deriv; rewrite sqrt_sq_val; field`. There is
        # no (sqrt 3)^2 in deriv's output for the rewrite to act on: the
        # square that matters is ((2x − 1)/sqrt 3)^2, and s² appears only
        # once field has normalised it. The fact has to reach the normal form.
        dF = deriv(parse(self.F), "x")
        s2 = ("pow", parse("sqrt 3"), 2)
        self.assertNotIn(s2, list(subterms(dF)))
        self.assertEqual(replace(dF, s2, parse("3")), dF)
        self.assertFalse(field(dF, "1/(1 + x^3)").holds)

    def test_surd_answers_compare_equal_only_with_the_fact(self):
        # §8.7: π√3/9 against π/(3√3).
        self.assertFalse(field("pi*sqrt(3)/9", "pi/(3*sqrt 3)").holds)
        r = field("pi*sqrt(3)/9", "pi/(3*sqrt 3)", facts=[("(sqrt 3)^2", "3")])
        self.assertTrue(r.holds)
        self.assertIn("3 * sqrt(3)", open_divisors(r))

    def test_close_step(self):
        r = field("(1/3)*ln 2 + pi/(3*sqrt 3)", "(1/3)*ln 2 + pi*sqrt(3)/9",
                  facts=[("(sqrt 3)^2", "3")])
        self.assertTrue(r.holds)

    def test_fact_with_a_rational_right_side(self):
        # Unit 00 P4, quadratic drag: m·v' = m·g − k·v², v = V·tanh(g·t/V)
        # with V = sqrt(m·g/k). Needs V² = m·g/k, a fact whose right side
        # divides — and so owes k # 0 itself.
        v = parse("sqrt(m*g/k) * tanh(g*t/sqrt(m*g/k))")
        lhs = ("mul", parse("m"), deriv(v, "t"))
        rhs = ("add", parse("m*g"), ("neg", ("mul", parse("k"), ("pow", v, 2))))
        self.assertFalse(field(lhs, rhs).holds)
        r = field(lhs, rhs, facts=[("sqrt(m*g/k)^2", "m*g/k")])
        self.assertTrue(r.holds)
        self.assertIn("k", open_divisors(r))
        self.assertIn("sqrt(m * g / k)", open_divisors(r))

    def test_higher_powers_reduce(self):
        r = field("sqrt(2)^5", "4*sqrt(2)", facts=[("sqrt(2)^2", "2")])
        self.assertTrue(r.holds)
        self.assertFalse(field("sqrt(2)^5", "2*sqrt(2)",
                               facts=[("sqrt(2)^2", "2")]).holds)


class Refusals(unittest.TestCase):
    def test_division_by_zero(self):
        for rule in (ring, field):
            with self.assertRaises(Refused):
                rule("1/0", "1")
            with self.assertRaises(Refused):
                rule("1/(x - x)", "1")

    def test_malformed_facts(self):
        with self.assertRaises(Refused):
            field("x", "x", facts=[("2*sqrt(3)^2", "6")])
        with self.assertRaises(Refused):
            field("x", "x", facts=[("sqrt(3)^2", "sqrt(3) + 1")])
        with self.assertRaises(Refused):
            field("x", "x", facts=[("sqrt(3)^2", "3"), ("sqrt(3)^4", "9")])


# ------------------------------------------------------------ properties

def random_term(rng, depth):
    if depth == 0 or rng.random() < 0.25:
        r = rng.random()
        if r < 0.55:
            return ("var", rng.choice("xyz"))
        if r < 0.85:
            return ("num", Fraction(rng.randint(-3, 4), rng.choice([1, 1, 2, 3])))
        return ("app", "f", (random_term(rng, 1),))
    k = rng.choice(["add", "add", "mul", "mul", "neg", "div", "pow", "app"])
    if k in ("add", "mul", "div"):
        return (k, random_term(rng, depth - 1), random_term(rng, depth - 1))
    if k == "neg":
        return (k, random_term(rng, depth - 1))
    if k == "pow":
        return (k, random_term(rng, depth - 1), rng.randint(-2, 3))
    return ("app", "f", (random_term(rng, depth - 1),))


def commuted(rng, t):
    """t with the children of + and * shuffled at random, all the way down."""
    k = t[0]
    if k in ("add", "mul"):
        a, b = commuted(rng, t[1]), commuted(rng, t[2])
        return (k, b, a) if rng.random() < 0.5 else (k, a, b)
    if k in ("div", "rpow"):
        return (k, commuted(rng, t[1]), commuted(rng, t[2]))
    if k == "neg":
        return (k, commuted(rng, t[1]))
    if k == "pow":
        return (k, commuted(rng, t[1]), t[2])
    if k == "app":
        return (k, t[1], tuple(commuted(rng, a) for a in t[2]))
    return t


def disguised(rng, t):
    """A term equal to t wherever its divisors are nonzero."""
    u = random_term(rng, 2)
    moves = [
        lambda: ("mul", t, ("div", u, u)),
        lambda: ("add", ("add", t, u), ("neg", u)),
        lambda: ("div", ONE_, ("div", ONE_, t)),
        lambda: ("div", ("pow", t, 2), t),
        lambda: ("mul", ("pow", t, -1), ("pow", t, 2)),
        lambda: commuted(rng, t),
    ]
    return rng.choice(moves)()


ONE_ = ("num", Fraction(1))


def points(rng, n):
    for _ in range(n):
        yield {v: Fraction(rng.randint(-7, 7), rng.randint(1, 4)) for v in "xyz"}


def check_sound(testcase, result, lhs, rhs, rng, n_points=12):
    """Wherever every obligation holds, lhs and rhs must be defined and equal.

    `ring` cancels nothing and so owes nothing; for it the claim is only that
    the sides agree wherever both are defined.
    """
    obls = [parse(o.divisor) for o in result.obligations]
    for env in points(rng, n_points):
        try:
            if any(evaluate(d, env, FUNCS) == 0 for d in obls):
                continue
        except ZeroDivisionError:
            continue  # a divisor inside a divisor vanished: also an obligation
        try:
            a, b = evaluate(lhs, env, FUNCS), evaluate(rhs, env, FUNCS)
        except ZeroDivisionError:
            if result.rule == "ring":
                continue
            testcase.fail(f"obligations hold but a side is undefined at {env}:\n"
                          f"  {show(lhs)}\n  {show(rhs)}\n{result}")
        if result.holds:
            testcase.assertEqual(a, b, f"false 'holds' at {env}:\n"
                                 f"  {show(lhs)}\n  {show(rhs)}\n{result}")


class Properties(unittest.TestCase):
    N = 400

    def test_printer_round_trips(self):
        rng = random.Random(1)
        for _ in range(self.N):
            t = random_term(rng, 4)
            back = parse(show(t))
            for env in points(rng, 3):
                try:
                    v = evaluate(t, env, FUNCS)
                except ZeroDivisionError:
                    continue
                self.assertEqual(evaluate(back, env, FUNCS), v, show(t))

    def test_field_proves_disguised_equalities_soundly(self):
        rng = random.Random(2)
        for _ in range(self.N):
            t = random_term(rng, 3)
            t2 = disguised(rng, t)
            try:
                r = field(t, t2)
            except Refused:
                continue
            self.assertTrue(r.holds, f"{show(t)}  vs  {show(t2)}\n{r}")
            check_sound(self, r, t, t2, rng)

    def test_field_never_proves_t_equals_t_plus_one(self):
        rng = random.Random(3)
        for _ in range(self.N):
            t = random_term(rng, 3)
            try:
                r = field(t, ("add", t, ONE_))
            except Refused:
                continue
            self.assertFalse(r.holds, show(t))

    def test_field_verdicts_on_unrelated_pairs_are_sound(self):
        rng = random.Random(4)
        held = 0
        for _ in range(self.N):
            a, b = random_term(rng, 3), random_term(rng, 3)
            try:
                r = field(a, b)
            except Refused:
                continue
            held += r.holds
            check_sound(self, r, a, b, rng, n_points=4)
        # Random pairs coincide only by accident — mostly both constant.
        self.assertLess(held, self.N // 4)

    def test_ring_implies_field_and_is_sound(self):
        rng = random.Random(5)
        for _ in range(self.N):
            t = random_term(rng, 3)
            t2 = commuted(rng, t)
            try:
                r = ring(t, t2)
            except Refused:
                continue
            self.assertTrue(r.holds, f"{show(t)}  vs  {show(t2)}")
            self.assertTrue(field(t, t2).holds)
            check_sound(self, r, t, t2, rng, n_points=4)

    def test_expansion(self):
        rng = random.Random(6)
        for _ in range(self.N // 4):
            a, b = random_term(rng, 2), random_term(rng, 2)
            lhs = ("pow", ("add", a, b), 2)
            rhs = ("add", ("add", ("pow", a, 2),
                           ("mul", ("num", Fraction(2)), ("mul", a, b))),
                   ("pow", b, 2))
            try:
                r = field(lhs, rhs)
            except Refused:
                continue
            self.assertTrue(r.holds, f"{show(a)} ; {show(b)}")
            check_sound(self, r, lhs, rhs, rng, n_points=4)


if __name__ == "__main__":
    unittest.main()
