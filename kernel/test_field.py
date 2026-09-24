"""Tests for ring, field, norm_num and the residual renderer.

Run: python3 -m unittest -v test_field (in kernel/), or python3 test_field.py.

Ported from spike/ring/test_field.py to terms.py's nodes and field.py's
interface: a check returns Checked(divisors) or raises NotEqual, divisors
are Terms, and refusals are asserted by code. Four kinds of test:

- The worked cases are DESIGN.md's examples and the checks P1 runs, with
  deriv's outputs written out as p1_expected's DERIV gives them (kernel
  deriv is tested elsewhere).
- The refusals are the fragment's edges, E25 among them.
- The property tests are the ones that matter. `field` is the component
  whose bug is a false `Proved` (§17), so its verdicts are checked against
  exact rational evaluation, which shares no code with the normaliser. Any
  rational function standing in for an opaque atom is a model of ℚ[atoms],
  so that evaluation is an honest oracle.
- The planted bugs are the spike README's four, plus one in fact
  reduction, applied as test-only patches. Each must make the property
  suite fail, or the suite is not testing what it claims.
"""

import math
import random
import sys
import unittest
from fractions import Fraction
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

import field as FD  # noqa: E402
import residual  # noqa: E402
from terms import (Add, App, Call, Const, Deriv, Div, Integral, MVar, Mul,  # noqa: E402
                   Neg, Num, Pow, RPow, Refused, Var, lit, parse_judgement,
                   parse_term, show, trees)

SIG = {"f": 1, "h": 2}


def T(s):
    return parse_term(s, SIG)


def decide(rule, lhs, rhs, facts=()):
    """(holds, divisors, residual) for the named rule, strings or Terms."""
    lhs, rhs = (T(x) if isinstance(x, str) else x for x in (lhs, rhs))
    facts = [tuple(T(x) if isinstance(x, str) else x for x in f)
             for f in facts]
    try:
        r = FD.ring(lhs, rhs) if rule == "ring" else FD.field(lhs, rhs, facts)
    except FD.NotEqual as e:
        return False, None, e.residual
    return True, r.divisors, None


def holds(rule, lhs, rhs, facts=()):
    return decide(rule, lhs, rhs, facts)[0]


def divisors(lhs, rhs, facts=()):
    ok, ds, _ = decide("field", lhs, rhs, facts)
    assert ok, "expected field to hold"
    return set(ds)


def terms(*ss):
    return {T(s) for s in ss}


# deriv's outputs, exactly as p1_expected's DERIV states them
D_P1_1 = ("0*sin t + 2*(cos t * 1)"
          " + (0*(2*t*cos t) + (-1)*((0*t + 2*1)*cos t"
          " + 2*t*(-sin t * 1)))")
D_P1_1_FALLBACK = ("0*sin(sqrt x) + 2*(cos(sqrt x)*(1/(2*sqrt x)))"
                   " + (0*(2*sqrt x * cos(sqrt x))"
                   " + (-1)*((0*sqrt x + 2*(1/(2*sqrt x)))*cos(sqrt x)"
                   " + 2*sqrt x * (-sin(sqrt x)*(1/(2*sqrt x)))))")
D_P1_2 = ("0*ln(1 + x) + (1/3)*((0 + 1)/(1 + x))"
          " + (0*((1/6)*ln(x^2 - x + 1))"
          " + (-1)*(0*ln(x^2 - x + 1)"
          " + (1/6)*((2*x^1*1 + (0*x + (-1)*1) + 0)/(x^2 - x + 1))))"
          " + (0*atan((2*x - 1)/sqrt 3)"
          " + (1/sqrt 3)*(((0*x + 2*1 + 0)*(1/sqrt 3) + (2*x - 1)*0)"
          "/(1 + ((2*x - 1)/sqrt 3)^2)))")
D_W1 = ("cos t * 1 + (0*(t*cos t)"
        " + (-1)*(1*cos t + t*(-sin t * 1)))")
# W2's F has 1/3 for 1/6. Any correct derivative will do, since the
# residual is compared by value.
D_W2 = ("(1/3)*(1/(1 + x)) - (1/3)*((2*x - 1)/(x^2 - x + 1))"
        " + (1/sqrt 3)*((2/sqrt 3)/(1 + ((2*x - 1)/sqrt 3)^2))")
P1_2_F_RHS = "1/(1 + x^3)"
SQRT3_FACT = ("(sqrt 3)^2", "3")
BEFORE_CLOSE = ("(1/3)*ln(1 + 1) - (1/6)*0 + (1/sqrt 3)*(pi/6)"
                " - ((1/3)*0 - (1/6)*0 + (1/sqrt 3)*(-(pi/6)))")
ANSWER = "(1/3)*ln 2 + pi/(3*sqrt 3)"
ANSWER_ALT = "(1/3)*ln 2 + pi*sqrt 3 / 9"


def subterms(t):
    yield t
    for name in ("a", "b", "base", "exp", "arg", "body"):
        if hasattr(t, name) and not isinstance(getattr(t, name), (int, str)):
            yield from subterms(getattr(t, name))
    for a in getattr(t, "args", ()):
        yield from subterms(a)


class Ring(unittest.TestCase):
    def test_commutative_ring_facts(self):
        self.assertTrue(holds("ring", "sin x + cos x", "cos x + sin x"))
        self.assertTrue(holds("ring", "(x + 1)^2", "x^2 + 2*x + 1"))
        self.assertTrue(holds("ring", "(a - b)*(a + b)", "a^2 - b^2"))
        self.assertTrue(holds("ring", "x/3 + x/6", "x/2"))

    def test_ring_owes_nothing(self):
        self.assertEqual(FD.ring(T("x/3 + 1/y"), T("1/y + x/3")).divisors, ())

    def test_atoms_are_opaque(self):
        # §6.2: sin²x + cos²x ≐ 1 needs `pyth`; ring must not know it.
        self.assertFalse(holds("ring", "(sin x)^2 + (cos x)^2", "1"))

    def test_atoms_identified_up_to_their_arguments(self):
        self.assertTrue(holds("ring", "sin(x + 1) - sin(1 + x)", "0"))
        self.assertTrue(holds("ring", "f(2*x) * h(x, y)", "h(x, y) * f(x + x)"))
        self.assertFalse(holds("ring", "f(x)", "f(y)"))
        self.assertTrue(holds("ring", "ln(1 + 1)", "ln 2"))

    def test_division_is_not_a_ring_operation(self):
        # STAGE0.md gap 2: m·(1/m) cancels only in a field.
        ok, _, r = decide("ring", "m * (1/m)", "1")
        self.assertFalse(ok)
        self.assertTrue(holds("ring", residual.residual_term(r), "m*(1/m) - 1"))
        self.assertFalse(holds("ring", "1/x^2", "(1/x)^2"))

    def test_p1_1_checks(self):
        # P1.1 s2 (deriv; ring) and s6 (close by ring)
        self.assertTrue(holds("ring", D_P1_1, "sin t * (2*t)"))
        self.assertTrue(holds("ring", "2*1 - 2*(pi/2)*0 - (2*0 - 2*0*cos 0)",
                              "2"))

    def test_w1_residual_names_the_missing_term(self):
        # §11.1's factor of 2: F := sin t − t cos t is short by t·sin t.
        ok, _, r = decide("ring", D_W1, "sin t * (2*t)")
        self.assertFalse(ok)
        rt = residual.residual_term(r)
        self.assertEqual(show(rt), "-t*sin t")
        self.assertTrue(holds("ring", rt, "-t*sin t"))


class Matcher(unittest.TestCase):
    """ring_equal is REWRITE_RULE step 3's test; the cases are P1's."""

    def test_accepts(self):
        for a, b in [("(2*1 - 1)/sqrt 3", "1/sqrt 3"),
                     ("(2*0 - 1)/sqrt 3", "-(1/sqrt 3)"),
                     ("(pi/2)^2", "pi^2/4"), ("0^2", "0"),
                     ("(t - t + 1)^2", "1"), ("1/x - 1/x + 1", "1"),
                     ("x*(1/x) - x*(1/x) + 1", "1"), ("1 + 1", "2")]:
            self.assertTrue(FD.ring_equal(T(a), T(b)), (a, b))

    def test_refuses(self):
        for a, b in [("(2*0 - 1)/sqrt 3", "1/sqrt 3"), ("x/x", "1"),
                     ("1/x^2", "(1/x)^2")]:
            self.assertFalse(FD.ring_equal(T(a), T(b)), (a, b))

    def test_ring_is_zero(self):
        self.assertTrue(FD.ring_is_zero(T("x - x")))
        self.assertTrue(FD.ring_is_zero(T("1/x - 1/x")))
        self.assertFalse(FD.ring_is_zero(T("x/x - 1")))
        with self.assertRaises(Refused) as cm:
            FD.ring_is_zero(T("1/(x - x)"))
        self.assertEqual(cm.exception.code, "divisor-normalises-to-zero")

    def test_ring_polys_share_atoms(self):
        (p, q), atoms = FD.ring_polys([T("pi/2"), T("2*pi + 1/x")])
        self.assertEqual(atoms, (Const("pi"), Var("x"), Div(Num(1), Var("x"))))
        self.assertEqual(p, {((0, 1),): Fraction(1, 2)})
        self.assertEqual(q, {((0, 1),): 2, ((2, 1),): 1})


class Field(unittest.TestCase):
    def test_cancelling_owes_the_divisor(self):
        self.assertEqual(divisors("m * (1/m)", "1"), terms("m"))

    def test_both_spellings_owe_the_same(self):
        # §5.1: x^(-1) and 1/x must not differ in what they owe.
        self.assertEqual(divisors("x * x^(-1)", "1"), terms("x"))
        self.assertEqual(divisors("x * (1/x)", "1"), terms("x"))

    def test_nested_divisors_each_owe(self):
        self.assertEqual(divisors("1/(1 + 1/x)", "x/(x + 1)"),
                         terms("1 + 1/x", "x", "x + 1"))

    def test_divisors_inside_atoms_owe(self):
        self.assertEqual(divisors("sin(x/x)", "sin(x/x)"), terms("x"))

    def test_divisors_are_first_seen_and_deduplicated(self):
        _, ds, _ = decide("field", "1/y + 1/x + 1/y", "2/y + 1/x")
        self.assertEqual(ds, (Var("y"), Var("x")))

    def test_literal_divisors_are_returned(self):
        # The kernel's norm_num discharges them (E7).
        self.assertEqual(divisors("x/3", "(1/3)*x"), terms("3"))

    def test_common_denominator_is_not_squared(self):
        ok, _, r = decide("field", "1/(x+1) + 1/(x+1) + 1", "2/(1+x)")
        self.assertFalse(ok)
        self.assertEqual(sum(e for _, e in r.den), 1)

    def test_telescoping_partial_fractions(self):
        lhs = " + ".join(f"1/((x + {k})*(x + {k + 1}))" for k in range(1, 9))
        self.assertTrue(holds("field", lhs, "1/(x + 1) - 1/(x + 9)"))
        self.assertFalse(holds("field", lhs, "1/(x + 1) - 1/(x + 10)"))

    def test_linear_drag_ode(self):
        # §6.5 / STAGE0.md gap 2: m·v' = −b·v, v = v0·exp(−b·t/m).
        dv = "v0*(exp(-b*t/m)*(-b/m))"
        lhs, rhs = f"m*({dv})", "-b*(v0*exp(-b*t/m))"
        self.assertFalse(holds("ring", lhs, rhs))
        self.assertIn(Var("m"), divisors(lhs, rhs))

    def test_p1_1_fallback_check(self):
        # P1.1-fallback s1: field owes the term 2*sqrt x, not split.
        self.assertEqual(divisors(D_P1_1_FALLBACK, "sin(sqrt x)"),
                         terms("2*sqrt x"))


class Facts(unittest.TestCase):
    def test_flagship_needs_the_fact(self):
        # §11.2, P1.2 s2: with sqrt 3 opaque, D[x]F ≐ 1/(1+x³) is false in
        # ℚ(x, s). The divisors are p1_expected's field_div keys at s2.
        self.assertFalse(holds("field", D_P1_2, P1_2_F_RHS))
        self.assertEqual(divisors(D_P1_2, P1_2_F_RHS, [SQRT3_FACT]), terms(
            "3", "6", "1 + x", "x^2 - x + 1", "sqrt 3",
            "1 + ((2*x - 1)/sqrt 3)^2", "1 + x^3"))

    def test_w3_residual_matches_the_design(self):
        # §11.2 states the residual as (3/2 − s²/2)/(s²x² − s²x + s² + 4x⁴
        # − 8x³ + 9x² − 5x + 1). Compared by field without the fact (E14).
        ok, _, r = decide("field", D_P1_2, P1_2_F_RHS)
        self.assertFalse(ok)
        rt = residual.residual_term(r)
        for stated in ("(3/2 - (sqrt 3)^2/2)/((sqrt 3)^2*x^2 - (sqrt 3)^2*x"
                       " + (sqrt 3)^2 + 4*x^4 - 8*x^3 + 9*x^2 - 5*x + 1)",
                       "-((sqrt 3)^2 - 3)/(2*(x^2 - x + 1)"
                       "*((sqrt 3)^2 + 4*x^2 - 4*x + 1))"):
            self.assertTrue(holds("field", rt, stated))
        self.assertFalse(holds("field", rt, "0"))

    def test_w2_residual(self):
        ok, _, r = decide("field", D_W2, P1_2_F_RHS, [SQRT3_FACT])
        self.assertFalse(ok)
        rt = residual.residual_term(r)
        self.assertTrue(holds("field", rt, "-(2*x - 1)/(6*(x^2 - x + 1))",
                              [SQRT3_FACT]))
        self.assertFalse(holds("field", rt, "0", [SQRT3_FACT]))

    def test_rewriting_before_field_is_not_enough(self):
        # §11.2's first script said `deriv; rewrite sqrt_sq_val; field`.
        # There is no (sqrt 3)^2 in deriv's output for a rewrite to act on:
        # s² appears only once field has normalised ((2x − 1)/sqrt 3)^2.
        self.assertNotIn(T("(sqrt 3)^2"), set(subterms(T(D_P1_2))))

    def test_p1_2_close(self):
        # s9: no fact needed, and 3*sqrt 3 is owed (§11.2)
        self.assertEqual(divisors(BEFORE_CLOSE, ANSWER),
                         terms("3", "6", "sqrt 3", "3*sqrt 3"))

    def test_p1_2_alt_close_and_w4(self):
        # §8.7: π√3/9 against π/(3√3) only with the fact
        ok, _, r = decide("field", BEFORE_CLOSE, ANSWER_ALT)
        self.assertFalse(ok)
        rt = residual.residual_term(r)
        self.assertTrue(holds("field", rt, "pi*(3 - (sqrt 3)^2)/(9*sqrt 3)"))
        self.assertFalse(holds("field", rt, "0"))
        self.assertEqual(divisors(BEFORE_CLOSE, ANSWER_ALT, [SQRT3_FACT]),
                         terms("3", "6", "9", "sqrt 3"))

    def test_surd_answers_compare_equal_only_with_the_fact(self):
        self.assertFalse(holds("field", "pi*sqrt 3/9", "pi/(3*sqrt 3)"))
        self.assertIn(T("3*sqrt 3"), divisors("pi*sqrt 3/9", "pi/(3*sqrt 3)",
                                              [SQRT3_FACT]))

    def test_fact_with_a_rational_right_side(self):
        # Unit 00 P4, quadratic drag: m·v' = m·g − k·v², v = V·tanh(g·t/V)
        # with V = sqrt(m·g/k). Needs V² = m·g/k, a fact whose right side
        # divides, and so owes k # 0 itself.
        V = "sqrt(m*g/k)"
        th = f"tanh(g*t/{V})"
        dv = f"{V}*((1 - ({th})^2)*(g/{V}))"
        lhs, rhs = f"m*({dv})", f"m*g - k*({V}*{th})^2"
        self.assertFalse(holds("field", lhs, rhs))
        ds = divisors(lhs, rhs, [(f"({V})^2", "m*g/k")])
        self.assertIn(Var("k"), ds)
        self.assertIn(T(V), ds)

    def test_fact_divisors_are_owed(self):
        # The fact is input, and reduce's Q ≠ 0 rests on its divisors.
        self.assertEqual(divisors("(sqrt y)^2 * x", "x/(1/y)",
                                  [("(sqrt y)^2", "1/(1/y)")]),
                         terms("1/y", "y"))

    def test_higher_powers_reduce(self):
        self.assertTrue(holds("field", "(sqrt 2)^5", "4*sqrt 2",
                              [("(sqrt 2)^2", "2")]))
        self.assertFalse(holds("field", "(sqrt 2)^5", "2*sqrt 2",
                               [("(sqrt 2)^2", "2")]))


class Refusals(unittest.TestCase):
    def assertRefused(self, code, fn, *args):
        with self.assertRaises(Refused) as cm:
            fn(*args)
        self.assertEqual(cm.exception.code, code)

    def test_division_by_zero(self):
        for rule in (FD.ring, FD.field):
            for d in ("1/0", "1/(x - x)", "x^(-2) * (x - x)^(-1)",
                      "sin(1/(1 - 1))"):
                self.assertRefused("divisor-normalises-to-zero", rule,
                                   T(d), T("1"))

    def test_field_zero_divisor_ring_cannot_see(self):
        # E25 and BAD_MOVES field_zero_divisor: 1 == 1/(x/x - 1)
        self.assertFalse(holds("ring", "1", "1/(x/x - 1)"))
        self.assertRefused("divisor-normalises-to-zero", FD.field,
                           T("1"), T("1/(x/x - 1)"))
        # tested as met, so an unequal pair is refused, not NotEqual
        self.assertRefused("divisor-normalises-to-zero", FD.field,
                           T("2"), T("1/(x/x - 1)"))

    def test_trees_are_not_atoms(self):
        # p1_expected E26 (b): D and Int have no definedness condition the
        # kernel can state, so no normaliser reads one as an atom. Each pair
        # below was decided before E26 (the first three as atoms), and each
        # is now refused, whichever side holds the node, and inside an atom
        # argument too. BAD_MOVES close_D_goal_scope_passes, ring_refuses_*.
        for rule in ("ring", "field"):
            for lhs, rhs in (("D[x] x^2", "2*x"), ("D[x] x^2 + 1", "1 + D[x] x^2"),
                             ("D[x](x + 0)", "D[x] x"),
                             ("Int[t = 0 .. 1] 1/t", "Int[t = 0 .. 1] 1/t"),
                             ("(Int[x = 0 .. oo] 1) - (Int[x = 0 .. oo] 1)", "0"),
                             ("0", "sin(D[x](abs x) - D[x](abs x))")):
                with self.subTest(rule=rule, lhs=lhs, rhs=rhs):
                    self.assertRefused("Int-or-D-not-normalisable", decide,
                                       rule, lhs, rhs)
        # and in a fact, which field normalises too
        self.assertRefused("Int-or-D-not-normalisable", FD.field, T("x"), T("x"),
                           [(T("(sqrt(Int[t = 0 .. 1] t))^2"), T("Int[t = 0 .. 1] t"))])
        for fn in (FD.ring_is_zero, lambda t: FD.ring_equal(t, t),
                   lambda t: FD.ring_polys([t])):
            self.assertRefused("Int-or-D-not-normalisable", fn,
                               T("(Int[x = 0 .. oo] 1) - (Int[x = 0 .. oo] 1)"))
            self.assertRefused("Int-or-D-not-normalisable", fn, T("1/(D[x](abs x))"))

    def test_field_refuses_trees_holding_zero_divisors(self):
        # Before E26 (b) these were D and Int atoms whose inner divisors
        # field tested (E25). Now no side holding one is normalised at all,
        # so each is refused, and never decided or given a divisor list.
        for lhs in ("(Int[y = 0 .. 1] 1/(y/y - 1)) - (Int[y = 0 .. 1] 1/(y/y - 1)) + 1",
                    "D[x](1/(x/x - 1)) - D[x](1/(x/x - 1)) + 1",
                    "(Int[t = 0 .. 1/(x/x - 1)] t) - (Int[t = 0 .. 1/(x/x - 1)] t) + 1",
                    "Int[t = 0 .. 1/0] t",
                    "(Int[t = 1 .. 2] 1/t) + 1/x"):
            self.assertRefused("Int-or-D-not-normalisable", FD.field,
                               T(lhs), T("1"))

    def test_malformed_facts(self):
        for facts in ([("2*(sqrt 3)^2", "6")],
                      [("(sqrt 3)^2", "sqrt 3 + 1")],
                      [("(sqrt 3)^2", "3"), ("(sqrt 3)^4", "9")],
                      [("(sqrt 3)^2", "1/sqrt 3")],
                      [("1/sqrt 3", "3")]):
            self.assertRefused("field-fact-shape", FD.field, T("x"), T("x"),
                               [tuple(map(T, f)) for f in facts])

    def test_what_never_reaches_here(self):
        # The kernel refuses ?A first; meeting one is a kernel bug.
        with self.assertRaises(TypeError):
            FD.field(MVar("A"), Num(1))
        with self.assertRaises(TypeError):
            FD.ring_equal(Var("x"), "x")


class NormNum(unittest.TestCase):
    def test_decides_literals(self):
        J = parse_judgement
        for s, v in [("2 # 0", True), ("3 >= 0", True), ("0 >= 0", True),
                     ("0 # 0", False), ("1/2 < 1/3", False),
                     ("2^(-1) == 1/2", True), ("-(1/3) <= -1/4", True),
                     ("(1 - 1)*5 > 0", False), ("1 + 1 == 2", True),
                     # each comparison at its boundary, so no _OPS entry
                     # can be swapped for a neighbour unseen
                     ("1 <= 1", True), ("1 < 1", False), ("1 == 2", False),
                     ("1 >= 1", True), ("1 > 1", False)]:
            self.assertIs(FD.norm_num(J(s)), v, s)

    def test_declines_the_rest(self):
        J = parse_judgement
        for s in ("0 <= pi/2", "x # 0", "1 + x^3 # 0 @ x in [0, 1]",
                  "sqrt 3 # 0", "1/0 # 0", "0^(-1) > 0", "1 in C^0(true)",
                  "x in C^1((0, 1))"):
            self.assertIsNone(FD.norm_num(J(s)), s)

    def test_refuses_trees_in_prop_and_domain(self):
        # E7 with E26 (b): refused, not decided and not declined, whether
        # the node is in the proposition or the domain, closed or not.
        J = parse_judgement
        for s in ("(Int[x = 0 .. oo] 1) - (Int[x = 0 .. oo] 1) >= 0",
                  "D[x] x^2 > 0", "(Int[t = 0 .. x] t) >= 0",
                  "x > 0 @ x > (Int[t = 0 .. oo] 1) - (Int[t = 0 .. oo] 1)",
                  "x > 0 @ x > D[y] y^2", "0 # 0 @ x in [0, (Int[t = 0 .. 1] t)]"):
            j = J(s)
            with self.assertRaises(Refused, msg=s) as cm:
                FD.norm_num(j)
            self.assertEqual(cm.exception.code, "Int-or-D-not-normalisable", s)

    def test_hypothesis_gate_is_its_own_seam(self):
        # E26 (b) at install: hypothesis_tree refuses on its own, and
        # norm_num's check does not go through it, so weakening one seam
        # leaves the other in force.
        for s in ("Int[t = 0 .. oo] 1", "D[x] x^2"):
            with self.assertRaises(Refused, msg=s) as cm:
                FD.hypothesis_tree(T(s))
            self.assertEqual(cm.exception.code, "Int-or-D-not-normalisable", s)
        j = parse_judgement("x > 0 @ x > D[y] y^2")
        with mock.patch.object(FD, "hypothesis_tree", lambda node: None):
            with self.assertRaises(Refused):
                FD.norm_num(j)

    def test_rational_value_inverts_lit(self):
        rng = random.Random(7)
        for _ in range(200):
            q = Fraction(rng.randint(-50, 50), rng.randint(1, 30))
            self.assertEqual(FD.rational_value(lit(q)), q)
        self.assertIsNone(FD.rational_value(T("1/(2 - 2)")))
        self.assertIsNone(FD.rational_value(T("x")))


# ------------------------------------------------------------ properties

def _f(v):
    return 3 * v * v - v + Fraction(7, 2)


# Opaque atoms, modelled by rational functions with no rational pole.
# random_term still draws Deriv nodes, which ring and field refuse
# (p1_expected E26 (b)); `attempt` fails the test if either decides a pair
# holding one. "tree" models a Deriv only for the printer and the residual.
FUNCS = {"f": _f, "h": lambda u, v: u * v - 2 * v + 1,
         "sin": lambda v: v / (v * v + 1), "exp": lambda v: 2 - v,
         "rpow": lambda b, e: b * b + e,
         "tree": lambda t: Fraction(len(show(t)) % 7 + 1)}


def evaluate(t, env, funcs=FUNCS):
    """Exact value of t. Raises ZeroDivisionError where a divisor, or a
    negatively powered base, vanishes."""
    k = type(t)
    if k is Num:
        return Fraction(t.n)
    if k is Var or k is Const:
        return env[t.name]
    if k is Neg:
        return -evaluate(t.a, env, funcs)
    if k in (Add, Mul, Div):
        a, b = evaluate(t.a, env, funcs), evaluate(t.b, env, funcs)
        return a + b if k is Add else a * b if k is Mul else a / b
    if k is Pow:
        return evaluate(t.base, env, funcs) ** t.n
    if k is RPow:
        return funcs["rpow"](evaluate(t.base, env, funcs),
                             evaluate(t.exp, env, funcs))
    if k is App:
        return funcs[t.fn](evaluate(t.arg, env, funcs))
    if k is Call:
        return funcs[t.fn](*(evaluate(a, env, funcs) for a in t.args))
    if k in (Deriv, Integral):
        return funcs["tree"](t)
    raise ValueError(f"cannot evaluate {t!r}")


def random_term(rng, depth):
    if depth == 0 or rng.random() < 0.25:
        r = rng.random()
        if r < 0.5:
            return Var(rng.choice("xyz"))
        if r < 0.8:
            return lit(Fraction(rng.randint(-3, 4), rng.choice([1, 1, 2, 3])))
        if r < 0.9:
            return Const("pi")
        return Call("f", (random_term(rng, 1),))
    k = rng.choice(["add", "add", "mul", "mul", "neg", "div", "pow", "f",
                    "h", "app", "rpow", "deriv"])
    sub = lambda: random_term(rng, depth - 1)  # noqa: E731
    if k in ("add", "mul", "div"):
        return {"add": Add, "mul": Mul, "div": Div}[k](sub(), sub())
    if k == "neg":
        return Neg(sub())
    if k == "pow":
        return Pow(sub(), rng.randint(-2, 3))
    if k == "f":
        return Call("f", (sub(),))
    if k == "h":
        return Call("h", (sub(), sub()))
    if k == "app":
        return App(rng.choice(("sin", "exp")), sub())
    if k == "rpow":
        return RPow(sub(), Var(rng.choice("xyz")))
    return Deriv("x", sub())


def commuted(rng, t):
    """t with the children of + and * shuffled at random, all the way down
    to, but not into, the atoms keyed by their tree."""
    c = lambda u: commuted(rng, u)  # noqa: E731
    k = type(t)
    if k in (Add, Mul):
        a, b = c(t.a), c(t.b)
        return k(b, a) if rng.random() < 0.5 else k(a, b)
    if k is Div:
        return Div(c(t.a), c(t.b))
    if k is Neg:
        return Neg(c(t.a))
    if k is Pow:
        return Pow(c(t.base), t.n)
    if k is RPow:
        return RPow(c(t.base), t.exp)
    if k is App:
        return App(t.fn, c(t.arg))
    if k is Call:
        return Call(t.fn, tuple(map(c, t.args)))
    return t


ONE = Num(1)


def disguised(rng, t):
    """A term equal to t wherever its divisors are nonzero."""
    u = random_term(rng, 2)
    moves = [
        lambda: Mul(t, Div(u, u)),
        lambda: Add(Add(t, u), Neg(u)),
        lambda: Div(ONE, Div(ONE, t)),
        lambda: Div(Pow(t, 2), t),
        lambda: Mul(Pow(t, -1), Pow(t, 2)),
        lambda: commuted(rng, t),
    ]
    return rng.choice(moves)()


def points(rng, n, names="xyz"):
    for _ in range(n):
        env = {v: Fraction(rng.randint(-7, 7), rng.randint(1, 4)) for v in names}
        env["pi"] = Fraction(rng.randint(1, 30), rng.randint(1, 9))
        yield env


def input_divisors(t):
    """Every divisor in t, as field is specified to collect them."""
    if type(t) in (Deriv, Integral):
        return
    if type(t) is Div:
        yield t.b
    if type(t) is Pow and t.n < 0:
        yield t.base
    for s in _children(t):
        yield from input_divisors(s)


def _children(t):
    for name in ("a", "b", "base", "exp", "arg"):
        if hasattr(t, name):
            yield getattr(t, name)
    yield from getattr(t, "args", ())


def check_sound(tc, rule, ok, divs, lhs, rhs, rng, n_points=12, funcs=FUNCS,
                names="xyz"):
    """Wherever every returned divisor is nonzero, lhs and rhs must be
    defined, and equal if the check held. A NotEqual returns no divisors
    (divs None), so the input's own are used.

    `ring` cancels nothing and so owes nothing; for it the claim is only
    that the sides agree wherever both are defined.
    """
    if divs is None:
        divs = [*input_divisors(lhs), *input_divisors(rhs)]
    for env in points(rng, n_points, names):
        try:
            if any(evaluate(d, env, funcs) == 0 for d in divs):
                continue
        except ZeroDivisionError:
            continue  # a divisor inside a divisor vanished: also owed
        try:
            a, b = evaluate(lhs, env, funcs), evaluate(rhs, env, funcs)
        except ZeroDivisionError:
            if rule == "ring":
                continue
            tc.fail(f"divisors hold but a side is undefined at {env}:\n"
                    f"  {show(lhs)}\n  {show(rhs)}\n  owes {list(map(show, divs))}")
        if ok:
            tc.assertEqual(a, b, f"false check at {env}:\n  {show(lhs)}\n"
                           f"  {show(rhs)}\n  owes {list(map(show, divs))}")


def attempt(rule, lhs, rhs, facts=()):
    """decide(), or None when the rule refuses. A rule that decides a pair
    holding a Deriv or Integral node, rather than refusing it, is a failure
    (E26 (b)): such a node is never an atom."""
    try:
        got = decide(rule, lhs, rhs, facts)
    except Refused:
        return None
    held = [t for t in (lhs, rhs, *(x for f in facts for x in f))
            if not isinstance(t, str) and any(trees(t))]
    if held:
        raise AssertionError(f"{rule} decided {show(held[0])}, which holds "
                             "a Deriv or Integral node (E26 (b))")
    return got


class Properties(unittest.TestCase):
    N = 400

    def test_printer_round_trips(self):
        rng = random.Random(1)
        for _ in range(self.N):
            t = random_term(rng, 4)
            self.assertEqual(parse_term(show(t), SIG), t, show(t))

    def test_field_proves_disguised_equalities_soundly(self):
        rng = random.Random(2)
        for _ in range(self.N):
            t = random_term(rng, 3)
            t2 = disguised(rng, t)
            got = attempt("field", t, t2)
            if got is None:
                continue
            ok, divs, _ = got
            self.assertTrue(ok, f"{show(t)}  vs  {show(t2)}")
            check_sound(self, "field", ok, divs, t, t2, rng)

    def test_field_never_proves_t_equals_t_plus_one(self):
        rng = random.Random(3)
        for _ in range(self.N):
            t = random_term(rng, 3)
            got = attempt("field", t, Add(t, ONE))
            if got is not None:
                self.assertFalse(got[0], show(t))

    def test_field_verdicts_on_unrelated_pairs_are_sound(self):
        rng = random.Random(4)
        held = 0
        for _ in range(self.N):
            a, b = random_term(rng, 3), random_term(rng, 3)
            got = attempt("field", a, b)
            if got is None:
                continue
            held += got[0]
            check_sound(self, "field", got[0], got[1], a, b, rng, n_points=4)
        # Random pairs coincide only by accident, mostly both constant.
        self.assertLess(held, self.N // 4)

    def test_field_owes_exactly_its_input_divisors(self):
        # §6.2: every divisor in the input, and nothing else.
        rng = random.Random(8)
        for _ in range(self.N):
            a = random_term(rng, 3)
            try:
                ds = FD.field(a, a).divisors
            except Refused:
                continue
            self.assertEqual(set(ds), set(input_divisors(a)), show(a))
            self.assertEqual(len(ds), len(set(ds)))

    def test_ring_implies_field_and_is_sound(self):
        rng = random.Random(5)
        for _ in range(self.N):
            t = random_term(rng, 3)
            t2 = commuted(rng, t)
            got = attempt("ring", t, t2)
            if got is None:
                continue
            self.assertTrue(got[0], f"{show(t)}  vs  {show(t2)}")
            self.assertEqual(got[1], ())
            self.assertTrue(holds("field", t, t2))
            self.assertTrue(FD.ring_equal(t, t2))
            check_sound(self, "ring", True, (), t, t2, rng, n_points=4)

    def test_expansion(self):
        rng = random.Random(6)
        for _ in range(self.N // 4):
            a, b = random_term(rng, 2), random_term(rng, 2)
            lhs = Pow(Add(a, b), 2)
            rhs = Add(Add(Pow(a, 2), Mul(Num(2), Mul(a, b))), Pow(b, 2))
            got = attempt("field", lhs, rhs)
            if got is None:
                continue
            self.assertTrue(got[0], f"{show(a)} ; {show(b)}")
            check_sound(self, "field", True, got[1], lhs, rhs, rng, n_points=4)

    def test_residual_has_the_value_of_lhs_minus_rhs(self):
        # residual.py is untrusted, but WRONG_ANSWERS rely on its value.
        rng = random.Random(9)
        seen = 0
        for _ in range(self.N):
            a, b = random_term(rng, 3), random_term(rng, 3)
            rule = rng.choice(("ring", "field"))
            got = attempt(rule, a, b)
            if got is None or got[0]:
                continue
            rt = residual.residual_term(got[2])
            divs = list(input_divisors(a)) + list(input_divisors(b))
            for env in points(rng, 4):
                try:
                    if any(evaluate(d, env) == 0 for d in divs):
                        continue
                    want = evaluate(a, env) - evaluate(b, env)
                except ZeroDivisionError:
                    continue
                self.assertEqual(evaluate(rt, env), want,
                                 f"{show(a)}  vs  {show(b)}: {show(rt)}")
                seen += 1
        self.assertGreater(seen, self.N // 2)


# The atom s = sqrt((x/y)^2) with the fact s^2 == (x/y)^2: a right side
# with a non-constant Q, y^2. Modelled by the exact rational square root,
# which exists because the argument is a square.
W = Pow(Div(Var("x"), Var("y")), 2)
S = App("sqrt", W)
S_FACT = [(Pow(S, 2), W)]


def _exact_sqrt(v):
    n, d = math.isqrt(v.numerator), math.isqrt(v.denominator)
    assert Fraction(n, d) ** 2 == v, v
    return Fraction(n, d)


FACT_FUNCS = dict(FUNCS, sqrt=_exact_sqrt)


def fact_term(rng, depth):
    if depth == 0 or rng.random() < 0.3:
        r = rng.random()
        if r < 0.4:
            return S
        if r < 0.75:
            return Var(rng.choice("xy"))
        return lit(Fraction(rng.randint(-3, 4), rng.choice([1, 2])))
    k = rng.choice(["add", "mul", "mul", "neg", "div", "pow"])
    sub = lambda: fact_term(rng, depth - 1)  # noqa: E731
    if k == "add":
        return Add(sub(), sub())
    if k == "mul":
        return Mul(sub(), sub())
    if k == "neg":
        return Neg(sub())
    if k == "div":
        return Div(sub(), sub())
    return Pow(sub(), rng.randint(-2, 4))


class FactProperties(unittest.TestCase):
    """field modulo a fact, against evaluation in a model of the fact."""
    N = 300

    def check(self, lhs, rhs, rng, expect=None):
        got = attempt("field", lhs, rhs, S_FACT)
        if got is None:
            return
        if expect is not None:
            self.assertEqual(got[0], expect, f"{show(lhs)}  vs  {show(rhs)}")
        check_sound(self, "field", got[0], got[1], lhs, rhs, rng,
                    n_points=6, funcs=FACT_FUNCS, names="xy")

    def test_the_fact_is_used(self):
        rng = random.Random(10)
        for _ in range(self.N):
            u, j = fact_term(rng, 2), rng.randint(1, 3)
            self.check(Mul(Pow(S, 2 * j), u), Mul(Pow(W, j), u), rng, True)
            self.check(Mul(Pow(S, 2 * j + 1), u), Mul(Mul(Pow(W, j), S), u),
                       rng, True)

    def test_near_misses_are_sound(self):
        # Dropping Q would make s^2 * u equal x^2 * u.
        rng = random.Random(11)
        for _ in range(self.N):
            u = fact_term(rng, 2)
            self.check(Mul(Pow(S, 2), u), Mul(Pow(Var("x"), 2), u), rng)
            self.check(Pow(S, 3), Mul(Pow(Var("x"), 2), S), rng)

    def test_random_pairs_are_sound(self):
        rng = random.Random(12)
        for _ in range(self.N):
            self.check(fact_term(rng, 3), fact_term(rng, 3), rng)


# ------------------------------------------------------------ planted bugs
#
# Each is a patch on _Normaliser applied in this process only, for the
# length of one suite run. They are the spike README's four, plus a fact
# reduction that forgets its Q. The suite must fail under every one.

_norm, _invert, _add = (FD._Normaliser.norm, FD._Normaliser.invert,
                        FD._Normaliser.add)
_reduce = FD._Normaliser.reduce  # a plain function, through the class


def _no_divisor(self, d):
    pass  # an unrecorded divisor


def _neg_power_wrong_divisor(self, t):
    if type(t) is Pow and t.n < 0:  # charges the exponent, not the base
        return self.pow(self.invert(self.norm(t.base), lit(-t.n)), -t.n)
    return _norm(self, t)


def _inverse_drops_content(self, a, d):
    r = _invert(self, a, d)
    if self.is_field and r.den:
        c, _ = FD.P.content_normal(a.num)
        return FD._Frac(FD.P.scale(r.num, c), r.den)  # undo the 1/c
    return r


def _lcm_ignores_second(self, a, b):
    if a.num and b.num and a.den != b.den:
        return FD._Frac(FD.P.add(a.num, FD.P.mul(b.num, self.expand(a.den))),
                        dict(a.den))
    return _add(self, a, b)


def _reduce_drops_q(n, i, k, p_num, q):
    return _reduce(n, i, k, p_num, FD.P.const(1))


PLANTED = {
    "unrecorded_divisor": ("divisor", _no_divisor),
    "neg_power_wrong_divisor": ("norm", _neg_power_wrong_divisor),
    "inverse_drops_content": ("invert", _inverse_drops_content),
    "lcm_ignores_second_denominator": ("add", _lcm_ignores_second),
    "reduce_drops_q": ("reduce", staticmethod(_reduce_drops_q)),
}


def run_suite():
    """Failures plus errors of the property suites, run quietly."""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite([loader.loadTestsFromTestCase(c)
                                for c in (Properties, FactProperties)])
    result = unittest.TestResult()
    suite.run(result)
    return len(result.failures) + len(result.errors)


class PlantedBugs(unittest.TestCase):
    def test_control(self):
        self.assertEqual(run_suite(), 0)

    def test_each_bug_is_caught(self):
        for name, (attr, bad) in PLANTED.items():
            with self.subTest(bug=name), mock.patch.object(
                    FD._Normaliser, attr, bad):
                self.assertGreater(run_suite(), 0, f"{name} went unnoticed")
        self.assertIs(FD._Normaliser.norm, _norm)  # patches undone


if __name__ == "__main__":
    unittest.main()
