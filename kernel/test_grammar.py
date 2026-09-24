"""Tests for D13 and R4's reading of "the judgement's free variables", for
D12's `# 0`, and for subst's binder cases (GRAMMAR.md §5), which no P1 move
reaches: its refusal under D and its capture-avoiding Int rename.

Run: python3 -m unittest -v test_grammar (in kernel/).

GRAMMAR.md defines fv only for terms (§5). D13 counts a judgement's free
variables without the bare intervals' own variable, which the parser cannot
see, and R4 cites D13, so both count the same set: fv of the sides, the
constraint items and every interval's endpoints, never an interval's own
variable. These are the cases the review of that reading named. They sit
outside ROUND_TRIP_GRAMMAR because none of them is a P1 datum.
"""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from terms import (Interval, NonZero, Num, ParseError, Refused,  # noqa: E402
                   Var, parse_judgement, parse_term, show, subst)


class D13R4(unittest.TestCase):
    def round_trip(self, s):
        j = parse_judgement(s)
        self.assertEqual(show(j), s)
        self.assertEqual(parse_judgement(show(j)), j)
        return j

    def test_closed_reg_names_its_interval(self):
        # S = {}, so the interval is named, and it round-trips
        j = self.round_trip("sqrt 3 in C^0(t in [0, pi/2])")
        self.assertEqual(j.dom[0].var, "t")

    def test_closed_relation_names_its_interval(self):
        self.round_trip("1 > 0 @ t in [0, 1]")

    def test_bare_beside_named(self):
        # S = {x}: the bare interval is x's and prints bare again; y's
        # interval is named because its variable is not in S
        j = self.round_trip("x > 0 @ [0, 1], y in [0, 1]")
        self.assertEqual(j.dom, (Interval("x", Num(0), True, Num(1), True),
                                 Interval("y", Num(0), True, Num(1), True)))
        self.assertEqual(j.lhs, Var("x"))

    def test_two_free_variables_stay_named(self):
        self.round_trip("x + y > 0 @ x in [0, 1]")

    def test_bare_interval_with_no_free_variable_is_refused(self):
        with self.assertRaises(ParseError) as cm:
            parse_judgement("1 > 0 @ [0, 1]")
        self.assertEqual(cm.exception.code, "D13-unnamed-interval")


class HashZero(unittest.TestCase):
    """GRAMMAR.md §4: `expr "#" "0"`, where "0" is the NAT 0 itself: one
    token, so a group that parses to 0 is not it, and 00 (NAT 0 under §3's
    [0-9]+) is."""

    def test_parenthesised_zero_is_refused(self):
        with self.assertRaises(ParseError) as cm:
            parse_judgement("a # (0)")
        self.assertEqual(cm.exception.code, "hash-nonzero")

    def test_padded_zero_is_the_nat_zero(self):
        self.assertEqual(parse_judgement("a # 00"), NonZero(Var("a")))


class Subst(unittest.TestCase):
    """GRAMMAR.md §5's rule for D, with its three SymPy-checked cases, and
    the Int rename (p1_expected step 1: 'the substitution is
    capture-avoiding'). ftc's F[x := b] only reaches the unchanged case, so
    the proof run cannot catch a bug in the others."""

    def sub(self, t, **m):
        return subst(parse_term(t), {k: parse_term(v) for k, v in m.items()})

    def test_d_cases_are_refused(self):
        for t, m in (("D[x] x^2", {"x": "1"}), ("D[x](x*y)", {"y": "x"}),
                     ("D[x](x*z)", {"x": "z"})):
            with self.subTest(t=t, m=m), self.assertRaises(Refused) as cm:
                self.sub(t, **m)
            self.assertEqual(cm.exception.code, "subst-under-D")

    def test_d_passes_through(self):
        self.assertEqual(self.sub("D[x](x*y)", y="z"), parse_term("D[x](x*z)"))

    def test_d_not_live_is_unchanged(self):
        self.assertEqual(self.sub("D[x](x*y)", w="x"), parse_term("D[x](x*y)"))

    def test_binder_is_renamed(self):
        self.assertEqual(self.sub("Int[t=0..1] x*t", x="t"),
                         parse_term("Int[t_1=0..1] t*t_1"))

    def test_rename_skips_a_taken_name(self):
        self.assertEqual(self.sub("Int[t=0..1] x*t*t_1", x="t"),
                         parse_term("Int[t_2=0..1] t*t_2*t_1"))

    def test_mapped_bound_name_is_left_alone(self):
        self.assertEqual(self.sub("Int[y=0..x] y", y="2"),
                         parse_term("Int[y=0..x] y"))

    def test_endpoint_and_body_are_substituted(self):
        self.assertEqual(self.sub("Int[y=0..x] x*y", x="2"),
                         parse_term("Int[y=0..2] 2*y"))


if __name__ == "__main__":
    unittest.main()
