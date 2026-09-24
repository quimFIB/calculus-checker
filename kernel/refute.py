"""Decided false: E33's F1, F2 and F3 (§18 Q22, settled 2026-09-24).

Untrusted (DESIGN.md §15.2's untrusted callees; p1_expected E33,
DISCHARGE_RULE "Decided false"). A refutation can only refuse a step, and a
refused step changes nothing (E13), so a bug here costs a wrongly refused
step, never a false 'Proved'. That is the condition under which trusted code
may call untrusted code, argued as schema.check_evaluated's is.

An obligation that is not literal as emitted is decided false in exactly
three ways, each giving 'obligation-decided-false' with a message saying how
(E35 (4)):

  F1  `exact_false`: the exact values (discharge.exact_values) changed it
      and made it literal, and norm_num finds it false.
  F2  `refute`, a closed ordering whose negation (a > b to a <= b, a >= b to
      a < b, and back) is discharged by DISCHARGE_RULE's steps (3)-(5).
  F3  `refute`, a key with a free variable, at the first point of
      COUNTERPOINT_CANDIDATES, among the first POINT_BOUND, where every
      former the proposition and the domain items owe is settled, every
      domain item is settled, and the proposition is false by F1 (literal
      after the exact values, norm_num False) or F2.

`settled(key)` is steps (3)-(5): E7's norm_num, the exact values then
norm_num, or the search's certificate accepted by the trusted checker. A
terms.Refused met anywhere here is no refutation. `owed`, the formers a
subterm owes, is the kernel's `_owed`, passed in by the caller so that this
module does not import the kernel.
"""

import itertools
from dataclasses import dataclass, replace
from fractions import Fraction

import math

import discharge as DC
import field as FD
import poly as P
import search as SR
from terms import (Add, Interval, Mul, Neg, NonZero, Pow, Refused, Rel, Term,
                   Var, children, fv, lit, show, with_domain, subst)

# p1_expected's DECIDED_FALSE_MESSAGES, which the suite checks these against.
MESSAGES = {
    "exact": "{key} is false: with {entries} it reads {rewritten}",
    "negation": "{key} is false: its negation {negation} holds ({tag})",
    "point": "{key} is false at {point}, where it reads {reading}",
    "point_exact": "{key} is false at {point}, where with {entries} it "
                   "reads {reading}",
    "point_negation": "{key} is false at {point}, where its negation "
                      "{negation} holds ({tag})",
}
NEGATION = {">": "<=", ">=": "<", "<": ">=", "<=": ">"}
# COUNTERPOINT_CANDIDATES' bound: the walk visits at most this many points
# (the Cartesian product is exponential in the number of variables), and a
# key with no refuting point among them is admitted, tagged none (E35 (5)).
POINT_BOUND = 256
# E50's bound on the rational root test, as the tagger's factoriser's: a
# polynomial whose lowest nonzero or leading integer coefficient exceeds it
# contributes no root.
ROOT_TEST_BOUND = 10 ** 6


@dataclass(frozen=True)
class Refutation:
    how: str          # a MESSAGES key
    message: str
    point: object = None  # F3: {variable: Fraction}


def decided_false(key, owed):
    """F1, then F2 or F3: the Refutation for `key`, or None. The kernel asks
    F1 at step (4) and the others at step (6), after certification; a key
    the checker accepts is true, so neither order refutes one."""
    return exact_false(key) or refute(key, owed)


def exact_false(key):
    """F1 (DISCHARGE_RULE step (4)): the exact values changed the key and
    made it literal, and norm_num says False."""
    try:
        new, used = DC.exact_values(key)
        if new != key and FD.norm_num(new) is False:
            return Refutation("exact", MESSAGES["exact"].format(
                key=show(key), entries=", ".join(used), rewritten=show(new)))
    except Refused:
        pass
    return None


def refute(key, owed):
    """F2 for a closed key, F3 for a key with a free variable (step (6))."""
    try:
        if not fv(key):
            neg = _negation(key)
            if neg is None:
                return None
            return Refutation("negation", MESSAGES["negation"].format(
                key=show(key), negation=show(neg[0]), tag=_tag_text(neg[1])))
        return _counterpoint(key, owed)
    except Refused:
        return None


def settled(key):
    """The tag with which steps (3)-(5) discharge the closed or open `key`,
    or None."""
    try:
        said = FD.norm_num(key)
        if said is not None:
            return ("norm_num", ()) if said else None
        new, used = DC.exact_values(key)
        said = FD.norm_num(new)
        if said is not None:
            return ("norm_num", used) if said else None
        cert = SR.propose(key)
        return None if cert is None else DC.check(key, cert)
    except Refused:
        return None


def _tag_text(tag):
    return ", ".join((tag[0],) + tuple(tag[1]))


def _negation(prop):
    """(negated proposition, the tag that discharges it) for an ordering
    whose negation steps (3)-(5) discharge, else None. A # 0 has none: its
    negation is an equation."""
    if type(prop) is not Rel or prop.op not in NEGATION:
        return None
    neg = replace(prop, op=NEGATION[prop.op], dom=())
    tag = settled(neg)
    return None if tag is None else (neg, tag)


# ---------------------------------------------------------------- F3

def candidates(key):
    """COUNTERPOINT_CANDIDATES: variable -> its values in order, for every
    free variable of the key. (1) each domain item that bounds v alone
    against a rational literal c: c when closed or non-strict, c + 1 for a
    strict lower bound, c - 1 for a strict upper one; (2) each Interval
    item's midpoint when both ends are rational; (3) 0, 1, -1; (4) E50's
    rational roots of the target's univariate pieces in v (`roots`). A
    value is kept at its first occurrence only."""
    values = {v: [] for v in sorted(fv(key))}

    def add(v, q):
        if v in values and q not in values[v]:
            values[v].append(Fraction(q))

    for item in key.dom:
        if type(item) is Interval:
            for end, closed, step in ((item.lo, item.lo_closed, 1),
                                      (item.hi, item.hi_closed, -1)):
                c = FD.rational_value(end) if isinstance(end, Term) else None
                if c is not None:
                    add(item.var, c if closed else c + step)
        elif type(item) is Rel:
            bound = _bound(item)
            if bound is not None:
                add(*bound)
    for item in key.dom:
        if type(item) is Interval and isinstance(item.lo, Term) \
                and isinstance(item.hi, Term):
            lo, hi = FD.rational_value(item.lo), FD.rational_value(item.hi)
            if lo is not None and hi is not None:
                add(item.var, (lo + hi) / 2)
    for v in values:
        for q in (0, 1, -1):
            add(v, q)
    for v in values:
        for q in roots(key, v):
            add(v, q)
    return values


def roots(key, v):
    """E50, COUNTERPOINT_CANDIDATES (4): the rational roots in v of each
    polynomial piece of the key's target (the target, each factor of a
    top-level product, each base of an integer power, recursively) whose
    ring normal form has v as its only atom, by the rational root test on
    its integer coefficients, bounded by ROOT_TEST_BOUND, each kept only
    where the polynomial is exactly 0, smallest |r| first and positive
    before negative, and dropped when a domain item bounding v against a
    rational literal excludes it. A seam (ARCHITECTURE.md §7)."""
    prop = replace(key, dom=())
    target = prop.e if type(prop) is NonZero else Add(prop.lhs, Neg(prop.rhs))
    found = []
    for piece in _pieces(target):
        try:
            (p,), atoms = FD.ring_polys([piece])
        except Refused:
            continue
        if atoms != (Var(v),):
            continue
        found += [r for r in _rational_roots(p) if r not in found]
    found.sort(key=lambda r: (abs(r), r < 0))
    return [r for r in found if _within(key, v, r)]


def _pieces(t):
    """t, each factor of a top-level product in it, and each base of an
    integer power, recursively (E50)."""
    out, todo = [], [t]
    while todo:
        u = todo.pop()
        out.append(u)
        if type(u) is Mul:
            todo += [u.a, u.b]
        elif type(u) is Neg:
            todo.append(u.a)
        elif type(u) is Pow and u.n > 0:
            todo.append(u.base)
    return out


def _rational_roots(p):
    """The rational roots of a univariate polynomial p (one atom, index 0)
    by the rational root test, bounded by ROOT_TEST_BOUND."""
    if not p:
        return []
    n = P.degree_in(p, 0)
    coeffs = [p.get(((0, k),) if k else P.ONE_MONO, Fraction(0)) for k in range(n + 1)]
    lcm = math.lcm(*(c.denominator for c in coeffs))
    ints = [int(c * lcm) for c in coeffs]
    low = next(k for k, c in enumerate(ints) if c)
    if max(abs(ints[low]), abs(ints[n])) > ROOT_TEST_BOUND:
        return []
    out = [Fraction(0)] if low else []
    divs, dens = _divisors(ints[low]), _divisors(ints[n])
    for r in sorted({Fraction(s * a, b) for a in divs for b in dens for s in (1, -1)},
                    key=lambda r: (abs(r), r < 0)):
        if sum(c * r ** k for k, c in enumerate(coeffs)) == 0 and r not in out:
            out.append(r)
    return out


def _divisors(n):
    n = abs(n)
    small = [d for d in range(1, math.isqrt(n) + 1) if n % d == 0]
    return sorted(set(small + [n // d for d in small]))


def _within(key, v, r):
    """r satisfies every domain item that bounds v against a rational
    literal (an Interval's rational ends, a relation v REL c)."""
    for item in key.dom:
        if type(item) is Interval and item.var == v:
            for end, closed, lower in ((item.lo, item.lo_closed, True),
                                       (item.hi, item.hi_closed, False)):
                c = FD.rational_value(end) if isinstance(end, Term) else None
                if c is not None and not (
                        (r > c if lower else r < c) or (closed and r == c)):
                    return False
        elif type(item) is Rel:
            bound = _bound(item)
            if bound is not None and bound[0] == v:
                x = Rel(item.op, lit(r) if type(item.lhs) is Var else item.lhs,
                        lit(r) if type(item.rhs) is Var else item.rhs)
                if FD.norm_num(x) is False:
                    return False
    return True


_FLIP = {">": "<", ">=": "<=", "<": ">", "<=": ">=", "==": "=="}
_STEP = {">": 1, ">=": 0, "<": -1, "<=": 0, "==": 0}


def _bound(rel):
    """(v, value) for a relation item v REL c or c REL v, c rational."""
    if type(rel.lhs) is Var and FD.rational_value(rel.rhs) is not None:
        v, c, op = rel.lhs.name, FD.rational_value(rel.rhs), rel.op
    elif type(rel.rhs) is Var and FD.rational_value(rel.lhs) is not None:
        v, c, op = rel.rhs.name, FD.rational_value(rel.lhs), _FLIP[rel.op]
    else:
        return None
    return v, c + _STEP[op]


def _item_props(item):
    """A domain item as closed-able propositions: an Interval is its finite
    bounds, anything else is itself."""
    if type(item) is not Interval:
        return [item]
    v, out = Var(item.var), []
    if isinstance(item.lo, Term):
        out.append(Rel("<=" if item.lo_closed else "<", item.lo, v))
    if isinstance(item.hi, Term):
        out.append(Rel("<=" if item.hi_closed else "<", v, item.hi))
    return out


def _subterms(t):
    yield t
    for _, k in children(t):
        if isinstance(k, Term):
            yield from _subterms(k)


def _defined(prop, owed):
    """Every former the closed proposition's terms owe (kernel._owed over
    its subterms) is settled: its terms are defined there."""
    sides = (prop.lhs, prop.rhs) if type(prop) is Rel else (prop.e,)
    return all(settled(with_domain(p, ())) is not None
               for side in sides for s in _subterms(side) for p, _ in owed(s))


def _counterpoint(key, owed):
    values = candidates(key)
    names = list(values)
    points = itertools.product(*(values[v] for v in names))
    for qs in itertools.islice(points, POINT_BOUND):
        try:
            found = _false_at(key, dict(zip(names, qs)), owed)
        except Refused:
            found = None
        if found is not None:
            return found
    return None


def _false_at(key, env, owed):
    """The Refutation of `key` at the point `env`, or None."""
    sub = {v: lit(q) for v, q in env.items()}
    for item in key.dom:  # each item defined at the point, and holding there
        for p in _item_props(item):
            p = subst(p, sub)
            if not _defined(p, owed) or settled(with_domain(p, ())) is None:
                return None
    at = subst(replace(key, dom=()), sub)
    if not _defined(at, owed):
        return None
    parts = {"key": show(key),
             "point": ", ".join(f"{v} = {show(lit(q))}"
                                for v, q in sorted(env.items()))}
    new, used = DC.exact_values(at)
    if FD.norm_num(new) is False:
        how = "point_exact" if used else "point"
        return Refutation(how, MESSAGES[how].format(
            **parts, entries=", ".join(used), reading=show(new)), dict(env))
    neg = _negation(at)
    if neg is not None:
        return Refutation("point_negation", MESSAGES["point_negation"].format(
            **parts, negation=show(neg[0]), tag=_tag_text(neg[1])), dict(env))
    return None
