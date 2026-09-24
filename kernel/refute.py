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
      COUNTERPOINT_CANDIDATES where every domain item and every former the
      proposition owes is discharged by steps (3)-(5), and the proposition
      is false by F1 (literal after the exact values, norm_num False) or F2.

`settled(key)` is steps (3)-(5): E7's norm_num, the exact values then
norm_num, or the search's certificate accepted by the trusted checker. A
terms.Refused met anywhere here is no refutation. `owed`, the formers a
subterm owes, is the kernel's `_owed`, passed in by the caller so that this
module does not import the kernel.
"""

import itertools
from dataclasses import dataclass, replace
from fractions import Fraction

import discharge as DC
import field as FD
import search as SR
from terms import (Interval, Refused, Rel, Term, Var, children, fv, lit,
                   show, with_domain, subst)

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
    item's midpoint when both ends are rational; (3) 0, 1, -1. A value is
    kept at its first occurrence only."""
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
    return values


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


def _counterpoint(key, owed):
    values = candidates(key)
    names = list(values)
    for qs in itertools.product(*(values[v] for v in names)):
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
    for item in key.dom:
        for p in _item_props(item):
            if settled(with_domain(subst(p, sub), ())) is None:
                return None
    at = subst(replace(key, dom=()), sub)
    sides = (at.lhs, at.rhs) if type(at) is Rel else (at.e,)
    for s in (s for side in sides for s in _subterms(side)):
        for p, _ in owed(s):
            if settled(with_domain(p, ())) is None:
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
