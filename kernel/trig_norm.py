"""The trig normaliser (DESIGN.md §8.9; p1_expected section 22, E88).

Untrusted, like search.py. `propose(lhs, rhs, facts)` returns the §6.8
instances, as (entry name, inst) pairs in the order field must reduce by
them, that bring every sin, cos and tan atom of lhs - rhs whose arguments
are rational multiples of one base angle u to a polynomial in sin u and
cos u of degree at most one in cos u. The kernel builds each instance from
ENTRIES itself, emits what it owes, and re-runs the trusted field on them
(kernel._check), so a bug here costs a refusal, never a false `Proved`.

The instances, for each base angle u (E88):
  tan(n u)    tan_def, u := n u              (sin(n u)/cos(n u), owing
                                              cos(n u) # 0)
  sin(-n u)   sin_odd, u := n u    (n > 0)   -sin(n u)
  cos(-n u)   cos_even, u := n u   (n > 0)   cos(n u)
  sin(n u)    sin_add, u := (n - 1) u, v := u  for n = N down to 2
  cos(n u)    cos_add, u := (n - 1) u, v := u  for n = N down to 2
  (cos u)^2   pyth_cos, u := u                 last
Each right side mentions only atoms of later instances (E86's order), and
nothing here checks that: field does.
"""

from fractions import Fraction
from math import gcd, lcm

import field as FD
from terms import Add, App, Div, Mul, Neg, Pow, lit

TRIG = ("sin", "cos", "tan")
MAX_MULTIPLE = 12  # the largest n tried; beyond it, nothing is proposed


TRIG_COST = 24  # E95: the largest reduction proposed


def _atoms(t, out, power=1):
    """The sin, cos and tan applications reachable from t through ring and
    field operations, each with the exponent of the powers enclosing it:
    field reduces only these (an atom's argument is keyed, not reduced)."""
    if type(t) is App:
        if t.fn in TRIG:
            out.append((t, power))
        return
    if type(t) in (Add, Mul, Div):
        _atoms(t.a, out, power)
        _atoms(t.b, out, power)
    elif type(t) is Neg:
        _atoms(t.a, out, power)
    elif type(t) is Pow:
        _atoms(t.base, out, power * abs(t.n))


def _cost(t, n_of):
    """E95: an atom costs its multiple times its enclosing power; a sum
    costs its largest summand, a product the sum of its factors."""
    if type(t) is App:
        return n_of.get(t, 0)
    if type(t) is Add:
        return max(_cost(t.a, n_of), _cost(t.b, n_of))
    if type(t) in (Mul, Div):
        return _cost(t.a, n_of) + _cost(t.b, n_of)
    if type(t) is Neg:
        return _cost(t.a, n_of)
    if type(t) is Pow:
        return abs(t.n) * _cost(t.base, n_of)
    return 0


def _direction(p):
    """(key, c): p is c times the polynomial `key`, whose largest monomial
    has coefficient 1."""
    top = max(p)
    c = p[top]
    return frozenset((m, q / c) for m, q in p.items()), c


def _times(n, u):
    return u if n == 1 else Mul(lit(Fraction(n)), u)


def propose(lhs, rhs, facts=()):
    pairs = []
    _atoms(lhs, pairs)
    _atoms(rhs, pairs)
    if not pairs:
        return []
    found = [a for a, _ in pairs]
    polys, _ = FD.ring_polys([a.arg for a in found])
    families = {}  # key -> [(atom, multiple)]
    for a, p in zip(found, polys):
        if not p:
            continue  # sin 0, cos 0, tan 0: exact values, not ours
        key, c = _direction(p)
        families.setdefault(key, []).append((a, c))
    n_of = {}  # atom -> |multiple of its family's base angle|
    for members in families.values():
        cs = {c for _, c in members}
        g = Fraction(gcd(*(c.numerator for c in cs)),
                     lcm(*(c.denominator for c in cs)))
        for a, c in members:
            n_of[a] = abs(int(c / g))
    if max(_cost(lhs, n_of), _cost(rhs, n_of)) > TRIG_COST:
        return []
    out = []
    for members in families.values():
        cs = {c for _, c in members}
        g = Fraction(gcd(*(c.numerator for c in cs)),
                     lcm(*(c.denominator for c in cs)))
        a0, c0 = members[0]
        U = a0.arg if c0 == g else Mul(lit(g / c0), a0.arg)
        ns = {int(c / g) for c in cs}
        N = max(abs(n) for n in ns)
        if N > MAX_MULTIPLE:
            return []
        tans = sorted(n for fn, n in ((a.fn, int(c / g)) for a, c in members)
                      if fn == "tan")
        for n in dict.fromkeys(tans):
            out.append(("tan_def", {"u": _times(n, U) if n > 0 else
                                    Neg(_times(-n, U))}))
        negs = sorted({abs(n) for n in ns if n < 0})
        for n in negs:
            out.append(("sin_odd", {"u": _times(n, U)}))
            out.append(("cos_even", {"u": _times(n, U)}))
        for n in range(N, 1, -1):
            out.append(("sin_add", {"u": _times(n - 1, U), "v": U}))
            out.append(("cos_add", {"u": _times(n - 1, U), "v": U}))
        out.append(("pyth_cos", {"u": U}))
    return out
