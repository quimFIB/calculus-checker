"""What an integrand is, as a function of x — the recognizer's eyes.

Everything here is untrusted assistance-tier code (DESIGN.md §16.1): it reads
terms and never proves anything. It borrows the ring spike's normaliser to see
through spelling — `x*(x+1)` and `x^2 + x` are one polynomial — and its
`field` to test that a ratio is constant, which is how f′/f is recognised.

**Sign convention.** A symbol other than x is assumed positive, which is what
the course's problems declare (`k > 0`, `E > 0`, `m > 0`). Under that
assumption a coefficient's sign is known when all of its terms agree, and
*unknown* otherwise (`a − e`). Rows treat unknown as "not ruled out": the
recognizer suggests, the kernel decides.
"""

import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "ring"))

import poly as P  # noqa: E402
from deriv import deriv  # noqa: E402
from field import Refused, _Normaliser, field  # noqa: E402
from terms import ZERO, free_vars, show, subterms  # noqa: E402

TRANSCENDENTAL = {"exp", "sin", "cos", "sinh", "cosh"}


def depends(t, x):
    return x in free_vars(t)


class InX:
    """A polynomial in x whose coefficients are polynomials in other atoms."""

    def __init__(self, coeffs, nz):
        self.coeffs = coeffs  # {degree: poly over the other atoms}
        self.nz = nz

    @property
    def degree(self):
        return max(self.coeffs, default=-1)

    def coeff(self, d):
        return self.coeffs.get(d, {})

    def show_coeff(self, d):
        return P.to_str(self.coeff(d), self.nz.atom_names.__getitem__)


def _split_by_x(p, xi):
    out = {}
    for m, c in p.items():
        d = dict(m).get(xi, 0)
        rest = tuple((i, e) for i, e in m if i != xi)
        out.setdefault(d, {})[rest] = c
    return out


def _x_only(nz, x):
    """The index of x, if every other atom is free of x; else False."""
    xi = nz.atom_index.get(("var", x))
    for i, term in enumerate(nz.atom_terms):
        if i != xi and depends(term, x):
            return False
    return xi


def poly_in(t, x):
    """t as a polynomial in x, or None if x occurs anywhere else."""
    nz = _Normaliser("ring")
    try:
        f = nz.norm(t)
    except Refused:
        return None
    xi = _x_only(nz, x)
    if xi is False:
        return None
    return InX(_split_by_x(f.num, xi) if xi is not None else {0: f.num}, nz)


def rational_in(t, x):
    """t as (numerator, denominator) polynomials in x, or None."""
    nz = _Normaliser("field")
    try:
        f = nz.norm(t)
    except Refused:
        return None
    xi = _x_only(nz, x)
    if xi is False:
        return None
    den = nz.expand(f.den)
    if xi is None:
        return InX({0: f.num}, nz), InX({0: den}, nz)
    return InX(_split_by_x(f.num, xi), nz), InX(_split_by_x(den, xi), nz)


def sign(p):
    """+1, -1, or 0 for unknown, with every non-x symbol taken as positive."""
    if not p:
        return 0
    signs = {c > 0 for c in p.values()}
    if len(signs) > 1:
        return 0
    return 1 if signs.pop() else -1


def completed_constant_sign(q):
    """Sign of c − b²/4a for the quadratic a·x² + b·x + c."""
    a, b, c = q.coeff(2), q.coeff(1), q.coeff(0)
    if not b:
        return sign(c)
    if all(P.is_const(p) for p in (a, b, c)):
        a, b, c = (P.const_value(p) for p in (a, b, c))
        v = c - b * b / (4 * a)
        return (v > 0) - (v < 0)
    return 0


def quadratic(t, x):
    q = poly_in(t, x)
    return q if q is not None and q.degree == 2 else None


def is_linear(t, x):
    q = poly_in(t, x)
    return q is not None and q.degree == 1


def factors(t):
    """The factors of a top-level product, reading u/v as u·(1/v)."""
    k = t[0]
    if k == "mul":
        return factors(t[1]) + factors(t[2])
    if k == "neg":
        return [("num", Fraction(-1))] + factors(t[1])
    if k == "div" and t[1] != ("num", Fraction(1)):
        return factors(t[1]) + [("div", ("num", Fraction(1)), t[2])]
    return [t]


def summands(t):
    if t[0] == "add":
        return summands(t[1]) + summands(t[2])
    if t[0] == "neg":
        return [("neg", s) for s in summands(t[1])]
    return [t]


def split_constant(t, x):
    """t = c · g with c free of x: return (c factors, g factors)."""
    fs = factors(t)
    return [f for f in fs if not depends(f, x)], [f for f in fs if depends(f, x)]


def is_constant_ratio(a, b, x):
    """Whether a / b is free of x, decided by D[x](a/b) ≐ 0 in `field`.

    `holds` alone is the right reading here: the recognizer only needs to
    know the shape, and the kernel will charge the obligations when the
    move is actually made.
    """
    try:
        return field(deriv(("div", a, b), x), ZERO).holds
    except (Refused, NotImplementedError):
        return False


def is_zero(t):
    try:
        return field(t, ZERO).holds
    except Refused:
        return False


def sqrt_subterms(t, x):
    return [s for s in subterms(t)
            if s[0] == "app" and s[1] == "sqrt" and depends(s[2][0], x)]


def show_poly(q, x):
    """Render an InX back in the grammar's syntax."""
    parts = []
    for d in sorted(q.coeffs, reverse=True):
        c = q.show_coeff(d)
        xs = "" if d == 0 else x if d == 1 else f"{x}^{d}"
        if not xs:
            parts.append(c if all(ch not in c for ch in " +-") else f"({c})")
        elif c == "1":
            parts.append(xs)
        else:
            parts.append(f"({c})*{xs}")
    return " + ".join(parts) or "0"


__all__ = [
    "InX", "TRANSCENDENTAL", "completed_constant_sign", "deriv", "depends",
    "factors", "is_constant_ratio", "is_linear", "is_zero", "poly_in", "quadratic",
    "rational_in", "show", "show_poly", "sign", "split_constant",
    "sqrt_subterms", "summands",
]
