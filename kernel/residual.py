"""Residuals as terms: what a failed check reports (DESIGN.md §8.7).

Untrusted. The kernel calls this only to fill a Refusal's `residual`, and a
refused step changes nothing (p1_expected E13), so no bug here can produce a
theorem. A wrong rendering is caught instead by the regression suite, which
compares every reported residual with the expected one by `ring` or `field`
equality, never as a string (E14).

This takes over the spike's display code: poly.py's `to_str` and
`divide_exact`, and field.py's `_Normaliser.residual`. Any tidying is
allowed here, since only the value is asserted. It should cancel exact
factors from the denominator the way the spike did, so that §11.1's
residual reads `-t*sin t`.
"""

import poly as P
from terms import Add, Div, Mul, Neg, Num, Pow, lit


def divide_exact(p, f):
    """p / f if f divides p exactly in ℚ[atoms], else None.

    Division by a single polynomial under a monomial order: if f | p the
    quotient is found term by term from the leading terms. Used only to tidy
    residuals for display, never to decide an equation.
    """
    if not f:
        raise ZeroDivisionError("division by the zero polynomial")
    lf = P.leading(f)
    cf = f[lf]
    lfd = dict(lf)
    q = {}
    r = dict(p)
    while r:
        lr = P.leading(r)
        exps = dict(lr)
        if any(exps.get(i, 0) < e for i, e in lfd.items()):
            return None
        t = {P.mono_div(lr, lf): r[lr] / cf}
        q = P.add(q, t)
        r = P.sub(r, P.mul(t, f))
    return q


def poly_term(p, atoms):
    """The Term for polynomial p, where `atoms[i]` is the Term for atom i.

    Monomials go in poly.lex_key order, largest first, each a left-nested
    product of its coefficient (built with terms.lit, left out when it is 1)
    and its atoms, with Pow(atom, e) for e > 1. A negative term after the
    first is Add(acc, Neg(monomial)), which prints as a subtraction. A
    negative first term carries its Neg on its first factor, so that
    §11.1's residual prints `-t*sin t` and not `-(t*sin t)`. The zero
    polynomial is Num(0). The result has exactly p's value, and that is the
    only property anything relies on. The tagger reuses this to name a
    factor or a content part as a Term.
    """
    out = None
    for m in sorted(p, key=P.lex_key, reverse=True):
        c = p[m]
        fs = [atoms[i] if e == 1 else Pow(atoms[i], e) for i, e in m]
        if abs(c) != 1 or not fs:
            fs.insert(0, lit(abs(c)))
        if c < 0 and out is None:
            fs[0] = Neg(fs[0])
        t = fs[0]
        for f in fs[1:]:
            t = Mul(t, f)
        if out is None:
            out = t
        else:
            out = Add(out, Neg(t) if c < 0 else t)
    return Num(0) if out is None else out


def residual_term(r):
    """The Term for a field.Residual: poly_term(num), divided by the product
    of the den factors raised to their exponents, after cancelling each
    factor that divides num exactly. With no denominator left it is the
    numerator alone."""
    num, den = r.num, None
    for f, e in r.den:
        while e and num:
            q = divide_exact(num, f)
            if q is None:
                break
            num, e = q, e - 1
        if e:
            ft = poly_term(f, r.atoms)
            ft = ft if e == 1 else Pow(ft, e)
            den = ft if den is None else Mul(den, ft)
    t = poly_term(num, r.atoms)
    return t if den is None else Div(t, den)
