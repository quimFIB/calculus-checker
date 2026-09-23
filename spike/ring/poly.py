"""Sparse multivariate polynomials over ℚ (DESIGN.md §6.2, §16.2).

A polynomial is a dict {monomial: Fraction} holding no zero coefficients, so
the zero polynomial is {} and equality is dict equality. A monomial is a tuple
of (atom index, exponent) pairs sorted by atom index, every exponent positive;
the empty tuple is the constant monomial. What an atom index *means* is the
caller's business — this module knows nothing about terms.

Functions return fresh dicts and never mutate their arguments.
"""

from fractions import Fraction

ONE_MONO = ()


def const(c):
    c = Fraction(c)
    return {ONE_MONO: c} if c else {}


def atom(i, e=1):
    return {((i, e),): Fraction(1)}


def is_const(p):
    return not p or (len(p) == 1 and ONE_MONO in p)


def const_value(p):
    return p.get(ONE_MONO, Fraction(0))


def add(p, q):
    if len(p) < len(q):
        p, q = q, p
    r = dict(p)
    for m, c in q.items():
        s = r.get(m, 0) + c
        if s:
            r[m] = s
        else:
            del r[m]
    return r


def neg(p):
    return {m: -c for m, c in p.items()}


def sub(p, q):
    return add(p, neg(q))


def scale(p, c):
    if not c:
        return {}
    return {m: v * c for m, v in p.items()}


def mono_mul(a, b):
    i = j = 0
    out = []
    while i < len(a) and j < len(b):
        ai, bj = a[i][0], b[j][0]
        if ai == bj:
            out.append((ai, a[i][1] + b[j][1]))
            i += 1
            j += 1
        elif ai < bj:
            out.append(a[i])
            i += 1
        else:
            out.append(b[j])
            j += 1
    out.extend(a[i:])
    out.extend(b[j:])
    return tuple(out)


def mul(p, q):
    if not p or not q:
        return {}
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = mono_mul(m1, m2)
            s = r.get(m, 0) + c1 * c2
            if s:
                r[m] = s
            else:
                r.pop(m, None)
    return r


def power(p, n):
    if n < 0:
        raise ValueError("negative power of a polynomial")
    result = const(1)
    base = p
    while n:
        if n & 1:
            result = mul(result, base)
        n >>= 1
        if n:
            base = mul(base, base)
    return result


def lex_key(m):
    """Sort key giving lexicographic order with atom 0 most significant.

    Comparing sparse monomials as plain tuples is *not* a monomial order —
    ((1, 1),) would beat ((0, 1),). Negating the index fixes that, and a
    monomial that extends another is correctly the larger of the two.
    """
    return tuple((-i, e) for i, e in m)


def leading(p):
    return max(p, key=lex_key)


def content_normal(p):
    """Split p into (c, q) with p = c·q and q's leading coefficient 1."""
    c = p[leading(p)]
    return c, scale(p, 1 / c)


def monomial_gcd(p):
    """The largest monomial dividing every term of p."""
    it = iter(p)
    g = dict(next(it))
    for m in it:
        exps = dict(m)
        g = {i: min(e, exps[i]) for i, e in g.items() if i in exps}
        if not g:
            break
    return tuple(sorted(g.items()))


def mono_div(m, g):
    """m / g, for a monomial g known to divide m."""
    gd = dict(g)
    out = []
    for i, e in m:
        e -= gd.get(i, 0)
        if e:
            out.append((i, e))
    return tuple(out)


def divide_exact(p, f):
    """p / f if f divides p exactly in ℚ[atoms], else None.

    Division by a single polynomial under a monomial order: if f | p the
    quotient is found term by term from the leading terms. Used only to tidy
    residuals for display, never to decide an equation.
    """
    if not f:
        raise ZeroDivisionError("division by the zero polynomial")
    lf = leading(f)
    cf = f[lf]
    lfd = dict(lf)
    q = {}
    r = dict(p)
    while r:
        lr = leading(r)
        exps = dict(lr)
        if any(exps.get(i, 0) < e for i, e in lfd.items()):
            return None
        t = {mono_div(lr, lf): r[lr] / cf}
        q = add(q, t)
        r = sub(r, mul(t, f))
    return q


def frozen(p):
    """A hashable, order-independent form of p."""
    return tuple(sorted(p.items()))


def degree_in(p, i):
    return max((dict(m).get(i, 0) for m in p), default=0)


def to_str(p, name):
    """Render p, with `name(i)` giving the display form of atom i."""
    if not p:
        return "0"
    parts = []
    for m in sorted(p, key=lex_key, reverse=True):
        c = p[m]
        factors = [name(i) if e == 1 else f"{name(i)}^{e}" for i, e in m]
        mag = abs(c)
        if not factors:
            body = str(mag)
        elif mag == 1:
            body = "*".join(factors)
        else:
            body = f"{mag}*" + "*".join(factors)
        parts.append(("- " if c < 0 else "+ ") + body)
    s = " ".join(parts)
    return s[2:] if s.startswith("+ ") else "-" + s[2:]
