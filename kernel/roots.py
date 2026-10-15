"""The untrusted root finder for residues (p1_expected E204).

Given a divisor that is a polynomial in one complex variable with
coefficients in Q(i), propose its factorisation lc*(z - r_1)^m_1*...: each
root in Q(i), or from a quadratic or a biquadratic with a real surd
sqrt(s), s a squarefree integer. Nothing here is trusted: the kernel
checks the factorisation by field on its split parts (kernel._residues),
so a wrong root costs a refusal, never a false theorem.

Exact arithmetic throughout (Fraction pairs); floats only to propose
candidate Gaussian rational roots, each verified exactly before use.
"""

import math
from fractions import Fraction

from terms import Add, App, CVar, Const, Div, Mul, Neg, Num, Pow

DEGREE_MAX = 12  # a larger square-free part is not attempted
RAW_DEGREE_MAX = 64  # nor a larger polynomial
DENOM_MAX = 10 ** 6  # the largest denominator a float root is read as
SURD_MAX = 10 ** 12  # the largest integer trial division factors


# ------------------------------------------------------------ Q(i)

def _c(re, im=0):
    return (Fraction(re), Fraction(im))


def _cadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def _cneg(a):
    return (-a[0], -a[1])


def _cmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def _cinv(a):
    n = a[0] * a[0] + a[1] * a[1]
    return (a[0] / n, -a[1] / n)


ZERO, ONE = _c(0), _c(1)


# ------------------------------------------------------------ polynomials
# a polynomial is a list of Q(i) coefficients, lowest degree first


def _trim(p):
    while p and p[-1] == ZERO:
        p = p[:-1]
    return p


def _padd(p, q):
    n = max(len(p), len(q))
    return _trim([_cadd(p[k] if k < len(p) else ZERO,
                        q[k] if k < len(q) else ZERO) for k in range(n)])


def _pmul(p, q):
    if not p or not q:
        return []
    out = [ZERO] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] = _cadd(out[i + j], _cmul(a, b))
    return _trim(out)


def poly(t, z):
    """t as a polynomial in the CVar named z over Q(i), or None."""
    k = type(t)
    if k is Num:
        return _trim([_c(t.n)])
    if k is Const and t.name == "i":
        return [_c(0, 1)]
    if k is CVar and t.name == z:
        return [ZERO, ONE]
    if k is Neg:
        p = poly(t.a, z)
        return None if p is None else [_cneg(c) for c in p]
    if k is Add or k is Mul:
        p, q = poly(t.a, z), poly(t.b, z)
        if p is None or q is None:
            return None
        return _padd(p, q) if k is Add else _pmul(p, q)
    if k is Div:
        p, q = poly(t.a, z), poly(t.b, z)
        if p is None or q is None or len(q) != 1:
            return None  # only a constant divisor
        inv = _cinv(q[0])
        return [_cmul(c, inv) for c in p]
    if k is Pow and t.n >= 0:
        p = poly(t.base, z)
        if p is None:
            return None
        out = [ONE]
        for _ in range(t.n):
            out = _pmul(out, p)
        return out
    return None


def _eval(p, x):
    out = ZERO
    for c in reversed(p):
        out = _cadd(_cmul(out, x), c)
    return out


def _deflate(p, r):
    """p / (z - r), exact; r must be a root."""
    n = len(p) - 1
    out = [ZERO] * n
    acc = ZERO
    for k in range(n, 0, -1):
        acc = _cadd(_cmul(acc, r), p[k])
        out[k - 1] = acc
    return out


# ------------------------------------------------------------ surds
# a root is (A, B, s): A + B*sqrt(s), A and B in Q(i), s a squarefree
# integer >= 2, or (A, ZERO, 1) for a root in Q(i)


class _TooLarge(Exception):
    pass


def _squarefree(n):
    """(k, s) with n == k^2 * s, s squarefree; n a positive integer."""
    if n > SURD_MAX:
        raise _TooLarge()
    k, s, f = 1, 1, 2
    while f * f <= n:
        while n % (f * f) == 0:
            n //= f * f
            k *= f
        f += 1
    return k, n


def _rsqrt(q):
    """sqrt(q) for a rational q >= 0 as (c, s): c*sqrt(s), c rational."""
    if q == 0:
        return Fraction(0), 1
    num, den = q.numerator * q.denominator, q.denominator
    k, s = _squarefree(num)
    return Fraction(k, den), s


def _csqrt(w):
    """A square root of w in Q(i) as (C, s), C*sqrt(s) with C in Q(i), or
    None when it needs more than one surd."""
    p, q = w
    if q == 0:
        if p >= 0:
            c, s = _rsqrt(p)
            return _c(c), s
        c, s = _rsqrt(-p)
        return _c(0, c), s
    m2 = p * p + q * q
    m, s = _rsqrt(m2)
    if s != 1:
        return None
    xc, xs = _rsqrt((m + p) / 2)
    yc, ys = _rsqrt((m - p) / 2)
    if q < 0:
        yc = -yc
    if xc == 0:
        return _c(0, yc), ys
    if yc == 0:
        return _c(xc), xs
    if xs != ys:
        return None
    return _c(xc, yc), xs


def _quadratic(a, b, c):
    """The two roots of a z^2 + b z + c, or None."""
    disc = _cadd(_cmul(b, b), _cneg(_cmul(_c(4), _cmul(a, c))))
    r = _csqrt(disc)
    if r is None:
        return None
    C, s = r
    inv = _cinv(_cmul(_c(2), a))
    A = _cmul(_cneg(b), inv)
    B = _cmul(C, inv)
    if s == 1:
        return [(_cadd(A, B), ZERO, 1), (_cadd(A, _cneg(B)), ZERO, 1)]
    return [(A, B, s), (A, _cneg(B), s)]


def _biquadratic(p):
    """Roots of a z^4 + b z^2 + c with w = z^2 in Q(i), or None."""
    ws = _quadratic(p[4], p[2], p[0])
    if ws is None or any(B != ZERO for _, B, _ in ws):
        return None
    out = []
    for w, _, _ in ws:
        r = _csqrt(w)
        if r is None:
            return None
        C, s = r
        if s == 1:
            out += [(C, ZERO, 1), (_cneg(C), ZERO, 1)]
        else:
            out += [(ZERO, C, s), (ZERO, _cneg(C), s)]
    return out


def _float_roots(p):
    """Durand-Kerner on p's coefficients as floats."""
    n = len(p) - 1
    lead = complex(*map(float, p[-1]))
    cs = [complex(*map(float, c)) / lead for c in p]
    xs = [(0.4 + 0.9j) ** k for k in range(n)]
    for _ in range(500):
        new = []
        for i, x in enumerate(xs):
            num = sum(c * x ** k for k, c in enumerate(cs))
            den = 1
            for j, y in enumerate(xs):
                if j != i:
                    den *= x - y
            new.append(x - num / den if den else x + 1e-9)
        if max(abs(a - b) for a, b in zip(new, xs)) < 1e-14:
            xs = new
            break
        xs = new
    return xs


def _rational(x):
    return (Fraction(x.real).limit_denominator(DENOM_MAX),
            Fraction(x.imag).limit_denominator(DENOM_MAX))


def _pdivmod(p, q):
    """(quotient, remainder) of p by q over Q(i)."""
    p, out = list(p), [ZERO] * max(len(p) - len(q) + 1, 1)
    inv = _cinv(q[-1])
    while len(p) >= len(q) and p:
        c = _cmul(p[-1], inv)
        k = len(p) - len(q)
        out[k] = c
        for j, b in enumerate(q):
            p[k + j] = _cadd(p[k + j], _cneg(_cmul(c, b)))
        p = _trim(p[:-1]) if p[-1] == ZERO else _trim(p)
    return _trim(out), _trim(p)


def _gcd(p, q):
    """The monic gcd, so a constant gcd leaves p's square-free part p."""
    while q:
        p, q = q, _pdivmod(p, q)[1]
    inv = _cinv(p[-1])
    return [_cmul(c, inv) for c in p]


def _derivative(p):
    return _trim([_cmul(_c(k), c) for k, c in enumerate(p)][1:])


def _times_dividing(p, q):
    """How many times q divides p exactly."""
    m = 0
    while len(p) >= len(q):
        quo, rem = _pdivmod(p, q)
        if rem:
            break
        p, m = quo, m + 1
    return m


def factor(p):
    """(lc, [(root, multiplicity)]) for a polynomial p of degree >= 1, or
    None. Roots are (A, B, s) triples. The square-free part p/gcd(p, p')
    is factored, and each root's multiplicity counted by exact division
    (E211)."""
    p = _trim(p)
    if len(p) < 2:
        return None
    k = 0
    while p[0] == ZERO:  # the root 0, before the degree bound
        p, k = p[1:], k + 1
    lc = p[-1]
    if len(p) - 1 > RAW_DEGREE_MAX:
        return None
    try:
        sqf = _pdivmod(p, _gcd(p, _derivative(p)))[0] if len(p) > 1 else p
        if len(sqf) - 1 > DEGREE_MAX:
            return None
        found = [] if len(p) < 2 else _factor_sqf(sqf)
    except _TooLarge:
        return None
    if found is None:
        return None
    out = [((ZERO, ZERO, 1), k)] if k else []
    for root, factor_poly in found:
        out.append((root, _times_dividing(p, factor_poly)))
    return lc, out


def _factor_sqf(p):
    """[(root, the polynomial over Q(i) it is a root of)] for a
    square-free p, or None: a Q(i) root with its linear factor, a surd
    pair with its quadratic, a biquadratic's four with the quartic."""
    found = []
    while len(p) > 1 and p[0] == ZERO:  # the root 0
        p = p[1:]
        found.append(((ZERO, ZERO, 1), [ZERO, ONE]))
    progress = True
    while len(p) > 2 and progress:
        progress = False
        for x in _float_roots(p):
            if not all(math.isfinite(v) for v in (x.real, x.imag)):
                continue
            r = _rational(x)
            if _eval(p, r) == ZERO:
                p = _deflate(p, r)
                found.append(((r, ZERO, 1), [_cneg(r), ONE]))
                progress = True
                break
    if len(p) == 2:
        r = _cmul(_cneg(p[0]), _cinv(p[1]))
        found.append(((r, ZERO, 1), [_cneg(r), ONE]))
        return found
    if len(p) == 1:
        return found
    rest = None
    if len(p) == 3:
        rest = _quadratic(p[2], p[1], p[0])
    elif len(p) == 5 and p[1] == ZERO and p[3] == ZERO:
        rest = _biquadratic(p)
    if rest is None:
        return None
    if all(B == ZERO for _, B, _ in rest):  # rational after all
        return found + [((A, ZERO, 1), [_cneg(A), ONE]) for A, _, _ in rest]
    return found + [(r, p) for r in rest]


# ------------------------------------------------------------ terms

def _frac(q):
    """A rational as a term: Num, Div(Num, Num), or Neg of one."""
    a = abs(q)
    t = Num(a.numerator) if a.denominator == 1 else \
        Div(Num(a.numerator), Num(a.denominator))
    return Neg(t) if q < 0 else t


def _real(c0, c1, s):
    """c0 + c1*sqrt(s) as _sum's parts (empty for 0)."""
    parts = []
    if c0:
        parts.append(_frac(c0))
    if c1:
        sq = App("sqrt", Num(s))
        a = abs(c1)
        if a == 1:
            t = sq
        elif a.denominator == 1:
            t = Mul(Num(a.numerator), sq)
        elif a.numerator == 1:
            t = Div(sq, Num(a.denominator))
        else:
            t = Div(Mul(Num(a.numerator), sq), Num(a.denominator))
        parts.append((c1 < 0, t))
    return parts


def _sum(parts):
    out = None
    for p in parts:
        neg, t = p if isinstance(p, tuple) else (False, p)
        if isinstance(t, Neg):
            neg, t = not neg, t.a
        if out is None:
            out = Neg(t) if neg else t
        else:
            out = Add(out, Neg(t)) if neg else Add(out, t)
    return out


def root_term(root):
    """(A, B, s) as a term: its real part, then its imaginary part times
    i, each a rational plus a rational times sqrt(s)."""
    A, B, s = root
    re = _real(A[0], B[0], s) if s != 1 else _real(A[0], 0, s)
    im = _real(A[1], B[1], s) if s != 1 else _real(A[1], 0, s)
    i = Const("i")
    out = list(re)
    if im:
        it = _sum(im)
        neg = isinstance(it, Neg)
        core = it.a if neg else it
        core = i if core == Num(1) else Mul(core, i)
        out.append((neg, core))
    if not out:
        return Num(0)
    return _sum(out)


def surds(root):
    """The s of a surd root, or None."""
    return root[2] if root[2] != 1 else None


# ------------------------------------------------------------ rational
# K4c-i (p1_expected E214): a proposed P/Q for a rational term, which the
# kernel checks by field; and a polynomial written back as a term.

def _pneg(p):
    return [_cneg(c) for c in p]


def rational(t, z):
    """(P, Q) polynomials over Q(i) with t == P/Q, or None."""
    p = poly(t, z)
    if p is not None:
        return p, [ONE]
    k = type(t)
    if k is Neg:
        r = rational(t.a, z)
        return None if r is None else (_pneg(r[0]), r[1])
    if k in (Add, Mul, Div):
        a, b = rational(t.a, z), rational(t.b, z)
        if a is None or b is None:
            return None
        (p1, q1), (p2, q2) = a, b
        if k is Add:
            return _padd(_pmul(p1, q2), _pmul(p2, q1)), _pmul(q1, q2)
        if k is Mul:
            return _pmul(p1, p2), _pmul(q1, q2)
        if not p2:
            return None
        return _pmul(p1, q2), _pmul(q1, p2)
    if k is Pow:
        r = rational(t.base, z)
        if r is None or (t.n < 0 and not r[0]):
            return None
        p, q = r if t.n >= 0 else (r[1], r[0])
        out_p, out_q = [ONE], [ONE]
        for _ in range(abs(t.n)):
            out_p, out_q = _pmul(out_p, p), _pmul(out_q, q)
        return out_p, out_q
    return None


def poly_term(p, z):
    """sum of c_k*z^k, highest degree first, as a term."""
    zc = CVar(z)
    parts = []
    for k in range(len(p) - 1, -1, -1):
        c = p[k]
        if c == ZERO:
            continue
        mono = None if k == 0 else zc if k == 1 else Pow(zc, k)
        ct = root_term((c, ZERO, 1))
        neg = isinstance(ct, Neg)
        core = ct.a if neg else ct
        if mono is None:
            term = core
        elif core == Num(1):
            term = mono
        else:
            term = Mul(core if not isinstance(core, Add) else core, mono)
        parts.append((neg, term))
    return _sum(parts) if parts else Num(0)
