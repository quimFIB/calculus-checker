"""The factoriser and the partial-fraction solver (DESIGN.md §8.4;
app/assist/FACTOR.md).

Untrusted (tier 2). Search whose output is cheap to verify: every
factorisation and every decomposition is handed to the kernel's own `ring`
or `field` (with the fact (sqrt d)^2 = d when a radical appears) before it
is returned, and one the kernel does not accept is never returned. Nothing
here enters a proof.
"""

import math
from fractions import Fraction

from assist.shapes import KERNEL  # noqa: F401  (puts kernel/ on the path)
import field as FD
from terms import Refused, Var, parse_term, show

MAX_DEGREE = 12
ROOT_BOUND = 10 ** 6  # as kernel/tagger.py's ROOT_TEST_BOUND


class Refusal(Exception):
    def __init__(self, code, message):
        super().__init__(f"{code}: {message}")
        self.code, self.message = code, message


# ---------------------------------------------------------------- ℚ(√d)

class QD:
    """a + b√d, a and b Fractions; d a squarefree integer ≥ 2, or 0 when
    the number is rational (b = 0)."""

    __slots__ = ("a", "b", "d")

    def __init__(self, a, b=0, d=0):
        self.a, self.b = Fraction(a), Fraction(b)
        self.d = d if self.b else 0

    def _d(self, o):
        if self.d and o.d and self.d != o.d:
            raise Refusal("too-large", "two different radicals")
        return self.d or o.d

    def __add__(self, o):
        o = lift(o)
        return QD(self.a + o.a, self.b + o.b, self._d(o))

    def __neg__(self):
        return QD(-self.a, -self.b, self.d)

    def __sub__(self, o):
        return self + (-lift(o))

    def __mul__(self, o):
        o = lift(o)
        d = self._d(o)
        return QD(self.a * o.a + self.b * o.b * d,
                  self.a * o.b + self.b * o.a, d)

    def inv(self):
        n = self.a * self.a - self.b * self.b * self.d
        if n == 0:
            raise ZeroDivisionError("zero in ℚ(√d)")
        return QD(self.a / n, -self.b / n, self.d)

    def __truediv__(self, o):
        return self * lift(o).inv()

    def __eq__(self, o):
        o = lift(o)
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def is_zero(self):
        return self.a == 0 and self.b == 0

    def rational(self):
        return self.b == 0

    def text(self):
        """GRAMMAR.md text: a rational, b*sqrt d, or (a + b*sqrt d)."""
        if self.b == 0:
            return _frac(self.a)
        rad = f"sqrt {self.d}"
        b = rad if self.b == 1 else f"-{rad}" if self.b == -1 else \
            f"{_frac(self.b)}*{rad}"
        if self.a == 0:
            return b
        return f"({_frac(self.a)} + {b})"


def lift(v):
    return v if isinstance(v, QD) else QD(v)


def _frac(q):
    q = Fraction(q)
    return str(q.numerator) if q.denominator == 1 else \
        f"{q.numerator}/{q.denominator}"


# ---------------------------------------------------------------- polynomials
# a polynomial is a list of QD coefficients, lowest power first, no trailing 0

def trim(p):
    p = [lift(c) for c in p]
    while p and p[-1].is_zero():
        p.pop()
    return p


def deg(p):
    return len(p) - 1


def padd(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else QD(0))
                 + (q[i] if i < len(q) else QD(0)) for i in range(n)])


def pmul(p, q):
    if not p or not q:
        return []
    out = [QD(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] = out[i + j] + a * b
    return trim(out)


def ppow(p, k):
    out = [QD(1)]
    for _ in range(k):
        out = pmul(out, p)
    return out


def pdivmod(p, q):
    p, q = trim(p), trim(q)
    quot = [QD(0)] * max(1, len(p) - len(q) + 1)
    r = list(p)
    while r and len(r) >= len(q):
        c = r[-1] / q[-1]
        k = len(r) - len(q)
        quot[k] = c
        r = trim([r[i] - (c * q[i - k] if 0 <= i - k < len(q) else QD(0))
                  for i in range(len(r))])
    return trim(quot), r


def pgcd(p, q):
    p, q = trim(p), trim(q)
    while q:
        p, q = q, pdivmod(p, q)[1]
    return monic(p) if p else p


def monic(p):
    return [c / p[-1] for c in p]


def evaluate(p, x):
    out = QD(0)
    for c in reversed(p):
        out = out * x + c
    return out


def text(p, x):
    """GRAMMAR.md text of a polynomial in x, highest power first."""
    parts = []
    for k in range(len(p) - 1, -1, -1):
        c = p[k]
        if c.is_zero():
            continue
        xs = "" if k == 0 else x if k == 1 else f"{x}^{k}"
        if not xs:
            parts.append(c.text())
        elif c == QD(1):
            parts.append(xs)
        elif c == QD(-1):
            parts.append(f"-{xs}")
        else:
            parts.append(f"{c.text()}*{xs}")
    return " + ".join(parts).replace("+ -", "- ") or "0"


# ---------------------------------------------------------------- reading

def read(t, x):
    """(N, Q): t = N/Q as rational polynomials in x, in lowest terms, Q
    monic. Refused not-rational unless t is a rational function of x with
    rational coefficients."""
    nz = FD._Normaliser(True)
    try:
        f = nz.norm(t)
    except Refused as r:
        raise Refusal("not-rational", r.message) from None
    xs = {i for i, a in enumerate(nz.atom_terms) if a == Var(x)}

    def poly(d):
        out = []
        for mono, c in d.items():
            if any(i not in xs for i, _ in mono):
                raise Refusal("not-rational", f"{show(t)} is not a "
                              f"rational function of {x} with rational "
                              "coefficients")
            k = sum(e for _, e in mono)
            out += [QD(0)] * (k + 1 - len(out))
            out[k] = out[k] + QD(c)
        return trim(out)
    n = poly(f.num)
    q = [QD(1)]
    for i, e in f.den.items():
        q = pmul(q, ppow(poly(nz.factor_polys[i]), e))
    if deg(q) > MAX_DEGREE or deg(n) > 3 * MAX_DEGREE:
        raise Refusal("too-large", f"degree above {MAX_DEGREE}")
    g = pgcd(n, q)
    if deg(g) > 0:
        n, q = pdivmod(n, g)[0], pdivmod(q, g)[0]
    lc = q[-1]
    return [c / lc for c in n], monic(q)


# ---------------------------------------------------------------- factoring

def _divisors(n):
    n = abs(n)
    small = [d for d in range(1, math.isqrt(n) + 1) if n % d == 0]
    return sorted(set(small + [n // d for d in small]))


def _rational_root(p):
    """A rational root of p (rational coefficients), or None."""
    if p[0].is_zero():
        return Fraction(0)
    lcm = math.lcm(*(c.a.denominator for c in p))
    ints = [int(c.a * lcm) for c in p]
    if max(abs(ints[0]), abs(ints[-1])) > ROOT_BOUND:
        return None
    for d in _divisors(ints[0]):
        for e in _divisors(ints[-1]):
            for r in (Fraction(d, e), Fraction(-d, e)):
                if evaluate(p, QD(r)).is_zero():
                    return r
    return None


def squarefree(q):
    """(m, r): q = m·r² with m a squarefree integer and r a positive
    rational; q > 0."""
    n = q.numerator * q.denominator
    m, r = 1, 1
    k = 2
    while k * k <= n:
        while n % (k * k) == 0:
            n //= k * k
            r *= k
        if n % k == 0:
            n //= k
            m *= k
        k += 1
    m *= n
    return m, Fraction(r, q.denominator)


def _is_square(q):
    if q < 0:
        return None
    a, b = math.isqrt(q.numerator), math.isqrt(q.denominator)
    return Fraction(a, b) if a * a == q.numerator and b * b == \
        q.denominator else None


def _quartic_q(p):
    """Two monic rational quadratics whose product is the monic rational
    quartic p, or None. The monic integer quartic L⁴·p(y/L) is searched
    (Gauss: its monic factors have integer coefficients), and mapped
    back."""
    L = math.lcm(*(c.a.denominator for c in p))
    ints = [int(p[k].a * L ** (4 - k)) for k in range(5)]
    a0, a1, a2, a3 = ints[0], ints[1], ints[2], ints[3]
    if a0 == 0 or abs(a0) > ROOT_BOUND:
        return None
    for b in _divisors(a0):
        for b in (b, -b):
            e = a0 // b
            if b != e:
                if (a1 - b * a3) % (e - b):
                    continue
                a = (a1 - b * a3) // (e - b)
                cs = [(a, a3 - a)]
            else:
                if a1 != b * a3:
                    continue
                disc = a3 * a3 - 4 * (a2 - 2 * b)
                if disc < 0 or math.isqrt(disc) ** 2 != disc:
                    continue
                s = math.isqrt(disc)
                if (a3 + s) % 2:
                    continue
                cs = [((a3 + s) // 2, (a3 - s) // 2)]
            for a, c in cs:
                if b + e + a * c == a2:
                    f = [QD(Fraction(b, L * L)), QD(Fraction(a, L)), QD(1)]
                    g = [QD(Fraction(e, L * L)), QD(Fraction(c, L)), QD(1)]
                    return f, g
    return None


def _quad_real(p):
    """A monic rational quadratic with a positive, non-square
    discriminant, as its two real linear factors over ℚ(√m)."""
    b, c = p[1].a, p[0].a
    D = b * b - 4 * c
    m, r = squarefree(D)
    h = QD(0, r / 2, m)
    return [QD(b / 2) - h, QD(1)], [QD(b / 2) + h, QD(1)]


def _biquadratic_real(p):
    """x⁴ + px² + q with q = s² > 0 and 2s − p = m·r² (m ≥ 2 squarefree):
    (x² + r√m·x + s)(x² − r√m·x + s), or None."""
    if not (p[1].is_zero() and p[3].is_zero()):
        return None
    pp, q = p[2].a, p[0].a
    s = _is_square(q)
    if not s or 2 * s - pp <= 0:
        return None
    m, r = squarefree(2 * s - pp)
    if m == 1:
        return None
    return ([QD(s), QD(0, r, m), QD(1)], [QD(s), QD(0, -r, m), QD(1)])


def irreducible(f, field):
    """True, False or None (not known) for a monic factor over the field."""
    if deg(f) <= 1:
        return True
    if deg(f) == 2:
        D = f[1] * f[1] - QD(4) * f[0]
        if D.rational():
            if D.a < 0:
                return True
            if field == "Q":
                return _is_square(D.a) is None
            return False
        return None
    return None


def factor_poly(q, field):
    """Monic q -> [(factor, power)], monic factors whose product with
    powers is q, and a note when something was left whole."""
    rest, found, note = list(q), {}, None

    def add(f):
        key = tuple((c.a, c.b, c.d) for c in f)
        found[key] = (f, found.get(key, (f, 0))[1] + 1)
    while deg(rest) >= 1:
        r = _rational_root(rest) if all(c.rational() for c in rest) \
            else None
        if r is None:
            break
        lin = [QD(-r), QD(1)]
        add(lin)
        rest = pdivmod(rest, lin)[0]
    todo = [rest] if deg(rest) >= 1 else []
    while todo:
        f = todo.pop()
        if deg(f) == 4 and all(c.rational() for c in f):
            split = _quartic_q(f)
            if split is None and field == "R":
                split = _biquadratic_real(f)
            if split:
                todo += list(split)
                continue
        if deg(f) == 2 and field == "R" and irreducible(f, "R") is False \
                and all(c.rational() for c in f):
            lins = _quad_real(f)
            m = lins[0][0].d
            used = {c.d for g, _ in found.values() for c in g if c.d} | {
                c.d for g in todo for c in g if c.d}
            if not used or used == {m}:
                for lin in lins:
                    add(lin)
                continue
            note = (f"{text(f, 'x')} splits over ℝ with √{m}; one radical "
                    "at a time, so it is left whole")
            add(f)
            continue
        if irreducible(f, field) is None:
            note = f"no further factor found for {text(f, 'x')}"
        add(f)
    out = sorted(found.values(), key=lambda fk: (
        deg(fk[0]), [(c.a, c.b) for c in fk[0]]))
    return out, note


# ---------------------------------------------------------------- checking

def radical(polys):
    ds = {c.d for p in polys for c in p if c.d}
    if len(ds) > 1:
        raise Refusal("too-large", "more than one radical")
    return ds.pop() if ds else 0


def check(lhs, rhs, d, quotients=False):
    """The kernel decides lhs = rhs: ring for polynomials, field for
    quotients, and field with (√d)² = d when a radical appears. Returns
    the check's name; raises Refusal unchecked when it does not."""
    facts = [(parse_term(f"(sqrt {d})^2", {}), parse_term(str(d), {}))] \
        if d else []
    try:
        if d or quotients:
            done = FD.field(lhs, rhs, facts)
        else:
            FD.ring(lhs, rhs)
            return "ring"
    except (FD.NotEqual, Refused) as e:
        raise Refusal("unchecked", f"the kernel did not accept it: {e}") \
            from None
    # field's equality holds where its divisors are nonzero: a divisor that
    # is zero modulo the fact would make the check vacuous
    for dv in done.divisors:
        try:
            FD.field(dv, parse_term("0", {}), facts)
        except FD.NotEqual:
            continue
        except Refused:
            pass
        raise Refusal("unchecked", f"the divisor {show(dv)} is zero")
    return f"field using sqrt_sq_val with a := {d}" if d else "field"


def _pow_text(f, k, x):
    s = text(f, x)
    base = s if deg(f) == 1 and len([c for c in f if not c.is_zero()]) \
        == 1 else f"({s})"
    return base if k == 1 else f"{base}^{k}"


def factor(t, x, field, whole_denominator=True):
    """FACTOR.md's /factor answer for a polynomial or rational function."""
    n, q = read(t, x)
    target = q
    of = "denominator"
    content = QD(1)
    if deg(q) == 0:
        target, of = n, "polynomial"
        if not n:
            raise Refusal("not-rational", "the zero polynomial")
        content, target = n[-1], monic(n)
    if deg(target) < 1:
        raise Refusal("not-rational", "a constant has no factors")
    fs, note = factor_poly(target, field)
    d = radical([f for f, _ in fs])
    parts = [_pow_text(f, k, x) for f, k in fs]
    product = "*".join(([content.text()] if content != QD(1) else [])
                       + parts)
    whole = text([c * content for c in target], x)
    how = check(parse_term(whole, {}), parse_term(product, {}), d)
    return {"of": of, "polynomial": show(parse_term(whole, {})),
            "content": content.text(),
            "factors": [{"term": show(parse_term(text(f, x), {})),
                         "power": k, "irreducible": irreducible(f, field)}
                        for f, k in fs],
            "product": show(parse_term(product, {})), "check": how,
            "note": note}


# ---------------------------------------------------------------- apart

def _solve(rows, rhs):
    """Gaussian elimination over ℚ(√d): a solution of rows·u = rhs (free
    unknowns 0), or None when inconsistent."""
    m = [list(r) + [b] for r, b in zip(rows, rhs)]
    n = len(rows[0]) if rows else 0
    piv, r = [], 0
    for c in range(n):
        k = next((i for i in range(r, len(m)) if not m[i][c].is_zero()),
                 None)
        if k is None:
            continue
        m[r], m[k] = m[k], m[r]
        inv = m[r][c].inv()
        m[r] = [v * inv for v in m[r]]
        for i in range(len(m)):
            if i != r and not m[i][c].is_zero():
                f = m[i][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        piv.append(c)
        r += 1
    if any(all(v.is_zero() for v in row[:-1]) and not row[-1].is_zero()
           for row in m):
        return None
    u = [QD(0)] * n
    for i, c in enumerate(piv):
        u[c] = m[i][-1]
    return u


def apart(t, x, field, ansatz=None):
    """FACTOR.md's /apart answer: t as its polynomial part plus partial
    fractions, recombined and checked by the kernel."""
    n, q = read(t, x)
    if deg(q) < 1:
        raise Refusal("not-rational", f"{show(t)} has no denominator in {x}")
    s, n = pdivmod(n, q) if deg(n) >= deg(q) else ([], n)
    if ansatz is None:
        fs, _ = factor_poly(q, field)
        for f, _ in fs:
            if not irreducible(f, field):
                hint = "; try over ℝ" if field == "Q" else ""
                raise Refusal("not-split", f"{text(f, x)} does not factor "
                              f"further over {'ℚ' if field == 'Q' else 'ℝ'}"
                              f"{hint}")
        dens = [(f, j, deg(f) == 2) for f, k in fs for j in range(1, k + 1)]
        den_polys = [(ppow(f, j), lin) for f, j, lin in dens]
    else:
        den_polys = []
        for a in ansatz:
            dn, dq = read(parse_term(a["den"], {}), x)
            if deg(dq) > 0:  # a den term is itself the denominator
                den_polys.append((dn and dq, a["numerator"] == "linear"))
            else:
                den_polys.append((monic(dn), a["numerator"] == "linear"))
    unknowns = []  # (den index, power of x in the numerator)
    cols = []
    for i, (dp, lin) in enumerate(den_polys):
        co, rem = pdivmod(q, dp)
        if rem:
            raise Refusal("no-solution", f"{text(dp, x)} does not divide "
                          f"the denominator {text(q, x)}")
        for k in ((0, 1) if lin else (0,)):
            unknowns.append((i, k))
            cols.append(pmul(co, [QD(0)] * k + [QD(1)]))
    size = max([len(c) for c in cols] + [len(n), 1])
    rows = [[c[r] if r < len(c) else QD(0) for c in cols]
            for r in range(size)]
    rhs = [n[r] if r < len(n) else QD(0) for r in range(size)]
    u = _solve(rows, rhs)
    if u is None:
        raise Refusal("no-solution", "these denominators cannot express "
                      "it: a factor or a power is missing")
    terms = []
    for i, (dp, lin) in enumerate(den_polys):
        num = [u[j] for j, (ii, k) in enumerate(unknowns) if ii == i]
        num = trim(num)
        if not num:
            continue
        terms.append(f"({text(num, x)})/({text(dp, x)})")
    d = radical([dp for dp, _ in den_polys] + [[v] for v in u] + [s])
    whole = " + ".join(([f"({text(s, x)})"] if s else []) + terms) or "0"
    how = check(t, parse_term(whole, {}), d, quotients=True)
    return {"polynomial": show(parse_term(text(s, x), {})) if s else None,
            "terms": [show(parse_term(tm, {})) for tm in terms],
            "sum": show(parse_term(whole, {})), "check": how}
