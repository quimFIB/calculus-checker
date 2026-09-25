"""What an integrand is, as a function of x: the recognizer's eyes.

Untrusted (tier 2, DESIGN.md §16.1). Everything here reads terms through
the kernel's own `field` normal form (RECOGNIZER.md, "Normalisation
first"): `x*(x+1)` and `x^2 + x` are one polynomial, and a divisor is kept
as a factor. It asks `field` whether a ratio is constant, which is how
f′/f and a chain-rule substitution are seen. Nothing it returns enters a
proof.

**Sign convention** (as the spike had it). A symbol other than x is taken
as positive, which is what the course's problems declare (`k > 0`,
`m > 0`). A coefficient's sign is known when every term of it agrees, or
when it is a closed number that evaluates; otherwise it is unknown (0),
and rows read unknown as "not ruled out": the recognizer suggests, the
kernel decides.
"""

import math
import os
import sys
from dataclasses import fields, replace

KERNEL = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))), "kernel")
if KERNEL not in sys.path:
    sys.path.insert(0, KERNEL)

import field as FD  # noqa: E402
import poly as P  # noqa: E402
from residual import poly_term  # noqa: E402
from terms import (Add, App, Call, Const, Div, Mul, Neg, Num, Pow,  # noqa: E402
                   RPow, Term, Var, fv, lit)

ZERO, ONE = Num(0), Num(1)
LINEAR_FNS = ("sin", "cos", "exp", "sinh", "cosh")


class Unreadable(Exception):
    """A term the recognizer cannot read (a refusal, an unknown node)."""


# ---------------------------------------------------------------- terms

def depends(t, x):
    return x in fv(t)


def subterms(t):
    """Every Term in t, pre-order."""
    yield t
    for f in fields(t) if isinstance(t, Term) else ():
        v = getattr(t, f.name)
        for k in (v if isinstance(v, tuple) else (v,)):
            if isinstance(k, Term):
                yield from subterms(k)


def replace_term(t, old, new):
    """t with every subterm equal to `old` replaced by `new`."""
    if t == old:
        return new
    if not isinstance(t, Term):
        return t
    changes = {}
    for f in fields(t):
        v = getattr(t, f.name)
        if isinstance(v, Term):
            w = replace_term(v, old, new)
            if w is not v:
                changes[f.name] = w
        elif isinstance(v, tuple):
            w = tuple(replace_term(k, old, new) for k in v)
            if w != v:
                changes[f.name] = w
    return replace(t, **changes) if changes else t


def mul(*ts):
    out = None
    for t in ts:
        out = t if out is None else Mul(out, t)
    return ONE if out is None else out


def sqrt(t):
    return App("sqrt", t)


# ---------------------------------------------------------------- derivative

def _d_app(fn, u):
    """d/du fn(u), as a Term in u."""
    rules = {
        "sin": lambda: App("cos", u),
        "cos": lambda: Neg(App("sin", u)),
        "tan": lambda: Add(ONE, Pow(App("tan", u), 2)),
        "exp": lambda: App("exp", u),
        "ln": lambda: Div(ONE, u),
        "sqrt": lambda: Div(ONE, Mul(Num(2), sqrt(u))),
        "asin": lambda: Div(ONE, sqrt(Add(ONE, Neg(Pow(u, 2))))),
        "acos": lambda: Neg(Div(ONE, sqrt(Add(ONE, Neg(Pow(u, 2)))))),
        "atan": lambda: Div(ONE, Add(ONE, Pow(u, 2))),
        "sinh": lambda: App("cosh", u),
        "cosh": lambda: App("sinh", u),
        "tanh": lambda: Add(ONE, Neg(Pow(App("tanh", u), 2))),
        "asinh": lambda: Div(ONE, sqrt(Add(Pow(u, 2), ONE))),
        "acosh": lambda: Div(ONE, sqrt(Add(Pow(u, 2), Neg(ONE)))),
        "atanh": lambda: Div(ONE, Add(ONE, Neg(Pow(u, 2)))),
    }
    if fn not in rules:
        raise Unreadable(f"no derivative rule for {fn}")
    return rules[fn]()


def deriv(t, x):
    """D[x] t as a Term, unsimplified. Untrusted and wider than the
    kernel's deriv (every builtin but abs); a wrong answer here only makes
    a row match or miss."""
    if not depends(t, x):
        return ZERO
    k = type(t)
    if k is Var:
        return ONE
    if k is Neg:
        return Neg(deriv(t.a, x))
    if k is Add:
        return Add(deriv(t.a, x), deriv(t.b, x))
    if k is Mul:
        return Add(Mul(deriv(t.a, x), t.b), Mul(t.a, deriv(t.b, x)))
    if k is Div:
        return Div(Add(Mul(deriv(t.a, x), t.b), Neg(Mul(t.a, deriv(t.b, x)))),
                   Pow(t.b, 2))
    if k is Pow:
        if t.n == 0:
            return ZERO
        return Mul(Mul(lit(t.n), Pow(t.base, t.n - 1)), deriv(t.base, x))
    if k is RPow:
        return Mul(t, Add(Mul(deriv(t.exp, x), App("ln", t.base)),
                          Div(Mul(t.exp, deriv(t.base, x)), t.base)))
    if k is App:
        return Mul(_d_app(t.fn, t.arg), deriv(t.arg, x))
    raise Unreadable(f"no derivative for {type(t).__name__}")


def free_of(t, x):
    """Whether t is free of x: syntactically, or by `field` deciding
    D[x] t ≐ 0. Any refusal reads as no."""
    if not depends(t, x):
        return True
    try:
        FD.field(deriv(t, x), ZERO)
        return True
    except Exception:  # NotEqual, Refused, Unreadable, a bound hit
        return False


# ---------------------------------------------------------------- signs

_POSITIVE_FNS = ("sqrt", "exp", "cosh")


def value(t):
    """The float value of a closed term, or None."""
    try:
        return _value(t)
    except (ArithmeticError, ValueError, TypeError, OverflowError):
        return None


def _value(t):
    k = type(t)
    if k is Num:
        return float(t.n)
    if k is Const:
        return math.pi if t.name == "pi" else math.e
    if k is Neg:
        return -_value(t.a)
    if k is Add:
        return _value(t.a) + _value(t.b)
    if k is Mul:
        return _value(t.a) * _value(t.b)
    if k is Div:
        return _value(t.a) / _value(t.b)
    if k is Pow:
        return _value(t.base) ** t.n
    if k is RPow:
        return _value(t.base) ** _value(t.exp)
    if k is App and hasattr(math, t.fn):
        return getattr(math, t.fn)(_value(t.arg))
    if k is App and t.fn == "ln":
        return math.log(_value(t.arg))
    raise TypeError("not closed")


def _atom_sign(t):
    if isinstance(t, (Var, Const, RPow)):
        return 1
    if isinstance(t, App) and t.fn in _POSITIVE_FNS:
        return 1
    return 0


def poly_sign(p, atoms):
    """+1, -1, or 0 for unknown: the sign of p over `atoms` (Terms free of
    x) under the sign convention, or its value when p is closed."""
    if not p:
        return 0
    vals = [value(a) for a in atoms]
    used = {i for m in p for i, _ in m}
    if all(vals[i] is not None for i in used):
        v = sum(float(c) * math.prod(vals[i] ** e for i, e in m)
                for m, c in p.items())
        return 0 if abs(v) < 1e-12 else (1 if v > 0 else -1)
    signs = set()
    for m, c in p.items():
        s = 1 if c > 0 else -1
        for i, e in m:
            s *= 1 if e % 2 == 0 else _atom_sign(atoms[i])
        signs.add(s)
    return signs.pop() if len(signs) == 1 else 0


# ---------------------------------------------------------------- polynomials

class InX:
    """A polynomial in x whose coefficients are polynomials in atoms free
    of x, over a denominator free of x whose sign is `den_sign`."""

    def __init__(self, coeffs, atoms, den_sign=1):
        self.coeffs, self.atoms, self.den_sign = coeffs, atoms, den_sign

    @property
    def degree(self):
        return max(self.coeffs, default=-1)

    def coeff(self, d):
        return self.coeffs.get(d, {})

    def sign(self, d):
        return poly_sign(self.coeff(d), self.atoms) * self.den_sign

    def completed_sign(self):
        """For a quadratic a x² + b x + c, the sign of c − b²/4a."""
        a, b, c = self.coeff(2), self.coeff(1), self.coeff(0)
        if not b:
            return self.sign(0)
        disc = P.sub(P.scale(P.mul(a, c), 4), P.mul(b, b))  # 4ac − b²
        return poly_sign(disc, self.atoms) * poly_sign(a, self.atoms)

    def term(self, x):
        """The polynomial as a Term, x^d as its own factor."""
        xi = len(self.atoms)
        p = {}
        for d, c in self.coeffs.items():
            for m, v in c.items():
                p[tuple(sorted(m + (((xi, d),) if d else ())))] = v
        return poly_term(p, list(self.atoms) + [Var(x)])


def _split_by(p, xi):
    out = {}
    for m, c in p.items():
        d = dict(m).get(xi, 0)
        rest = tuple((i, e) for i, e in m if i != xi)
        out.setdefault(d, {})[rest] = c
    return out


def _inverse(t):
    """1/t with each power's exponent kept: 1/(b^n) is b^(-n)."""
    k = type(t)
    if k is Pow:
        return Pow(t.base, -t.n)
    if k is Mul:
        return Mul(_inverse(t.a), _inverse(t.b))
    if k is Neg:
        return Neg(_inverse(t.a))
    return Pow(t, -1)


def as_powers(t):
    """t with every a/b read as a·b^(-1), so the normal form keeps
    (x + 1)^2 in a denominator as the factor x + 1 twice, not as the
    expanded x^2 + 2x + 1 (RECOGNIZER.md: each divisor kept as a factor)."""
    if not isinstance(t, Term):
        return t
    if type(t) is Div:
        a, b = as_powers(t.a), as_powers(t.b)
        return _inverse(b) if a == ONE else Mul(a, _inverse(b))
    changes = {}
    for f in fields(t):
        v = getattr(t, f.name)
        if isinstance(v, Term):
            w = as_powers(v)
            if w is not v:
                changes[f.name] = w
    return replace(t, **changes) if changes else t


class Shape:
    """A term's field normal form, read as a function of x.

    `num` is a polynomial in the normaliser's atoms; `den` maps factor ids
    to exponents. `dep` is the set of atom indices whose term holds x
    (x's own included); `xi` is x's index, or None.
    """

    def __init__(self, t, x):
        self.t, self.x = t, x
        nz = FD._Normaliser(True)
        try:
            f = nz.norm(as_powers(t))
        except Exception as e:  # Refused, a bound, an unreadable node
            raise Unreadable(str(e)) from None
        self.nz, self.num, self.den = nz, f.num, f.den
        self.atoms = nz.atom_terms
        self.xi = nz.atom_index.get(Var(x))
        self.dep = {i for i, a in enumerate(self.atoms) if depends(a, x)}

    # -- the denominator

    def factor(self, fid):
        return self.nz.factor_polys[fid]

    def factor_dep(self, fid):
        return any(i in self.dep for m in self.factor(fid) for i, _ in m)

    @property
    def den_x(self):
        """The denominator's factors that hold x: {fid: exponent}."""
        return {f: e for f, e in self.den.items() if self.factor_dep(f)}

    def den_free_sign(self):
        s = 1
        for f, e in self.den.items():
            if not self.factor_dep(f) and e % 2:
                s *= poly_sign(self.factor(f), self.atoms)
        return s

    def factor_term(self, fid):
        return poly_term(self.factor(fid), self.atoms)

    # -- the numerator

    def num_xparts(self):
        """The set of x-dependent parts of the numerator's monomials, each
        a tuple of (atom index, exponent)."""
        return {tuple((i, e) for i, e in m if i in self.dep) for m in self.num}

    def separable(self):
        """The numerator's x-dependent part as {atom: exponent} when every
        monomial shares it (the numerator is c · that), else None."""
        parts = self.num_xparts()
        return dict(parts.pop()) if len(parts) == 1 else None

    def x_only(self, fids=None):
        """Whether x is the only atom holding x (in the numerator and the
        given factors, all of the denominator's by default)."""
        fids = self.den if fids is None else fids
        used = {i for m in self.num for i, _ in m}
        used |= {i for f in fids for m in self.factor(f) for i, _ in m}
        return all(i == self.xi or i not in self.dep for i in used)

    def num_in_x(self):
        if self.xi is None:
            return InX({0: self.num} if self.num else {}, self.atoms)
        return InX(_split_by(self.num, self.xi), self.atoms)

    def den_in_x(self):
        d = self.nz.expand(self.den_x)
        if self.xi is None:
            return InX({0: d}, self.atoms)
        return InX(_split_by(d, self.xi), self.atoms)

    def atom(self, i):
        return self.atoms[i]


def shape(t, x):
    try:
        return Shape(t, x)
    except Unreadable:
        return None


def poly_in(t, x):
    """t as an InX, or None: x occurs only polynomially, over a
    denominator free of x."""
    s = shape(t, x)
    if s is None or s.den_x or not s.x_only():
        return None
    q = s.num_in_x()
    q.den_sign = s.den_free_sign()
    return q


def is_linear(t, x):
    q = poly_in(t, x)
    return q is not None and q.degree == 1


def sqrt_quadratic(root, x):
    """For √(u), u read with any monomial denominator in x cleared
    (revision 8): the numerator as an InX when it is quadratic, else None."""
    s = shape(root.arg, x)
    if s is None:
        return None
    for f in s.den_x:
        p = s.factor(f)
        if not (len(p) == 1 and next(iter(p)) == ((s.xi, 1),)):
            return None
    if not s.x_only():
        return None
    q = s.num_in_x()
    q.den_sign = s.den_free_sign()
    return q if q.degree == 2 else None


def sqrt_subterms(t, x):
    return [s for s in subterms(t)
            if type(s) is App and s.fn == "sqrt" and depends(s.arg, x)]


def summands(t):
    """The top-level summands of t, Neg pushed onto each."""
    if type(t) is Add:
        return summands(t.a) + summands(t.b)
    if type(t) is Neg:
        return [Neg(s) for s in summands(t.a)]
    return [t]
