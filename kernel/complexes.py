"""Complex terms as pairs of real ones (COMPLEX.md §4; p1_expected E167,
E168).

Trusted (DESIGN.md §15.2): `split` is the one place the kernel reads a
complex number, and everything downstream of it (ring, field, discharge,
the regularity checker) sees only real terms. Its identities are the
textbook ones, each valid wherever the term is defined, and the term's own
formers owe that definedness where it entered (E171).

A part is a Term, or None for a part known to be zero, so that a term
with no complex structure splits to (itself, None) unchanged and a real
goal's keys are the keys it always had. The real atoms a split may hold
are `re z` and `im z` of a CVar z, and `arg[theta](w)` of any w, which
field keys by w's own split.
"""

from terms import (Add, App, Branch, Call, Const, CVar, Deriv, Div, Integral,
                   Interval, MVar, Mul, Neg, NonZero, Num, Pow, Refused, Reg,
                   Rel, RPow, Term, Var, children, sort_of)

I = Const("i")
_COMPLEX_APPS = frozenset(("re", "im", "conj"))


def has_complex(x):
    """Whether x (a Term, judgement, interval or tuple) holds complex
    structure that split must remove: i, a CVar outside re/im, log or
    sqrt[theta], conj, or re/im of anything but a CVar. The real atoms a
    split leaves (re z, im z, arg[theta](w)) are not complex structure, so
    split is idempotent on its own output."""
    return not real_form(x)


# -- pair arithmetic; None is zero

def _add(a, b):
    return b if a is None else a if b is None else Add(a, b)


def _neg(a):
    return None if a is None else Neg(a)


def _sub(a, b):
    return _add(a, _neg(b))


def _mul(a, b):
    if a is None or b is None:
        return None
    if a == Num(1):
        return b
    return a if b == Num(1) else Mul(a, b)


def _real(a):
    return Num(0) if a is None else a


def _pmul(x, y):
    (a, b), (c, d) = x, y
    return (_sub(_mul(a, c), _mul(b, d)), _add(_mul(a, d), _mul(b, c)))


def _psq(x):
    return _pmul(x, x)


def _ppow(x, n):
    """x^n for n >= 1, by squaring, so the tree grows with log n."""
    out = None
    while n:
        if n & 1:
            out = x if out is None else _pmul(out, x)
        n >>= 1
        if n:
            x = _psq(x)
    return out


def _norm2(x):
    """a^2 + b^2 of a pair (b None: a^2)."""
    a, b = x
    return _add(Pow(_real(a), 2), None if b is None else Pow(b, 2))


def _pdiv(x, y):
    (p, q), (r, s) = x, y
    if s is None:  # a real divisor
        return (None if p is None else Div(p, _real(r)),
                None if q is None else Div(q, _real(r)))
    d = _norm2(y)
    re = _add(_mul(p, r), _mul(q, s))
    im = _sub(_mul(q, r), _mul(p, s))
    return (None if re is None else Div(re, d), None if im is None else Div(im, d))


def _zero(t):
    """t is ring-zero: the trusted field, read lazily (field imports this
    module)."""
    import field as FD
    return FD.ring_is_zero(t)


# -- split

def split(t):
    """(re, im) of a term of either sort, each a real Term or None for
    zero (E167). Raises Refused 'complex-unsplit' on a node no K1 rule
    covers, which check_goal's sort rules keep from arising."""
    k = type(t)
    if k is Const and t.name == "i":
        return (None, Num(1))
    if k is CVar:
        return (App("re", t), App("im", t))
    if not has_complex(t):
        return (t, None)
    if k is Neg:
        a, b = split(t.a)
        return (_neg(a), _neg(b))
    if k is Add:
        (a, b), (c, d) = split(t.a), split(t.b)
        return (_add(a, c), _add(b, d))
    if k is Mul:
        return _pmul(split(t.a), split(t.b))
    if k is Div:
        return _pdiv(split(t.a), split(t.b))
    if k is Pow:
        x = split(t.base)
        if t.n == 0:
            return (Num(1), None)
        if t.n > 0:
            return _ppow(x, t.n)
        return _pdiv((Num(1), None), _ppow(x, -t.n))
    if k is RPow:  # base Real (D20); a Complex exponent: exp(e*ln b)
        return split(App("exp", Mul(t.exp, App("ln", t.base))))
    if k is App:
        return _split_app(t)
    if k is Branch:
        return _split_branch(t)
    if k in (Call, Integral, Deriv, MVar, Var, Num, Const):
        raise Refused("complex-unsplit", f"no K1 rule splits {type(t).__name__}")
    raise Refused("complex-unsplit", f"not a term: {t!r}")


def _split_app(t):
    fn = t.fn
    if fn == "re":
        return (_real(split(t.arg)[0]), None)
    if fn == "im":
        return (_real(split(t.arg)[1]), None)
    if fn == "conj":
        a, b = split(t.arg)
        return (a, _neg(b))
    a, b = split(t.arg)
    if b is None:  # a real argument holding complex structure: re z, abs z
        return (App(fn, _real(a)), None)
    if fn == "abs":  # the modulus
        return (App("sqrt", _norm2((a, b))), None)
    a = _real(a)
    if fn == "exp":
        ea = None if _zero(a) else App("exp", a)
        return ((App("cos", b) if ea is None else Mul(ea, App("cos", b))),
                (App("sin", b) if ea is None else Mul(ea, App("sin", b))))
    if fn == "sin":  # sin a cosh b + i cos a sinh b
        return (Mul(App("sin", a), App("cosh", b)),
                Mul(App("cos", a), App("sinh", b)))
    if fn == "cos":  # cos a cosh b - i sin a sinh b
        return (Mul(App("cos", a), App("cosh", b)),
                Neg(Mul(App("sin", a), App("sinh", b))))
    if fn == "sinh":  # sinh a cos b + i cosh a sin b
        return (Mul(App("sinh", a), App("cos", b)),
                Mul(App("cosh", a), App("sin", b)))
    if fn == "cosh":  # cosh a cos b + i sinh a sin b
        return (Mul(App("cosh", a), App("cos", b)),
                Mul(App("sinh", a), App("sin", b)))
    if fn == "tan":
        return _pdiv(_split_app(App("sin", t.arg)), _split_app(App("cos", t.arg)))
    if fn == "tanh":
        return _pdiv(_split_app(App("sinh", t.arg)),
                     _split_app(App("cosh", t.arg)))
    raise Refused("sort-real-only", f"{fn} takes a real argument")


def _split_branch(t):
    if t.fn == "arg":  # an opaque real atom
        return (t, None)
    if t.fn == "log":  # ln(a^2 + b^2)/2 + i arg[theta] w
        return (Div(App("ln", _norm2(split(t.arg))), Num(2)),
                Branch("arg", t.theta, t.arg))
    # sqrt[theta] w = exp(log[theta](w)/2)
    return split(App("exp", Div(Branch("log", t.theta, t.arg), Num(2))))


def join(pair):
    """re + i*im as one term, for display and for `parts` (E170)."""
    a, b = pair
    if b is None:
        return _real(a)
    neg = type(b) is Neg  # (-x)*i written -(x*i), so a - x*i prints
    im = Mul(b.a if neg else b, I)
    if a is None:
        return Neg(im) if neg else im
    return Add(a, Neg(im) if neg else im)


def realify(t):
    """The real part of a Real-sorted term: the term itself when it holds
    no complex structure (E168)."""
    if not has_complex(t):
        return t
    if sort_of(t) != "R":
        raise Refused("complex-key", "a complex term where a real one is "
                      "needed")
    return _real(split(t)[0])


# -- judgements (E168): every key and domain the kernel decides is real

def realify_judgement(j):
    """A tuple of real judgements equivalent to j, each with a realified
    domain. A judgement with no complex structure is (j,) unchanged."""
    if not has_complex(j):
        return (j,)
    dom = realify_dom(j.dom)
    if isinstance(j, Rel):
        if j.op == "==" and "C" in (sort_of(j.lhs), sort_of(j.rhs)):
            (a, b), (c, d) = split(j.lhs), split(j.rhs)
            return (Rel("==", _real(a), _real(c), dom),
                    Rel("==", _real(b), _real(d), dom))
        return (Rel(j.op, realify(j.lhs), realify(j.rhs), dom),)
    if isinstance(j, NonZero):
        if sort_of(j.e) == "C":
            a, b = split(j.e)
            return (NonZero(_real(_norm2((a, b))) if b is not None
                            else _real(a), dom),)
        return (NonZero(realify(j.e), dom),)
    if isinstance(j, Reg):
        return (Reg(realify(j.e), j.k, dom),)
    raise Refused("complex-key", f"not a judgement: {j!r}")


def realify_dom(items):
    out = []
    for it in items:
        if isinstance(it, Interval):  # Real ends (D20), realified (E175)
            out.append(Interval(it.var, realify(it.lo) if isinstance(
                it.lo, Term) else it.lo, it.lo_closed, realify(it.hi)
                if isinstance(it.hi, Term) else it.hi, it.hi_closed))
        else:
            out.extend(realify_judgement(it))
    return tuple(out)


def real_form(x):
    """True when x holds no complex structure outside the real atoms a
    split may leave: re and im of a CVar, and arg[theta](w) of anything.
    _emit's invariant (E168)."""
    todo = [x]
    while todo:
        t = todo.pop()
        if isinstance(t, tuple):
            todo.extend(t)
            continue
        if type(t) is App and t.fn in ("re", "im") and type(t.arg) is CVar:
            continue
        if type(t) is Branch and t.fn == "arg":
            continue
        if isinstance(t, (CVar, Branch)) or (type(t) is Const and
                                              t.name == "i"):
            return False
        if type(t) is App and t.fn in _COMPLEX_APPS:
            return False
        if isinstance(t, (Rel, NonZero, Reg)):
            todo.extend((t.lhs, t.rhs) if isinstance(t, Rel) else (t.e,))
            todo.extend(t.dom)
        elif isinstance(t, Interval):
            todo.extend(e for e in (t.lo, t.hi) if isinstance(e, Term))
        elif isinstance(t, Term):
            todo.extend(k for _, k in children(t))
    return True
