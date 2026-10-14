"""Limits at an infinite end (p1_expected section 20, E77, LIMIT_RULES).

Trusted (§15.2): int_improper replaces an integral by the value this module
computes, so a wrong limit here is a false `Proved`. It is kept small and
structural. Every rule is a textbook limit law, and every x-free fact a rule
relies on is either decided here from rational literals or returned as a
side condition for the kernel to emit, where discharge proves it, refutes it
(refusing the step) or admits it (E78). Nothing is assumed silently.

The caller also owes that the term is defined on the whole range (its
formers, and its C^0 premise), which the laws below use: a quotient's
denominator does not vanish there, ln's argument is positive there, and
so on.

lim(t, x, s, sign) -> (value, sides)
  s is +1 for x -> oo and -1 for x -> -oo. value is a Term (a finite limit),
  or POS or NEG. sides is a tuple of x-free Judgements (Rel or NonZero, no
  domain). sign(c) is the caller's guess at an x-free constant's sign, +1,
  -1 or None; it only chooses a branch, and the branch's premise is always
  in sides. Raises NoLimit when no rule applies. Never guesses.
"""

import complexes
import field as FD
from terms import (Add, App, Const, Div, Mul, Neg, NonZero, Num, Pow, Rel,
                   Term, Var, fv, lit, sort_of, trees)
from field import rational_value, ring_equal

POS, NEG = "+oo", "-oo"
_HALF_PI = Div(Const("pi"), Num(2))


class NoLimit(Exception):
    """No rule of LIMIT_RULES applies. A refusal, never a verdict."""


class _Ctx:
    def __init__(self, x, s, sign):
        self.x, self.s, self.sign, self.sides = x, s, sign, []

    def free(self, t):
        return self.x not in fv(t)

    def nonzero(self, c):
        """c # 0: decided here for a literal, else owed."""
        q = rational_value(c)
        if q is not None:
            if q == 0:
                raise NoLimit("a leading coefficient is 0")
            return
        self.sides.append(NonZero(c))

    def sign_of(self, c):
        """+1 or -1 for an x-free c, owing c > 0 or c < 0 unless c is a
        literal; NoLimit when neither is known."""
        q = rational_value(c)
        if q is not None:
            if q == 0:
                raise NoLimit("a sign is asked of 0")
            return 1 if q > 0 else -1
        g = self.sign(c)
        if g == 1:
            self.sides.append(Rel(">", c, Num(0)))
        elif g == -1:
            self.sides.append(Rel("<", c, Num(0)))
        else:
            raise NoLimit("the sign of a constant is not decided")
        return g


def lim(t, x, s, sign):
    if s not in (1, -1):
        raise ValueError("s is +1 or -1")
    if not isinstance(t, Term) or any(True for _ in trees(t)):
        raise NoLimit("an Int or D node")
    ctx = _Ctx(x, s, sign)
    value = _lim_c(t, ctx) if complexes.has_complex(t) else _lim(t, ctx)
    return value, tuple(ctx.sides)


# ---------------------------------------------------------------- rational
#
# Coefficient arithmetic folds rational literals and drops a literal 1, so
# that a coefficient reads as the learner wrote it (sqrt 2, not sqrt 2 * 1)
# and discharge can decide its sign. Each fold is an identity of ℚ.

def _fold(op, a, b=None):
    qa, qb = rational_value(a), (None if b is None else rational_value(b))
    if op == "neg":
        return lit(-qa) if qa is not None else Neg(a)
    if qa is not None and qb is not None and not (op == "div" and qb == 0):
        return lit({"add": qa + qb, "mul": qa * qb,
                    "div": qa / qb if qb else 0}[op])
    if op == "mul":
        return b if qa == 1 else a if qb == 1 else Mul(a, b)
    if op == "div":
        if qb == 1:
            return a
        return Num(1) if ring_equal(a, b) else Div(a, b)  # b # 0 is owed
    return Add(a, b)


def _pow(c, n):
    q = rational_value(c)
    if q is not None and (n >= 0 or q != 0):
        return lit(q ** n)
    return c if n == 1 else Pow(c, n)


def _rational(t, x):
    """t is built from x, x-free subterms, +, -, *, / and integer powers."""
    if x not in fv(t) or t == Var(x):
        return True
    if isinstance(t, Neg):
        return _rational(t.a, x)
    if isinstance(t, (Add, Mul, Div)):
        return _rational(t.a, x) and _rational(t.b, x)
    if isinstance(t, Pow):
        return _rational(t.base, x)
    return False


def _lead(t, ctx):
    """(c, k): t / (c * x^k) -> 1, every c returned owing c # 0."""
    if ctx.free(t):
        return t, 0
    if t == Var(ctx.x):
        return Num(1), 1
    if isinstance(t, Neg):
        c, k = _lead(t.a, ctx)
        return _fold("neg", c), k
    if isinstance(t, Mul):
        (c1, k1), (c2, k2) = _lead(t.a, ctx), _lead(t.b, ctx)
        return _fold("mul", c1, c2), k1 + k2
    if isinstance(t, Div):
        (c1, k1), (c2, k2) = _lead(t.a, ctx), _lead(t.b, ctx)
        ctx.nonzero(c2)
        return _fold("div", c1, c2), k1 - k2
    if isinstance(t, Pow):
        c, k = _lead(t.base, ctx)
        if t.n < 0:
            ctx.nonzero(c)
        return _pow(c, t.n), k * t.n
    if isinstance(t, Add):
        (c1, k1), (c2, k2) = _lead(t.a, ctx), _lead(t.b, ctx)
        ctx.nonzero(c1)  # each summand's leading term is a true one
        ctx.nonzero(c2)
        if k1 != k2:
            return (c1, k1) if k1 > k2 else (c2, k2)
        c = _fold("add", c1, c2)
        ctx.nonzero(c)  # equal degree: they must not cancel
        return c, k1
    raise NoLimit("not rational")  # unreachable after _rational


def _from_lead(t, ctx):
    c, k = _lead(t, ctx)
    ctx.nonzero(c)
    if k == 0:
        return c
    if k < 0:
        return Num(0)
    g = ctx.sign_of(c) * (ctx.s ** k)
    return POS if g > 0 else NEG


# ---------------------------------------------------------------- the laws

def _inf(v):
    return v in (POS, NEG)


def _flip(v):
    return NEG if v == POS else POS


def _lim(t, ctx):
    if ctx.free(t):
        return t
    if _rational(t, ctx.x):
        return _from_lead(t, ctx)
    if isinstance(t, Neg):
        a = _lim(t.a, ctx)
        return _flip(a) if _inf(a) else Neg(a)
    if isinstance(t, Add):
        a, b = _lim(t.a, ctx), _lim(t.b, ctx)
        if _inf(a) and _inf(b):
            if a != b:
                raise NoLimit("oo - oo")
            return a
        if _inf(a) or _inf(b):
            return a if _inf(a) else b
        return Add(a, b)
    if isinstance(t, Mul):
        a, b = _lim(t.a, ctx), _lim(t.b, ctx)
        if _inf(a) and _inf(b):
            return POS if a == b else NEG
        if _inf(a) or _inf(b):
            v, fin = (a, b) if _inf(a) else (b, a)
            return v if ctx.sign_of(fin) > 0 else _flip(v)
        return Mul(a, b)
    if isinstance(t, Div):
        a, b = _lim(t.a, ctx), _lim(t.b, ctx)
        if _inf(b):
            if _inf(a):
                raise NoLimit("oo / oo")
            return Num(0)
        if _inf(a):
            return a if ctx.sign_of(b) > 0 else _flip(a)
        ctx.nonzero(b)
        return Div(a, b)
    if isinstance(t, Pow):
        a, n = _lim(t.base, ctx), t.n
        if _inf(a):
            if n == 0:
                return Num(1)
            if n < 0:
                return Num(0)
            return NEG if (a == NEG and n % 2) else POS
        if n < 0:
            ctx.nonzero(a)
        return Pow(a, n)
    if isinstance(t, App):
        return _app(t.fn, _lim(t.arg, ctx), ctx)
    raise NoLimit(f"no limit law for {type(t).__name__}")


def _app(fn, a, ctx):
    if _inf(a):
        if fn == "exp":
            return POS if a == POS else Num(0)
        if fn in ("ln", "sqrt") and a == POS:
            return POS
        if fn == "atan":
            return _HALF_PI if a == POS else Neg(_HALF_PI)
        raise NoLimit(f"{fn} at an infinity")
    if fn in ("sin", "cos", "atan", "exp"):
        return App(fn, a)
    if fn == "ln":
        ctx.sides.append(Rel(">", a, Num(0)))
        return App(fn, a)
    if fn == "sqrt":
        ctx.sides.append(Rel(">=", a, Num(0)))
        return App(fn, a)
    raise NoLimit(f"no limit law for {fn}")


# ---------------------------------------------------------------- over C
#
# p1_expected E179. The real evaluator never sees complex structure: it
# would read i as an unknown real constant. Every law below is a textbook
# limit law over C, for a finite limit; an infinite part is NoLimit.

def _zero(v):
    try:
        return FD.ring_is_zero(v)
    except Exception:  # noqa: BLE001 -- not known zero: kept as it is
        return False


def _finite(v):
    if _inf(v):
        raise NoLimit("a complex limit that is not finite")
    return v


def _lim_c(t, ctx):
    if ctx.free(t):
        return t
    if complexes.real_form(t):
        return _lim(t, ctx)
    if sort_of(t) == "C" and isinstance(t, (Add, Neg, Mul, Div)):
        mark = len(ctx.sides)
        try:  # the laws that combine finite limits first
            return _combine(t, ctx)
        except NoLimit:  # then the parts (an infinite part diverges) or
            del ctx.sides[mark:]  # the modulus, with only their own sides
            return _lim_parts_or_modulus(t, ctx)
    return _combine(t, ctx)


def _combine(t, ctx):
    # Each combination folds a zero, by an identity: 0 + b = b, 0*b = 0,
    # 0/b = 0 (b # 0 still owed), re 0 = im 0 = conj 0 = 0, and re, conj of
    # a Real value are the value, im of one is 0.
    if isinstance(t, App) and t.fn in ("re", "im", "conj"):  # they commute
        a = _finite(_lim_c(t.arg, ctx))
        if _zero(a) or t.fn == "im" and sort_of(a) == "R":
            return Num(0)
        return a if sort_of(a) == "R" else App(t.fn, a)
    if isinstance(t, Neg):
        a = _finite(_lim_c(t.a, ctx))
        return Num(0) if _zero(a) else Neg(a)
    if isinstance(t, Add):
        a, b = _finite(_lim_c(t.a, ctx)), _finite(_lim_c(t.b, ctx))
        return b if _zero(a) else a if _zero(b) else Add(a, b)
    if isinstance(t, Mul):
        a, b = _finite(_lim_c(t.a, ctx)), _finite(_lim_c(t.b, ctx))
        return Num(0) if _zero(a) or _zero(b) else Mul(a, b)
    if isinstance(t, Div):
        a, b = _finite(_lim_c(t.a, ctx)), _finite(_lim_c(t.b, ctx))
        ctx.sides.append(NonZero(b))  # realified where it is emitted
        return Num(0) if _zero(a) else Div(a, b)
    if sort_of(t) == "C":
        return _lim_parts_or_modulus(t, ctx)
    raise NoLimit(f"no limit law over C for {type(t).__name__}")


def _lim_parts_or_modulus(t, ctx):
    """Both parts' limits when both are finite; else modulus_to_zero:
    (re G)^2 + (im G)^2 -> 0 gives G -> 0 (E179)."""
    a, b = (complexes._real(p) for p in complexes.split(t))
    try:
        va, vb = _lim(a, ctx), _lim(b, ctx)
        if _inf(va) or _inf(vb):  # E182: a part diverges, so G does
            return POS
        return complexes.join((va, vb))
    except NoLimit:
        pass
    g = Add(Pow(a, 2), Pow(b, 2))
    r = _reduced(g, ctx)
    v = _lim(r, ctx)
    if _inf(v) or not FD.ring_is_zero(v):
        raise NoLimit("neither the parts nor the modulus has a limit law")
    return Num(0)


def _reduced(g, ctx):
    """g reduced by field with pyth_cos, (cos u)^2 == 1 - (sin u)^2, at
    each cos atom: the reduction is an offer, kept only when the trusted
    field proves it equal to g, its divisors then owed as sides."""
    import entries
    from terms import subst
    st = entries.ENTRIES["pyth_cos"].statement
    atoms = {}
    for n in _nodes(g):
        if isinstance(n, App) and n.fn == "cos":
            atoms.setdefault(n.arg, None)
    facts = [(subst(st.lhs, {"u": u}), subst(st.rhs, {"u": u}))
             for u in atoms]
    try:
        ok = FD.field(g, Num(0), facts)
        ctx.sides.extend(NonZero(d) for d in ok.divisors)
        return Num(0)
    except FD.NotEqual as e:
        import residual
        r = residual.residual_term(e.residual)
    except Exception:  # noqa: BLE001 -- no reduction: read g itself
        return g
    try:
        ok = FD.field(g, r, facts)
    except Exception:  # noqa: BLE001 -- an offer field cannot prove
        return g
    ctx.sides.extend(NonZero(d) for d in ok.divisors)
    return r


def _nodes(t):
    todo = [t]
    while todo:
        n = todo.pop()
        yield n
        if isinstance(n, Term):
            from terms import children
            todo.extend(k for _, k in children(n) if isinstance(k, Term))
