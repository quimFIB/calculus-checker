"""The `closed` answer schema: the whitelist (DESIGN.md §9; p1_expected E23)
and the evaluated-form check (p1_expected E27, EVALUATED_RULE).

Untrusted: §9 puts the schema checker outside the trusted base. A
permissive schema gives a weaker true theorem, never a false one. The
trusted scope check (E19) runs before this in `close`, so bound names are
not this module's business and Var can be admitted.

Every P1 goal carries `answer schema closed` with no `+ f` extension. When a
problem adds one, `closed_ok` takes the extra declared symbols.

**E27, fully evaluated.** `check_evaluated` is the last check in `close`,
after the whitelist, the value's formers, the check and check_goal on the
theorem, so the value it sees was already proved equal to the goal's left
side, and every other refusal wins. It only reads the value: it never
rewrites it, builds a theorem or touches kernel state, so a bug here can
refuse a good answer or accept an unevaluated one, and neither is a false
theorem. 'Fully evaluated' is a property, the absence of a redex, never a
comparison with a canonical form:

  (a) no subterm can still be evaluated by an equation entry in force
      (entries.ENTRIES, read at the time of the check), matched as rewrite
      matches (REWRITE_RULE steps 3-4: an application through the ring
      normal form of its argument), with EVALUATED_RULE's reading for each
      schema entry (`_READINGS`);
  (b) no unreduced literal arithmetic, by four local tests b1-b4 over sum
      and product flattenings, none of which depends on the order of
      summands or factors.

(a) is searched over the whole value first, in pre-order (terms.children),
trying the entries in ENTRIES order at each node; only if nothing counts is
(b) searched, in pre-order, trying b1 to b4 at each node. The first
offender is carried as the refusal's residual. To test (a) and (b) this
module reads ring normal forms (field.ring_polys, a predicate and never a
proof) and ENTRIES, as tagger.py does.
"""

from fractions import Fraction
from math import gcd, isqrt

import entries
import field as FD
import poly as P
from terms import (Add, App, BUILTINS, Call, Const, Div, Mul, Neg, Num, Pow,
                   RPow, Refused, Rel, Var, children, fv, show)

# Admitted node kinds (E23). Refused: Call, Deriv, Integral, MVar, and anything
# else. App is admitted only over the sixteen builtins.
WHITELIST = (Num, Const, Var, Neg, Add, Mul, Div, Pow, RPow, App)


def closed_ok(value, extensions=()):
    """True when every node of `value`, checked raw with nothing unfolded
    (§9), is of a WHITELIST kind, every App is over BUILTINS, and every Call
    is to a symbol in `extensions`. P1 passes none."""
    todo = [value]
    while todo:
        t = todo.pop()
        # Exact types, so no subclass of an admitted kind slips through.
        if type(t) is Call and t.fn in extensions:
            todo.extend(t.args)
        elif type(t) in WHITELIST and (type(t) is not App or t.fn in BUILTINS):
            todo.extend(k for _, k in children(t))
        else:
            return False
    return True


# ---------------------------------------------------------------- E27

NOT_EVALUATED = "close-not-evaluated"  # p1_expected REFUSAL_CODES
# `term` is show(the offending subterm), `entry` the entry's name.
MESSAGES = {
    "a": "{term} can still be evaluated ({entry})",
    "b": "{term} is unreduced literal arithmetic",
}


def check_evaluated(value):
    """E27: return None when `value` is fully evaluated, and otherwise raise
    Refused('close-not-evaluated', message, residual), where residual is
    the first offending subterm (a subtree of `value`) and message is
    MESSAGES[clause[0]] filled with show(residual) and, for (a), the entry.
    The kernel calls it last in close, whose goals all carry the `closed`
    schema (the only one there is, E23)."""
    found = evaluated_offence(value)
    if found is not None:
        clause, at, entry = found
        raise Refused(NOT_EVALUATED,
                      MESSAGES[clause[0]].format(term=show(at), entry=entry),
                      at)


def evaluated_offence(value):
    """(clause, subterm, entry name or None) for the first E27 offender in
    `value`, or None. clause is 'a', or 'b1' to 'b4'. (a) over the whole
    value comes before (b)."""
    nodes = list(_preorder(value))
    eqs = [e for e in entries.ENTRIES.values()
           if isinstance(e.statement, Rel) and e.statement.op == "=="]
    for s, _ in nodes:
        for e in eqs:
            if _counts(e, s):
                return "a", s, e.name
    for s, parent in nodes:
        for clause, test in _B_TESTS:
            if test(s, parent):
                return clause, s, None
    return None


def _preorder(t, parent=None):
    """(node, parent) pairs, pre-order, children in GRAMMAR.md §7's field
    order (terms.children). A close value holds no Int limit (E23), so
    every child is a Term."""
    todo = [(t, parent)]
    while todo:
        s, p = todo.pop()
        yield s, p
        todo.extend((k, s) for _, k in reversed(children(s)))


def _ring(*terms):
    """Ring normal forms of `terms` over one shared atom table, and that
    table (index -> Term). The value passed E25 and the check already, so
    nothing here refuses."""
    return FD.ring_polys(list(terms))


# -- (a): entries in force

def _counts(e, s):
    """Does entry e (an equation) count at subterm s? A stated reading for
    a schema entry, else E1 step 3 at the obvious inst."""
    reading = _READINGS.get(e.name)
    if reading is not None:
        return reading(s)
    L = e.statement.lhs
    if not e.schema:
        # (a1): L = h(p) matches h(b) with ring_nf(b) == ring_nf(p); a
        # non-application L matches as a tree (E1 step 3).
        if type(L) is App:
            if type(s) is not App or s.fn != L.fn:
                return False
            (pb, pp), _ = _ring(s.arg, L.arg)
            return pb == pp
        return s == L
    # A schema entry with no stated reading: structurally, the schema
    # variables matching any subterm, the same one at each occurrence; E1
    # step 3 then accepts at that inst, since L[inst] is s itself.
    return _tree_match(L, s, frozenset(e.schema), {})


def _tree_match(pat, t, schema, bound):
    if type(pat) is Var and pat.name in schema:
        if pat.name in bound:
            return bound[pat.name] == t
        bound[pat.name] = t
        return True
    if type(pat) is not type(t):
        return False
    if type(pat) in (Num, Const, Var):
        return pat == t
    if type(pat) is Pow and pat.n != t.n:
        return False
    if type(pat) in (App, Call) and pat.fn != t.fn:
        return False
    kp, kt = children(pat), children(t)
    return len(kp) == len(kt) and all(
        sp == st and _tree_match(a, b, schema, bound)
        for (sp, a), (st, b) in zip(kp, kt))


def _sqrt_sq(s):
    """sqrt(u^2) == u @ u >= 0 counts at sqrt b when ring_nf(b) is c*c for
    a polynomial c over Q[atoms] every atom of which is closed: then c or
    -c is >= 0, and E1 step 3 accepts either."""
    if type(s) is not App or s.fn != "sqrt":
        return False
    (p,), atoms = _ring(s.arg)
    c = _poly_sqrt(p)
    return c is not None and not any(
        fv(atoms[i]) for m in c for i, _ in m)


def _odd_reading(fn):
    def reading(s):
        """atan(-u) == -atan u counts at atan b when ring_nf(b) is nonzero
        and every rational coefficient of it is negative (u := -b, whose
        result cannot be rewritten again). sin_odd and cos_even are read
        the same way at sin b and cos b (E89)."""
        if type(s) is not App or s.fn != fn:
            return False
        (p,), _ = _ring(s.arg)
        return bool(p) and all(c < 0 for c in p.values())
    return reading


_atan_odd = _odd_reading("atan")


def _sqrt_sq_val(s):
    """(sqrt a)^2 == a @ a >= 0 counts at Pow(sqrt b, n) with |n| >= 2:
    field's fact reduction lowers every such power, negative ones
    included ((sqrt 2)^(-2) is 1/2)."""
    return (type(s) is Pow and abs(s.n) >= 2 and type(s.base) is App
            and s.base.fn == "sqrt")


def _never(s):
    """pyth_cos, (cos u)^2 == 1 - (sin u)^2, never counts (ATOM_FACT_RULE,
    E54): it trades one atom for another and evaluates nothing, as a
    rewrite that swaps atoms is not an evaluation."""
    return False


# EVALUATED_RULE (a2): the reading of each schema entry in force. A schema
# entry added later is read structurally (_counts) until it states one;
# pyth is read so, at a subterm tree-equal to (sin b)^2 + (cos b)^2, which
# is 1 unevaluated (E54).
#
# E89: the addition formulas and tan_def expand an atom and evaluate
# nothing, so they never count, as pyth_cos never does; sin_odd and
# cos_even count as atan_odd does.
_READINGS = {"sqrt_sq": _sqrt_sq, "atan_odd": _atan_odd,
             "sqrt_sq_val": _sqrt_sq_val, "pyth_cos": _never,
             "sin_add": _never, "cos_add": _never, "tan_def": _never,
             "sin_odd": _odd_reading("sin"), "cos_even": _odd_reading("cos")}


def _rat_sqrt(q):
    """The positive rational square root of q, or None."""
    if q <= 0:
        return None
    n, d = isqrt(q.numerator), isqrt(q.denominator)
    if n * n != q.numerator or d * d != q.denominator:
        return None
    return Fraction(n, d)


def _poly_sqrt(p):
    """A polynomial c with c*c == p, or None when there is none. The
    classical leading-term square root in poly.py's lex order: each new
    term of c is lead(r) / (2 lead(c)) for the remainder r = p - c*c, so the
    terms come out strictly decreasing, and each is bounded by half of p's
    degree in every atom, so the loop ends."""
    if not p:
        return {}
    half = {}
    for m in p:
        for i, e in m:
            half[i] = max(half.get(i, 0), e)
    half = {i: e // 2 for i, e in half.items()}
    c, r, lead = {}, dict(p), None
    while r:
        m = P.leading(r)
        if lead is None:
            if any(e % 2 for _, e in m):
                return None
            coeff = _rat_sqrt(r[m])
            if coeff is None:
                return None
            tm = tuple((i, e // 2) for i, e in m)
        else:
            lm, lc = lead
            have = dict(m)
            if any(have.get(i, 0) < e for i, e in lm):
                return None
            tm = P.mono_div(m, lm)
            coeff = r[m] / (2 * lc)
        if any(e > half.get(i, 0) for i, e in tm):
            return None
        t = {tm: coeff}
        r = P.sub(r, P.add(P.scale(P.mul(c, t), 2), P.mul(t, t)))
        c = P.add(c, t)
        if lead is None:
            lead = (tm, coeff)
    return c


# -- (b): literal arithmetic

def _pq(p, q):
    """p/q's two naturals, for a rational literal's quotient shapes."""
    return type(q) is Num and p >= 1 and q.n >= 2 and gcd(p, q.n) == 1


def _rational_literal(t):
    """Num n (n >= 0); Neg(Num n) (n >= 1); Div(Num p, Num q),
    Neg(Div(Num p, Num q)) and Div(Neg(Num p), Num q) with p >= 1, q >= 2,
    gcd 1: lit(q)'s shapes plus the parser's -p/q (GRAMMAR.md D9)."""
    k = type(t)
    if k is Num:
        return True
    if k is Neg:
        a = t.a
        if type(a) is Num:
            return a.n >= 1
        return type(a) is Div and type(a.a) is Num and _pq(a.a.n, a.b)
    if k is Div:
        a = t.a
        if type(a) is Neg and type(a.a) is Num:
            return _pq(a.a.n, t.b)
        return type(a) is Num and _pq(a.n, t.b)
    return False


def _value(t):
    """The Fraction a rational literal stands for."""
    k = type(t)
    if k is Num:
        return Fraction(t.n)
    if k is Neg:
        return -_value(t.a)
    return _value(t.a) / _value(t.b)  # Div


_LITERAL_KINDS = (Num, Neg, Add, Mul, Div, Pow)


def _literal_term(t):
    """Built from Num by Neg, Add, Mul, Div and Pow alone (Pow's exponent is
    a field, not a subterm). RPow and App never are."""
    todo = [t]
    while todo:
        s = todo.pop()
        if type(s) not in _LITERAL_KINDS:
            return False
        todo.extend(k for _, k in children(s))
    return True


def _sum_node(t):
    return type(t) is Add or (type(t) is Neg and not _rational_literal(t))


def _product_node(t):
    return type(t) is Mul or (type(t) is Div and not _rational_literal(t))


def _summands(t):
    """Sum flattening, left to right. The signs are not kept: no test
    reads them (a zero summand, and a monomial count, are the same up to
    sign). Iterative, so a deep Neg chain cannot exhaust the stack."""
    out, todo = [], [t]
    while todo:
        s = todo.pop()
        if _rational_literal(s):
            out.append(s)
        elif type(s) is Add:
            todo += (s.b, s.a)
        elif type(s) is Neg:
            todo.append(s.a)
        else:
            out.append(s)
    return out


def _factors(t):
    """Product flattening, left to right: (factor, on the denominator
    side). Iterative, as _summands is."""
    out, todo = [], [(t, False)]
    while todo:
        s, below = todo.pop()
        if _rational_literal(s):
            out.append((s, below))
        elif type(s) is Mul:
            todo += ((s.b, below), (s.a, below))
        elif type(s) is Div:
            todo += ((s.b, not below), (s.a, below))
        else:
            out.append((s, below))
    return out


def _b1(t, parent):
    """A maximal literal term that is not a rational literal."""
    return (_literal_term(t) and not (parent is not None
                                      and _literal_term(parent))
            and not _rational_literal(t))


def _b2(t, parent):
    """A maximal sum with a summand whose ring normal form is 0, or whose
    own ring normal form has fewer monomials than its summands' normal
    forms have in total, so that ring would merge or cancel monomials
    across summands (two literals, like terms, 2*(pi + 1) - 2). The count
    subsumes a rational-multiples test; the zero test stays, since a zero
    summand adds no monomial to either count."""
    if not _sum_node(t) or (parent is not None and _sum_node(parent)):
        return False
    parts = _summands(t)
    polys, _ = _ring(t, *parts)
    whole, polys = polys[0], polys[1:]
    return (any(not p for p in polys)
            or len(whole) < sum(len(p) for p in polys))


def _b3(t, parent):
    """A maximal product with (i) a literal factor 0; (ii) a literal factor
    1 or -1 that is not the only numerator factor; (iii) two literal
    factors on one side; (iv) a denominator literal that is not Num n with
    n >= 2, or a numerator literal beside a denominator literal that is not
    an integer literal or shares a factor with it; (v) two non-literal
    factors on one side whose bases have equal ring normal forms. Factors
    on opposite sides are never compared (that is field's cancellation)."""
    if not _product_node(t) or (parent is not None and _product_node(parent)):
        return False
    lits, bases, above = [], [], 0
    for f, below in _factors(t):
        if _rational_literal(f):
            lits.append((f, below))
        else:
            # A non-literal Pow(c, n) has base c and, when n < 0, counts on
            # the opposite side in every test here: 1*pi^(-1) reads as 1/pi
            # and pi*pi^(-1) as pi/pi. Any other factor is its own base.
            base = f
            if type(f) is Pow and not _literal_term(f):
                base, below = f.base, below != (f.n < 0)
            bases.append((base, below))
        above += not below
    for f, below in lits:
        v = _value(f)
        if v == 0:
            return True                                            # (i)
        if abs(v) == 1 and (below or above != 1):
            return True                                            # (ii)
    for side in (False, True):
        if sum(below == side for _, below in lits) >= 2:
            return True                                            # (iii)
    ups = [f for f, below in lits if not below]
    for f, below in lits:
        if below:
            if type(f) is not Num or f.n < 2:
                return True                                        # (iv)
            for a in ups:
                whole = type(a) is Num or (type(a) is Neg
                                           and type(a.a) is Num)
                if not whole or gcd(abs(_value(a).numerator), f.n) != 1:
                    return True                                    # (iv)
    if len(bases) >= 2:                                            # (v)
        polys, _ = _ring(*(b for b, _ in bases))
        for i in range(len(bases)):
            for j in range(i):
                if bases[i][1] == bases[j][1] and polys[i] == polys[j]:
                    return True
    return False


def _b4(t, parent):
    """A Pow with exponent 0 or 1, or whose base is a Pow or a Neg that is
    not a rational literal; or a Neg directly over a Neg."""
    if type(t) is Pow:
        b = t.base
        return (t.n in (0, 1) or type(b) is Pow
                or (type(b) is Neg and not _rational_literal(b)))
    return type(t) is Neg and type(t.a) is Neg


_B_TESTS = (("b1", _b1), ("b2", _b2), ("b3", _b3), ("b4", _b4))
