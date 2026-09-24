"""The discharge search: one certificate per obligation, for the checker.

Untrusted (DESIGN.md §7 and §15.2; p1_expected E28, DISCHARGE_RULE). It
lives beside the tagger and reuses its feasibility checks, extended to build
the witness each already finds: `tagger.refutation` is the tagger's own
Fourier–Motzkin with its Farkas multipliers kept. Nothing here decides an
obligation. `propose(key)` hands one certificate to discharge.py, which
rebuilds everything from the key and re-checks it, so a bug here costs an
admission (REASON_REJECTED, or no certificate at all), never a discharge.

The methods are tried in §5.3's order, exactly as TAG_RULES orders them, and
the first certificate built is the one proposed; there is no fallback once
the checker has seen it (E28). For each:

  hyp           a domain relation or NonZero item equal to the proposition
                (or e > 0, e < 0, 0 < e, 0 > e for e # 0), else the
                shortest chain of ordering items from one end to the other.
                Interval items never count: a range is a Farkas certificate's.
  range/linear  the labelled constraint set (the sign facts of
                tagger.SIGN_FACTS for the constants that occur, then the
                domain in order), the satisfiability pre-check on it without
                ('goal',), then for each sense the tagger's deletion filter
                and `tagger.refutation` on what is left. The multipliers are
                scaled so that ('goal',) has 1.
  sign          the goal as written, then its ring normal form: a rational
                plus even powers with positive coefficients, or a
                one-atom quadratic with a negative discriminant, whose
                certificate is its completed square. e # 0 is tried as e > 0.
  sign product  E18's content split, then tagger.factor_rational_roots, each
                factor's sign found by this same search.
  cite          an ENTRIES ordering whose conclusion implies the proposition
                (tagger._implies), each instantiated hypothesis found by this
                same search.

Sub-obligations are searched after the exact values, as the checker decides
them, and a literal one gets the norm_num leaf. Termination is TAG_RULES':
strictly lower degree for a factorisation, and no second content split.

**Seam** (kernel/ARCHITECTURE.md §7): `_witness`, which scales the Farkas
multipliers, is replaced by the planted bug search_scales_wrongly.
"""

import itertools
import math
from dataclasses import replace
from fractions import Fraction

import discharge as DC
import field as FD
import poly as P
import tagger as TG
from entries import ENTRIES
from terms import (Add, Const, Div, Interval, Mul, Neg, NonZero, Num, Pow,
                   Refused, Rel, Term, Var, lit, subst, with_domain)

NORM_NUM = {"method": "norm_num"}
ZERO = Num(0)
ORDERINGS = ("<", "<=", ">", ">=")


def propose(key):
    """One certificate for `key` (a Rel or NonZero with its domain), or
    None. The certificate is for the key as the checker reads it, after the
    exact values (E31). Deterministic, and it keeps no cache."""
    return _search(key, split=True)


def domain_empty(key):
    """§5.3's satisfiability pre-check, as the search runs it: True when the
    key's constraint set without ('goal',) is infeasible in the linear
    relaxation. The kernel reads it for REASON_EMPTY."""
    try:
        key, _ = DC.exact_values(key)
        return _empty(key)
    except Refused:
        return False


def _search(key, split):
    try:
        key, _ = DC.exact_values(key)
        said = FD.norm_num(key)
    except Refused:
        return None
    if said is not None:
        return dict(NORM_NUM) if said else None
    if type(key) not in (Rel, NonZero) or getattr(key, "op", "#") == "==":
        return None
    prop, dom = replace(key, dom=()), key.dom
    methods = (lambda: _hyp(prop, dom), lambda: _farkas(key),
               lambda: _sign(prop), lambda: _product(key, split),
               lambda: _cite(prop, dom))
    for method in methods:
        try:
            cert = method()
        except Refused:
            cert = None  # a method that meets a zero divisor builds nothing
        if cert is not None:
            return cert
    return None


# ---------------------------------------------------------------- hyp

def _order(rel):
    """An ordering as (lo, hi, strict): lo < hi or lo <= hi."""
    a, b = rel.lhs, rel.rhs
    return {"<": (a, b, True), "<=": (a, b, False),
            ">": (b, a, True), ">=": (b, a, False)}[rel.op]


def _hyp(prop, dom):
    items = [(i, it) for i, it in enumerate(dom) if type(it) in (Rel, NonZero)]
    for i, it in items:
        if it == prop or (type(prop) is NonZero and type(it) is Rel
                          and it.op in ("<", ">")
                          and (it.lhs, it.rhs) in ((prop.e, ZERO),
                                                   (ZERO, prop.e))):
            return {"method": "hyp", "member": i}
    edges = [(*_order(it), i) for i, it in items
             if type(it) is Rel and it.op in ORDERINGS]
    if type(prop) is NonZero:
        ends, strict = [(prop.e, ZERO), (ZERO, prop.e)], True
    elif prop.op in ORDERINGS:
        lo, hi, strict = _order(prop)
        ends = [(lo, hi)]
    else:
        return None
    for lo, hi in ends:
        path = _path(lo, hi, strict, edges)
        if path:
            return {"method": "hyp", "chain": path}
    return None


def _path(x, y, strict, edges):
    """The shortest chain of item indices from x to y, strict if asked."""
    todo, seen = [(x, False, ())], set()
    while todo:
        node, s, path = todo.pop(0)
        if path and node == y and (s or not strict):
            return path
        if (node, s) in seen:
            continue
        seen.add((node, s))
        todo += [(hi, s or st, path + (i,)) for lo, hi, st, i in edges
                 if lo == node]
    return None


# ---------------------------------------------------------- range, linear

def _labelled(key):
    """The key's constraints as (label, x, y, strict), meaning x - y > 0 or
    >= 0: the sign facts first, then the domain's items in order, as
    tagger._linear lists them. Built here, apart from the checker's own
    construction, so that neither can hide the other's mistake."""
    names = {n.name for n in TG._nodes((key, key.dom)) if isinstance(n, Const)}
    out = [(("fact", entry), x, y, s)
           for const, (entry, fact) in TG.SIGN_FACTS.items() if const in names
           for x, y, s in TG._senses(fact)]
    for i, item in enumerate(key.dom):
        if type(item) is Interval:
            v = Var(item.var)
            if isinstance(item.lo, Term):
                out.append((("dom", i, "lo"), v, item.lo, not item.lo_closed))
            if isinstance(item.hi, Term):
                out.append((("dom", i, "hi"), item.hi, v, not item.hi_closed))
        elif type(item) is Rel and item.op in ORDERINGS:
            (x, y, s), = TG._senses(item)
            out.append((("dom", i, "rel"), x, y, s))
    return out


def _polys(cons):
    polys, _ = TG._normal_diffs([(x, y) for _, x, y, _ in cons])
    return [(p, s) for p, (_, _, _, s) in zip(polys, cons)]


def _empty(key):
    return TG.refutation(_polys(_labelled(key))) is not None


def _witness(multipliers):
    """The Farkas multipliers {label: q}, scaled so that ('goal',) has 1,
    or None if the goal is not among them. A seam (ARCHITECTURE.md §7)."""
    g = multipliers.get(DC.GOAL)
    if not g:
        return None
    return {label: m / g for label, m in multipliers.items()}


def _farkas(key):
    """Methods 2 and 3. The pre-check first: if the domain's constraint set
    is infeasible, no Farkas certificate is attempted (§5.3, E29)."""
    if _empty(key):
        return None
    rest = _labelled(key)
    nf = sum(label[0] == "fact" for label, *_ in rest)
    prop = replace(key, dom=())
    senses = TG._senses(prop)
    for sense, (a, b, strict) in zip(
            (">", "<") if type(prop) is NonZero else (None,), senses):
        cons = [(DC.GOAL, b, a, not strict)] + rest
        polys = _polys(cons)
        if TG.refutation(polys) is None:
            continue
        # tagger._linear's deletion filter: keep the negated goal, drop the
        # sign facts first, then the domain's constraints from last to first.
        keep = list(range(len(cons)))
        for k in list(range(1, 1 + nf)) + list(range(len(cons) - 1, nf, -1)):
            trial = [j for j in keep if j != k]
            if TG.refutation([polys[j] for j in trial]) is not None:
                keep = trial
        mult = TG.refutation([polys[j] for j in keep])
        found = _witness({cons[keep[j]][0]: m for j, m in mult.items()})
        if found is None:
            return None
        return {"method": "farkas", "sense": sense, "multipliers": found}
    return None


# ---------------------------------------------------------------- sign

def _sign(prop):
    senses = TG._senses(prop)
    if not senses:
        return None
    a, b, strict = senses[0]
    written = a if b == ZERO else Add(a, Neg(b))
    found = _written(written, strict) or _normal(a, b, strict)
    if found is None:
        return None
    c0, squares = found
    return {"method": "sign", "sense": ">" if type(prop) is NonZero else None,
            "const": c0, "squares": tuple(squares)}


def _written(t, strict):
    """The goal as written: a rational plus even powers (TAG_RULES sign)."""
    const, squares, todo = Fraction(0), [], [t]
    while todo:
        u = todo.pop()
        if type(u) is Add:
            todo += [u.a, u.b]
        elif (q := FD.rational_value(u)) is not None:
            const += q
        elif (sq := _even(u)) is not None:
            squares.append(sq)
        else:
            return None
    return (const, squares) if const > 0 or (not strict and const == 0) \
        else None


def _even(t):
    """t as (c, s, k), c * s^k with c > 0 and k even, as written: an even
    power, times or over positive rationals, or a product of even powers
    written as one square. None otherwise."""
    if type(t) is Pow:
        return (Fraction(1), t.base, t.n) if t.n > 0 and t.n % 2 == 0 else None
    if type(t) is Div:
        q, sq = FD.rational_value(t.b), _even(t.a)
        if sq is None or q is None or q <= 0:
            return None
        return sq[0] / q, sq[1], sq[2]
    if type(t) is not Mul:
        return None
    c, powers = Fraction(1), []
    for u in (t.a, t.b):
        q = FD.rational_value(u)
        if q is not None and q > 0:
            c *= q
        elif (sq := _even(u)) is not None:
            c *= sq[0]
            powers.append(sq)
        else:
            return None
    if not powers:
        return None
    if len(powers) == 1:
        return c, powers[0][1], powers[0][2]
    base = None
    for _, s, k in powers:  # (s1^k1)(s2^k2) = (s1^(k1/2) s2^(k2/2))^2
        f = s if k == 2 else Pow(s, k // 2)
        base = f if base is None else Mul(base, f)
    return c, base, 2


def _normal(a, b, strict):
    """The ring normal form: a rational plus even monomials with positive
    coefficients, or a one-atom quadratic with a positive leading
    coefficient and a negative discriminant, completed to a square."""
    [e], atoms = TG._normal_diffs([(a, b)])
    c0 = P.const_value(e)
    mons = [(m, c) for m, c in e.items() if m != P.ONE_MONO]
    if (all(c > 0 and all(k % 2 == 0 for _, k in m) for m, c in mons)
            and (c0 > 0 or (not strict and c0 == 0))):
        return c0, [_square(m, c, atoms) for m, c in mons]
    used = {i for m in e for i, _ in m}
    if len(used) != 1:
        return None
    i = used.pop()
    if P.degree_in(e, i) != 2:
        return None
    qa, qb = e.get(((i, 2),), Fraction(0)), e.get(((i, 1),), Fraction(0))
    if not (qa > 0 and qb * qb - 4 * qa * c0 < 0):
        return None
    h = qb / (2 * qa)
    s = atoms[i] if h == 0 else Add(atoms[i], lit(h))
    return c0 - qb * qb / (4 * qa), [(qa, s, 2)]


def _square(m, c, atoms):
    """The monomial c * m, every exponent even, as (c, s, k)."""
    if len(m) == 1:
        (i, k), = m
        return c, atoms[i], k
    base = None
    for i, k in m:
        f = atoms[i] if k == 2 else Pow(atoms[i], k // 2)
        base = f if base is None else Mul(base, f)
    return c, base, 2


# ---------------------------------------------------------------- sign product

_REL = {0: "# 0", 1: ">", -1: "<"}


def _product(key, split):
    """TAG_RULES sign product on e = a - b, as tagger._product finds it.
    The checker reads a < b as g = b - a = -e, so for a '<' key the
    content's sign is flipped, which keeps the parity +1."""
    prop, dom = replace(key, dom=()), key.dom
    if type(prop) is NonZero:
        a, b, want, sense = prop.e, ZERO, 0, "#"
    elif prop.op in (">", "<"):
        a, b, want, sense = prop.lhs, prop.rhs, 1 if prop.op == ">" else -1, None
    else:
        return None
    [e], atoms = TG._normal_diffs([(a, b)])
    if not e:
        return None
    flip = -1 if want == -1 else 1
    c, p = P.content_normal(e)
    if split and c != 1:
        s = want * (1 if c > 0 else -1)
        t = TG._as_term(p, atoms)
        cert = _search(TG._sign_goal(t, s, dom), split=False)
        if cert is not None:
            return {"method": "sign product", "sense": sense,
                    "content": flip * c, "factors": ((t, _REL[s], cert),)}
    factors = TG.factor_rational_roots(e, atoms)
    if not factors:
        return None
    options = []
    for f in factors:
        found = [(s, _search(TG._sign_goal(f, s, dom), split=True))
                 for s in ((0,) if want == 0 else (1, -1))]
        options.append([(s, cert) for s, cert in found if cert is not None])
    for choice in itertools.product(*options):
        if want == 0 or math.prod(s for s, _ in choice) == want:
            return {"method": "sign product", "sense": sense,
                    "content": Fraction(flip),
                    "factors": tuple((f, _REL[s], cert)
                                     for f, (s, cert) in zip(factors, choice))}
    return None


# ---------------------------------------------------------------- cite

def _cite(prop, dom):
    for name, entry in ENTRIES.items():
        st = entry.statement
        if not (type(st) is NonZero or (type(st) is Rel and st.op in ORDERINGS)):
            continue
        inst = TG._implies(replace(st, dom=()), prop, entry.schema)
        if inst is None or set(inst) != set(entry.schema):
            continue
        children = []
        for h in subst(st, inst).dom:
            cert = _search(with_domain(h, dom), split=True)
            if cert is None:
                break
            children.append((h, cert))
        else:
            return {"method": "cite", "entry": name, "inst": dict(inst),
                    "hyps": tuple(children)}
    return None
