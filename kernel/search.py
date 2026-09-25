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
  sign product  E18's content split, then tagger.normalised_factors, each
                factor's relation (strict first, then non-strict under a
                non-strict target, E53) found by this same search.
  cite          an ENTRIES ordering whose conclusion implies the proposition
                (tagger._implies), each instantiated hypothesis found by this
                same search.

Sub-obligations are searched after the exact values, as the checker decides
them, and a literal one gets the norm_num leaf. Termination is TAG_RULES':
strictly lower degree for a factorisation, and no second content split; and
factorisations nest at most tagger.FACTOR_DEPTH deep, as the tagger's do, so
no certificate is arbitrarily deep.

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
from terms import (Add, Const, Div, Interval, Mul, Neg, NonZero, Num, Pow, Reg,
                   Refused, Rel, Term, Var, lit, subst, with_domain)

NORM_NUM = {"method": "norm_num"}
ZERO = Num(0)
ORDERINGS = ("<", "<=", ">", ">=")


# Sub-searches already answered within one propose call: (key, split,
# depth) -> certificate or None. A sub-search is a function of its
# arguments, so the answer is reused, which keeps a factorisation that
# meets the same factor again and again (a high power's repeated root, the
# E56 timing goal's (a - 1)^40 <= 0) polynomial rather than exponential.
# Set by the outermost propose and dropped when it returns: no cache
# outlives a call.
_MEMO = None


def propose(key):
    """One certificate for `key` (a Rel or NonZero with its domain, or a Reg
    key), or None. The certificate is for the key as the checker reads it,
    after the exact values (E31). Deterministic; it keeps no cache between
    calls."""
    global _MEMO
    outer = _MEMO is None
    if outer:
        _MEMO = {}
    try:
        if type(key) is Reg:
            return _reg(key)
        return _search(key, split=True)
    finally:
        if outer:
            _MEMO = None


def domain_empty(key):
    """§5.3's satisfiability pre-check, as the search runs it: True when the
    key's constraint set without ('goal',) is infeasible in the linear
    relaxation. The kernel reads it for REASON_EMPTY."""
    try:
        key, _ = DC.exact_values(key)
        return _empty(key)
    except Refused:
        return False


_IN_NODE = False  # E82's node method: at the top of a search, or under itself


def _search(key, split, depth=0):
    memo = (key, split, depth, _IN_NODE)
    if _MEMO is not None and memo in _MEMO:
        return _MEMO[memo]
    cert = _search_uncached(key, split, depth)
    if _MEMO is not None:
        _MEMO[memo] = cert
    return cert


def _search_uncached(key, split, depth):
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
               lambda: _sign(prop), lambda: _product(key, split, depth),
               lambda: (_node(key, depth) if depth == 0 or _IN_NODE
                        else None),
               lambda: _cite(prop, dom, depth))
    for method in methods:
        try:
            cert = method()
        except Refused:
            cert = None  # a method that meets a zero divisor builds nothing
        if cert is not None:
            return cert
    return None


# ---------------------------------------------------------------- reg

def _reg_sides(sides):
    """The sides of one node the search certifies: all of them. A seam
    (ARCHITECTURE.md §7): the planted bug reg_search_drops_side drops the
    last."""
    return sides


def _reg(key):
    """REG_SEARCH_RULE: the derivation of the term by its structure
    (tagger.reg_derivation, over the trusted natural-domain data), each
    side's certificate from this search at the Reg's domain. A node with no
    rule, or a side with no certificate, and nothing is proposed. There is
    one derivation per term, so no alternative is tried."""
    d = TG.reg_derivation(key.e, key.k)
    if d is None:
        return None

    def node(d):
        rule, sides, kids = d
        side = []
        for prop in _reg_sides(sides):
            cert = propose(with_domain(prop, key.dom))
            if cert is None:
                return None
            side.append((prop, cert))
        args = []
        for k in kids:
            a = node(k)
            if a is None:
                return None
            args.append(a)
        return {"rule": rule, "args": tuple(args), "side": tuple(side)}
    tree = node(d)
    return None if tree is None else {"method": "reg", "tree": tree}


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
    out += [(("fact", name, w), x, y, s)  # E49, ATOM_FACT_RULE
            for name, w, (x, y, s) in TG.atom_facts((key, key.dom))]
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

def _product(key, split, depth=0):
    """TAG_RULES sign product on e = a - b, as tagger._product finds it,
    for every ordering and # 0 (E53). The checker reads a < b and a <= b as
    g = b - a = -e, so for those keys the content's sign is flipped, which
    keeps the parity +1. A factor's relation is tried strict first, then
    non-strict under a non-strict target; the factorisation's factors have
    positive leading coefficients and the content takes the sign."""
    prop, dom = replace(key, dom=()), key.dom
    form = TG.product_form(prop)
    if form is None:
        return None
    a, b, want, rels = form
    sense = "#" if want == 0 else None
    [e], atoms = TG._normal_diffs([(a, b)])
    if not e:
        return None
    flip = -1 if want == -1 else 1
    c, p = P.content_normal(e)
    if split and TG.splits(c, prop):
        s = want * (1 if c > 0 else -1)
        t = TG._as_term(p, atoms)
        for r in TG.split_relations(rels, s):
            cert = _search(TG.rel_goal(t, r, dom), split=False, depth=depth)
            if cert is not None:
                return {"method": "sign product", "sense": sense,
                        "content": flip * c, "factors": ((t, r, cert),)}
    # tagger.FACTOR_DEPTH bounds the nesting, so no certificate is deeper
    found = (TG.normalised_factors(e, atoms) if depth < TG.FACTOR_DEPTH
             else None)
    if not found:
        return None
    c, factors = found
    options = []
    for f in factors:
        certs = [(r, _search(TG.rel_goal(f, r, dom), split=True, depth=depth + 1))
                 for r in rels]
        options.append([(r, cert) for r, cert in certs if cert is not None])
    for choice in itertools.product(*options):
        if want == 0 or ((1 if c > 0 else -1)
                         * math.prod(TG.RELATION_SIGN[r] for r, _ in choice)) == want:
            return {"method": "sign product", "sense": sense,
                    "content": Fraction(flip) * c,
                    "factors": tuple((f, r, cert)
                                     for f, (r, cert) in zip(factors, choice))}
    return None


# ---------------------------------------------------------------- sign node

def _node(key, depth=0):
    """E82's method 5b: for the key's own node, a few certified relations
    per child, strict first and non-strict only when no strict one is
    found (for a sum, only the relations that can reach the target), tried
    in combination until the node's set of signs is inside the target's.
    The checker decides."""
    if depth >= TG.FACTOR_DEPTH:
        return None
    try:
        g, allowed = DC._node_target(key)
        kids = DC._node_children(g)
    except DC._Reject:
        return None
    dom = key.dom

    def cert(t, r):
        prop = NonZero(t) if r == "# 0" else Rel(r, t, ZERO)
        return _search(with_domain(prop, dom), split=True, depth=depth + 1)

    def first(t, tiers):
        """The certified relations of the first tier with any."""
        for tier in tiers:
            got = [(r, c) for r in tier for c in (cert(t, r),) if c is not None]
            if got:
                return got
        return []
    if type(g) is Add:
        signs = [sgn for sgn in (1, -1) if sgn in allowed]
        tiers = lambda sgn: (((">",), (">=",)) if sgn > 0  # noqa: E731
                             else (("<",), ("<=",)))
    else:
        signs = [None]
        tiers = lambda _: ((">", "<"), ("# 0",), (">=", "<="))  # noqa: E731
    global _IN_NODE
    outer, _IN_NODE = _IN_NODE, True
    try:
        for sgn in signs:
            options = [first(k, tiers(sgn)) for k in kids]
            for parts in itertools.product(*options):
                try:
                    got = DC._node_signs(g, [DC.SIGN_SETS[r] for r, _ in parts])
                except DC._Reject:
                    continue
                if got <= allowed:
                    return {"method": "sign node", "parts": tuple(parts)}
    finally:
        _IN_NODE = outer
    if (type(g) is Pow and g.n % 2 == 0 and g.n != 0
            and frozenset({1, 0}) <= allowed):  # an even power, no child
        return {"method": "sign node", "parts": ()}
    return None


# ---------------------------------------------------------------- cite

def _cite(prop, dom, depth=0):
    for name, entry in ENTRIES.items():
        st = entry.statement
        if not (type(st) is NonZero or (type(st) is Rel and st.op in ORDERINGS)):
            continue
        inst = TG._implies(replace(st, dom=()), prop, entry.schema)
        if inst is None or set(inst) != set(entry.schema):
            continue
        children = []
        for h in subst(st, inst).dom:
            cert = _search(with_domain(h, dom), split=True, depth=depth)
            if cert is None:
                break
            children.append((h, cert))
        else:
            return {"method": "cite", "entry": name, "inst": dict(inst),
                    "hyps": tuple(children)}
    return None
