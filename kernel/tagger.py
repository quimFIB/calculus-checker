"""The admission tagger: which §5.3 method should close each admission.

Untrusted (DESIGN.md §7; p1_expected E24). An obligation discharge does
not close is admitted (E32), and this module names the method expected to
close it, plus the §6.8 entries that method would cite. The
kernel records the tag and relies on it for nothing. A tag of
('none', ()) on an admission in an unmutated PROOFS run fails the milestone
(WHAT.md), and that is how the π gap of revision 9 would have shown up.

`tag` implements p1_expected's TAG_RULES as stated. Each method is a cheap
feasibility check, and none emits a certificate here: the discharge search
(search.py, untrusted as this is) builds the certificates from the same
checks, `refutation` below among them, for the trusted checker
(discharge.py) to re-check. The methods are tried in §5.3's order, and the
first to pass wins:

  reg           a Reg judgement, by shape alone. Nothing else is Reg.
  hyp           prop is in gamma, or follows from gamma's ordering items by
                reflexive-transitive closure. gamma is the goal's own
                hypotheses, never an Int range. P1's gamma is always ().
  range/linear  Fourier–Motzkin over ℚ, via field.ring_polys: every
                non-constant monomial becomes a fresh variable. The set is:
                the negated goal; the domain's items, where an interval on v
                gives c <= v and v <= d, strict at an open end and absent at
                an infinite one; and SIGN_FACTS for each named constant that
                occurs in prop or dom, and ATOM_FACTS' non-strict bound for
                each distinct atom of its head (sqrt_nonneg for sqrt,
                cos_le_one and cos_ge_neg_one for cos; ATOM_FACT_RULE). A
                goal e # 0 is tried as e > 0, then as
                e < 0. If the set is infeasible, shrink it to a support-minimal
                infeasible subset by a deletion filter that keeps the negated
                goal and tries to drop the sign facts first, then the domain
                items from last to first. The tag is 'range' if the subset
                holds a domain item, 'linear' otherwise, and the cites are
                the subset's sign facts.
  sign          first the goal as written, then its ring normal form, is
                matched against a positive rational plus even powers with
                positive coefficients, or a one-variable quadratic with a
                positive leading coefficient and a negative discriminant.
                E20: a non-strict `e >= 0` or `0 <= e` goal also accepts a
                zero constant. e # 0 is tried as e > 0.
  sign product  every ordering and # 0 (E53, SIGN_PRODUCT_NONSTRICT_RULE).
                (i) E18: the normal form is c*p with rational c other than 0
                and 1 (and other than -1 under a non-strict target, where
                p's goal restates the key), and p's obligation at dom is not
                tagged none. (ii) Otherwise, a factorisation into factors
                of strictly lower degree from `normalised_factors`, each
                factor with a positive leading coefficient and the content
                taking the sign, in which no factor's obligation at dom is
                tagged none. A factor's relation is tried strict first ('>'
                then '<'), then, under a non-strict target only, non-strict
                ('>=' then '<='); a choice's parity must give the goal's
                sign. The cites are the parts' cites.
  cite          an ENTRIES statement whose instantiated conclusion is prop as
                a tree, or is `a > 0` / `0 < a` where prop is `a # 0`,
                `a >= 0` or `0 <= a` for the same a, and whose instantiated
                hypotheses at dom are none of them tagged none. The cites are
                the entry plus its hypotheses' cites.
  none          ('none', ()).

Sub-obligations are tagged by this same list, recursively, and are never
recorded. Termination is §5.3's own: strictly lower degree in (ii), and a
literal content in (i). Cites are deduplicated in first-seen order.
"""

import itertools
import math
from dataclasses import fields, is_dataclass, replace
from fractions import Fraction

import field as FD
import poly as P
import residual
from entries import ENTRIES
from terms import (Add, App, Const, Div, Mul, Neg, NonZero, Num, Pow, Refused,
                   Reg, Rel, Term, Var, subst, with_domain)

# Constant name -> (entry name, sign fact). Read at call time. It is a seam:
# the planted bug pi_pos_not_in_constraint_set clears it
# (kernel/ARCHITECTURE.md §7).
SIGN_FACTS = {
    "pi": ("pi_pos", Rel(">", Const("pi"), Num(0))),
    "e_const": ("e_gt_one", Rel(">", Const("e_const"), Num(1))),
}

NONE = ("none", ())
SQRT_FACT = "sqrt_nonneg"  # E49's sign fact, one per sqrt atom
# ATOM_FACT_RULE (E54, generalising E49): each atom sign fact, read for each
# distinct atom of its head, in the order the cites list them. This module's
# own copy, apart from discharge.ATOM_FACTS, so neither hides the other.
ATOM_FACTS = {SQRT_FACT: "sqrt", "cos_le_one": "cos", "cos_ge_neg_one": "cos"}
ROOT_TEST_BOUND = 10 ** 6  # keeps the rational root test cheap (TAG_RULES)
# How deep sign product's factorisations nest, a factor's own obligation
# factorised again: past it, (ii) is not tried. §5.3's strictly lower degree
# terminates the recursion, but a degree-300 power would take 300 levels,
# each normalising a degree-300 polynomial. search.py uses the same bound,
# so that the method it certifies is the one this names (E28).
FACTOR_DEPTH = 8
ZERO = Num(0)


def tag(key, gamma=()):
    """The (method, cites) tag for the admission `key`, a Judgement with its
    domain. `gamma` is the part of key.dom that came from the goal's own
    domain. Pure and deterministic. It never raises for a well-formed key,
    and it keeps no cache between calls."""
    return _tag(key, tuple(gamma), split=True)


def _tag(key, gamma, split, depth=0):
    """The method list, in §5.3's order. `split` is False only for the p of
    a content split, which is monic and is not split again (E18). `depth`
    counts the factorisations enclosing this obligation (FACTOR_DEPTH)."""
    if isinstance(key, Reg):
        return ("reg", ())
    prop, dom = replace(key, dom=()), key.dom
    methods = (lambda: _hyp(prop, gamma),
               lambda: _linear(prop, dom),
               lambda: _sign(prop),
               lambda: _product(prop, dom, gamma, split, depth),
               lambda: _cite(prop, dom, gamma, depth))
    for method in methods:
        try:
            found = method()
        except Refused:
            # A zero divisor in what a method normalised, or an instantiated
            # hypothesis that cannot be built. That method does not pass.
            # The kernel refuses a key with a zero divisor before emitting
            # it, so a recorded admission never gets here.
            found = None
        if found:
            return found
    return NONE


def _dedup(cites):
    return tuple(dict.fromkeys(cites))


# ---------------------------------------------------------------- goal forms

def _senses(prop):
    """prop as goals `a - b > 0` (strict) or `a - b >= 0`: a list of (a, b,
    strict), in the order range/linear tries them. `e # 0` gives e > 0, then
    e < 0. An equation gives no goal: no method here closes one."""
    if isinstance(prop, NonZero):
        return [(prop.e, ZERO, True), (ZERO, prop.e, True)]
    return {">": [(prop.lhs, prop.rhs, True)],
            ">=": [(prop.lhs, prop.rhs, False)],
            "<": [(prop.rhs, prop.lhs, True)],
            "<=": [(prop.rhs, prop.lhs, False)]}.get(prop.op, [])


def _rel_senses(item):
    """A domain item or sign fact as (a, b, strict) facts `a - b > 0` or
    `>= 0`. An interval on v gives lo <= v and v <= hi, strict at an open
    end and absent at an infinite one. An `==` item gives both directions,
    and a `# 0` item gives nothing, since it is not convex."""
    if isinstance(item, Rel):
        if item.op == "==":
            return [(item.lhs, item.rhs, False), (item.rhs, item.lhs, False)]
        return _senses(item)
    if isinstance(item, NonZero):
        return []
    v, out = Var(item.var), []
    if isinstance(item.lo, Term):
        out.append((v, item.lo, not item.lo_closed))
    if isinstance(item.hi, Term):
        out.append((item.hi, v, not item.hi_closed))
    return out


def _nodes(x):
    """Every node of a term, judgement, interval or tuple, in pre-order."""
    yield x
    if isinstance(x, tuple):
        kids = x
    elif is_dataclass(x):
        kids = [getattr(x, f.name) for f in fields(x)]
    else:
        return
    for k in kids:
        yield from _nodes(k)


def _normal_diffs(pairs):
    """The ring normal form of a - b for each (a, b), one atom table for
    all. Returns (polys, atoms)."""
    polys, atoms = FD.ring_polys([t for ab in pairs for t in ab])
    return [P.sub(polys[2 * k], polys[2 * k + 1])
            for k in range(len(pairs))], atoms


# ---------------------------------------------------------------- hyp

def _hyp(prop, gamma):
    """§5.3 method 1: prop is in gamma, or follows from gamma's ordering
    items by reflexive-transitive closure. P1's gamma is always ()."""
    if prop in gamma:
        return ("hyp", ())
    # An edge (x, y, strict) says x < y, or x <= y. An interval item in
    # gamma is its two ordering facts.
    edges = [(b, a, s) for item in gamma for a, b, s in _rel_senses(item)]
    if isinstance(prop, NonZero):
        ok = (_below(ZERO, prop.e, True, edges)
              or _below(prop.e, ZERO, True, edges))
    elif prop.op == "==":
        ok = (_below(prop.lhs, prop.rhs, False, edges)
              and _below(prop.rhs, prop.lhs, False, edges))
    else:
        ok = all(_below(b, a, s, edges) for a, b, s in _senses(prop))
    return ("hyp", ()) if ok else None


def _below(x, y, strict, edges):
    """x < y (strict) or x <= y follows from the edges, as trees."""
    seen, todo = set(), [(x, False)]
    while todo:
        node, s = todo.pop()
        if node == y and (s or not strict):
            return True
        if (node, s) not in seen:
            seen.add((node, s))
            todo.extend((b, s or st) for a, b, st in edges if a == node)
    return False


# ---------------------------------------------------------- range, linear

def _linear(prop, dom):
    """§5.3 methods 2 and 3: Fourier–Motzkin over ℚ on the negated goal,
    dom's items and the sign facts of the constants in prop or dom. Every
    non-constant monomial is a variable, so only the linear fragment is
    used."""
    names = {n.name for n in _nodes((prop, dom)) if isinstance(n, Const)}
    facts = [(entry, s) for name, (entry, fact) in SIGN_FACTS.items()
             if name in names for s in _rel_senses(fact)]
    facts += [(name, c) for name, _, c in atom_facts((prop, dom))]
    items = [s for item in dom for s in _rel_senses(item)]
    for a, b, strict in _senses(prop):
        # The negation of a - b > 0 is b - a >= 0, and of >= it is >.
        pairs = [(b, a, not strict)] + [s for _, s in facts] + items
        polys, _ = _normal_diffs([(x, y) for x, y, _ in pairs])
        cons = [(p, s) for p, (_, _, s) in zip(polys, pairs)]
        if _feasible(cons):
            continue
        # Deletion filter: keep the negated goal, drop the sign facts
        # first, then the domain items from last to first, keeping each
        # drop that leaves the set infeasible.
        keep = list(range(len(cons)))
        nf = len(facts)
        for k in list(range(1, 1 + nf)) + list(range(len(cons) - 1, nf, -1)):
            trial = [j for j in keep if j != k]
            if not _feasible([cons[j] for j in trial]):
                keep = trial
        cites = _dedup(facts[j - 1][0] for j in keep if 1 <= j <= nf)
        return ("range" if any(j > nf for j in keep) else "linear", cites)
    return None


def atoms_of(x, head):
    """The argument w of each distinct atom head(w) of x (distinct by the
    ring normal form of w, §6.2's atom identity), in first-seen order.
    Raises Refused like ring."""
    args = [n.arg for n in _nodes(x) if isinstance(n, App) and n.fn == head]
    polys = FD.ring_polys(args)[0] if args else []
    seen, out = set(), []
    for w, p in zip(args, polys):
        if P.frozen(p) not in seen:
            seen.add(P.frozen(p))
            out.append(w)
    return out


def atom_facts(x):
    """ATOM_FACT_RULE: (entry name, w, (a, b, False)) for each ATOM_FACTS
    entry in ENTRIES and each distinct atom of its head in x, the fact's
    statement at w read as a - b >= 0, non-strict: sqrt w >= 0, 1 - cos w
    >= 0, cos w + 1 >= 0. Facts in ATOM_FACTS order, atoms in first-seen
    order. Raises Refused like ring."""
    out = []
    for name, head in ATOM_FACTS.items():
        entry = ENTRIES.get(name)
        if entry is None:
            continue
        for w in atoms_of(x, head):
            st = subst(replace(entry.statement, dom=()), {entry.schema[0]: w})
            (a, b, _), = _senses(st)
            out.append((name, w, (a, b, False)))
    return out


def _feasible(cons):
    """Fourier–Motzkin over ℚ. Each constraint is (p, strict), meaning
    p > 0 or p >= 0 for a polynomial p read linearly: each non-constant
    monomial is one variable. True when some rational point satisfies all
    of them."""
    return refutation(cons) is None


def refutation(cons):
    """Fourier–Motzkin over ℚ on `cons` as _feasible reads them, keeping
    for each derived constraint the multipliers of the originals it came
    from. None when the set is feasible; otherwise the Farkas witness of
    the first violated constraint: {index: Fraction > 0}, whose combination
    of the originals is a constant k with k < 0, or k = 0 and some used
    constraint strict. Exact with strict constraints: a combination is
    strict when either parent is. The discharge search (search.py) hands
    this witness to the trusted checker, which re-checks it (E29)."""
    rows = [(dict(p), s, {j: Fraction(1)}) for j, (p, s) in enumerate(cons)]
    while True:
        var = next((m for p, _, _ in rows for m in p if m != P.ONE_MONO), None)
        if var is None:
            for p, s, mult in rows:
                c = P.const_value(p)
                if not (c > 0 if s else c >= 0):
                    return mult
            return None
        pos = [r for r in rows if r[0].get(var, 0) > 0]
        neg = [r for r in rows if r[0].get(var, 0) < 0]
        rest = [r for r in rows if var not in r[0]]
        for (p, sp, mp), (q, sq, mq) in itertools.product(pos, neg):
            # -q[var] * p + p[var] * q has no `var`: both multipliers > 0.
            a, b = -q[var], p[var]
            r = P.add(P.scale(p, a), P.scale(q, b))
            mult = {j: a * mp.get(j, 0) + b * mq.get(j, 0)
                    for j in mp.keys() | mq.keys()}
            rest.append((r, sp or sq, mult))
        rows = rest


# ---------------------------------------------------------------- sign

def _sign(prop):
    """§5.3 method 4. The goal as written, then its ring normal form, is a
    positive rational plus even powers with positive coefficients, or a
    one-atom quadratic with a positive leading coefficient and a negative
    discriminant. E20: a non-strict goal also accepts a zero constant.
    `e # 0` is tried as e > 0."""
    senses = _senses(prop)
    if not senses:
        return None
    a, b, strict = senses[0]
    written = a if b == ZERO else Add(a, Neg(b))
    if _written_sum(written, strict):
        return ("sign", ())
    [e], _ = _normal_diffs([(a, b)])
    if _normal_sum(e, strict) or _quadratic(e):
        return ("sign", ())
    return None


def _pos_rational(t):
    q = FD.rational_value(t)
    return q is not None and q > 0


def _even_power(t):
    """t is an even power, times or over positive rationals, as written."""
    if isinstance(t, Pow):
        return t.n > 0 and t.n % 2 == 0
    if isinstance(t, Mul):
        parts = (t.a, t.b)
        return (any(_even_power(u) for u in parts)
                and all(_even_power(u) or _pos_rational(u) for u in parts))
    if isinstance(t, Div):
        return _even_power(t.a) and _pos_rational(t.b)
    return False


def _written_sum(t, strict):
    const, todo = Fraction(0), [t]
    while todo:
        u = todo.pop()
        if isinstance(u, Add):
            todo += [u.a, u.b]
        elif (q := FD.rational_value(u)) is not None:
            const += q
        elif not _even_power(u):
            return False
    return const > 0 or (not strict and const == 0)


def _normal_sum(e, strict):
    const = P.const_value(e)
    even = all(c > 0 and all(k % 2 == 0 for _, k in m)
               for m, c in e.items() if m != P.ONE_MONO)
    return even and (const > 0 or (not strict and const == 0))


def _quadratic(e):
    atoms = {i for m in e for i, _ in m}
    if len(atoms) != 1:
        return False
    i = atoms.pop()
    if P.degree_in(e, i) != 2:
        return False
    a, b = e.get(((i, 2),), 0), e.get(((i, 1),), 0)
    return a > 0 and b * b - 4 * a * P.const_value(e) < 0


# ---------------------------------------------------------------- sign product

def _sign_goal(t, sign, dom):
    """The sub-obligation t # 0 (sign 0), t > 0 (1) or t < 0 (-1) at dom."""
    prop = (NonZero(t) if sign == 0
            else Rel(">" if sign > 0 else "<", t, ZERO))
    return with_domain(prop, dom)


def rel_goal(t, r, dom):
    """The sub-obligation t # 0 (r '# 0') or t r 0 at dom."""
    return with_domain(NonZero(t) if r == "# 0" else Rel(r, t, ZERO), dom)


# A factor's relations, in the order they are tried (E53): strict first,
# then non-strict. The sign each claims, for the parity.
STRICT_RELATIONS = (">", "<")
NONSTRICT_RELATIONS = (">", "<", ">=", "<=")
RELATION_SIGN = {">": 1, ">=": 1, "<": -1, "<=": -1, "# 0": 0}


def product_form(prop):
    """For sign product: (a, b, want, relations) reading prop as the sign
    of e = a - b, want 0 (# 0), 1 (> or >=) or -1 (< or <=), and the
    relations its factors may take (E53: strict ones under a strict target,
    all four under a non-strict one), or None for an equation."""
    if isinstance(prop, NonZero):
        return prop.e, ZERO, 0, ("# 0",)
    if prop.op not in (">", "<", ">=", "<="):
        return None
    want = 1 if prop.op in (">", ">=") else -1
    rels = STRICT_RELATIONS if prop.op in (">", "<") else NONSTRICT_RELATIONS
    return prop.lhs, prop.rhs, want, rels


def split_relations(rels, s):
    """The relations a content split's one factor p may take, in order: those
    whose sign is s (s = 0: '# 0')."""
    return tuple(r for r in rels if RELATION_SIGN[r] == s)


def splits(c, prop):
    """E18: a content split is tried when c is a rational other than 0 and
    1, except c = -1 under a non-strict target (E53): there p's sign goal
    is the key's own proposition restated, and splitting it off would only
    nest the factorisation the key itself reaches."""
    return c != 1 and not (c == -1 and isinstance(prop, Rel)
                           and prop.op in (">=", "<="))


def _as_term(p, atoms):
    """p as a Term, a bare atom as its own term, so that cite sees the
    atom's tree (sqrt 3, not 1*sqrt 3)."""
    if len(p) == 1:
        [(m, c)] = p.items()
        if c == 1 and len(m) == 1 and m[0][1] == 1:
            return atoms[m[0][0]]
    return residual.poly_term(p, atoms)


def _product(prop, dom, gamma, split, depth=0):
    """§5.3 method 5 for every ordering and # 0 (E53): (i) E18's content
    split, then (ii) a factorisation into factors of strictly lower degree,
    each factor's relation strict first, then non-strict under a
    non-strict target."""
    form = product_form(prop)
    if form is None:
        return None
    a, b, want, rels = form
    [e], atoms = _normal_diffs([(a, b)])
    if not e:
        return None
    c, p = P.content_normal(e)
    if split and splits(c, prop):
        # e = c*p: p # 0, or p's sign times c's sign is the goal's.
        s = want * (1 if c > 0 else -1)
        for r in split_relations(rels, s):
            t = _tag(rel_goal(_as_term(p, atoms), r, dom), gamma, split=False,
                     depth=depth)
            if t != NONE:
                return ("sign product", t[1])
    found = normalised_factors(e, atoms) if depth < FACTOR_DEPTH else None
    if not found:
        return None
    # Each factor's relation, and a choice whose product, with the content's
    # sign, has the goal's sign. The content times the factors is e exactly.
    c, factors = found
    options = []
    for f in factors:
        tagged = [(r, _tag(rel_goal(f, r, dom), gamma, split=True,
                           depth=depth + 1))
                  for r in rels]
        options.append([(r, t) for r, t in tagged if t != NONE])
    for choice in itertools.product(*options):
        if want == 0 or ((1 if c > 0 else -1)
                         * math.prod(RELATION_SIGN[r] for r, _ in choice)) == want:
            return ("sign product",
                    _dedup(c for _, t in choice for c in t[1]))
    return None


def normalised_factors(p, atoms):
    """(c, factors) with p = c * f1 * ... * fn exactly: factor_rational_roots'
    factorisation, each factor divided by its leading coefficient so that it
    is positive, and c their product (E53: the content takes the sign), or
    None."""
    polys = _factor_polys(p)
    if polys is None:
        return None
    c, out = Fraction(1), []
    for f in polys:
        lc, monic = P.content_normal(f)
        c *= lc
        out.append(residual.poly_term(monic, atoms))
    return c, out


def factor_rational_roots(p, atoms):
    """An untrusted factorisation of p, univariate in one atom, into factors
    of strictly lower degree, found by the rational root test on p's
    coefficients. Returns a list of factor Terms (built with
    residual.poly_term), or None when no rational root exists or p is not
    univariate. 1 + x^3 gives [1 + x, x^2 - x + 1], up to term shape: only
    each factor's sign obligation matters. Returns None when |a0| or |an|
    (as integers) exceeds ROOT_TEST_BOUND, so the test stays cheap; a
    factorisation it misses only weakens a tag."""
    polys = _factor_polys(p)
    return None if polys is None else [residual.poly_term(f, atoms)
                                       for f in polys]


def _factor_polys(p):
    """factor_rational_roots' factors as polynomials, [atom - root,
    quotient], whose product is p; or None."""
    used = {i for m in p for i, _ in m}
    if len(used) != 1:
        return None
    i = used.pop()
    n = P.degree_in(p, i)
    if n < 2:
        return None
    coeffs = [p.get(((i, k),) if k else P.ONE_MONO, Fraction(0))
              for k in range(n + 1)]
    # Integer coefficients with the same roots, for the candidate list.
    lcm = math.lcm(*(c.denominator for c in coeffs))
    ints = [int(c * lcm) for c in coeffs]
    low = next(k for k, c in enumerate(ints) if c)
    if max(abs(ints[low]), abs(ints[n])) > ROOT_TEST_BOUND:
        return None
    if low:
        root = Fraction(0)
    else:
        root = next((r for r in _candidates(ints[0], ints[n])
                     if sum(c * r ** k for k, c in enumerate(coeffs)) == 0),
                    None)
        if root is None:
            return None
    # Synthetic division by (atom - root).
    quot = [Fraction(0)] * n
    quot[n - 1] = coeffs[n]
    for k in range(n - 1, 0, -1):
        quot[k - 1] = coeffs[k] + root * quot[k]
    q = {}
    for k, c in enumerate(quot):
        q = P.add(q, P.scale(P.atom(i, k) if k else P.const(1), c))
    linear = P.sub(P.atom(i), P.const(root))
    if P.mul(linear, q) != p:  # a factoriser bug, caught before it is used
        return None
    return [linear, q]


def _divisors(n):
    n = abs(n)
    small = [d for d in range(1, math.isqrt(n) + 1) if n % d == 0]
    return sorted(set(small + [n // d for d in small]))


def _candidates(a0, an):
    """The rational root test's candidates ±d/e, d | a0, e | an, smallest
    first."""
    found = {Fraction(s * d, e) for d in _divisors(a0) for e in _divisors(an)
             for s in (1, -1)}
    return sorted(found, key=lambda r: (abs(r), r < 0))


# ---------------------------------------------------------------- cite

def _cite(prop, dom, gamma, depth=0):
    """§5.3 method 6: an ENTRIES statement whose instantiated conclusion is
    prop, or is `a > 0` / `0 < a` for prop `a # 0`, `a >= 0` or `0 <= a`,
    and whose instantiated hypotheses at dom are none of them tagged
    none."""
    for name, entry in ENTRIES.items():
        conclusion = replace(entry.statement, dom=())
        inst = _implies(conclusion, prop, entry.schema)
        if inst is None or set(inst) != set(entry.schema):
            continue
        cites = [name]
        for h in entry.hyps:
            t = _tag(with_domain(subst(h, inst), dom), gamma, split=True,
                     depth=depth)
            if t == NONE:
                break
            cites += t[1]
        else:
            return ("cite", _dedup(cites))
    return None


def _implies(conclusion, prop, schema):
    """The instantiation under which `conclusion` implies prop
    syntactically, or None."""
    inst = _match(conclusion, prop, schema, {})
    if inst is not None or not isinstance(conclusion, Rel):
        return inst
    if conclusion.op == ">" and conclusion.rhs == ZERO:
        a = conclusion.lhs
    elif conclusion.op == "<" and conclusion.lhs == ZERO:
        a = conclusion.rhs
    else:
        return None
    if isinstance(prop, NonZero):
        target = prop.e
    elif prop.op == ">=" and prop.rhs == ZERO:
        target = prop.lhs
    elif prop.op == "<=" and prop.lhs == ZERO:
        target = prop.rhs
    else:
        return None
    return _match(a, target, schema, {})


def _match(pat, t, schema, inst):
    """First-order matching of pat against t, as trees, binding the schema
    variables of pat. Returns the extended instantiation, or None."""
    if inst is None:
        return None
    if isinstance(pat, Var) and pat.name in schema:
        if pat.name in inst:
            return inst if inst[pat.name] == t else None
        return {**inst, pat.name: t}
    if isinstance(pat, tuple):
        if not isinstance(t, tuple) or len(pat) != len(t):
            return None
        for x, y in zip(pat, t):
            inst = _match(x, y, schema, inst)
        return inst
    if not is_dataclass(pat) or type(pat) is not type(t):
        return inst if pat == t else None
    for f in fields(pat):
        inst = _match(getattr(pat, f.name), getattr(t, f.name), schema, inst)
    return inst
