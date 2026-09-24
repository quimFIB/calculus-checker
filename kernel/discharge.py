"""Discharge's certificate checkers and the exact-value rewrite.

Trusted (DESIGN.md §15.2 item 5; p1_expected E28-E31 and DISCHARGE_RULE,
which this module implements paragraph by paragraph). An obligation is
discharged only when a certificate for it is accepted here. The search that
proposes certificates is untrusted (search.py), so everything this module
checks against is rebuilt from the key alone: the target, the constraint
set, and every sub-obligation's key. A certificate names constraints and
supplies witnesses. It can never supply a hypothesis.

A certificate is plain data, a dict whose 'method' picks the checker:

  {'method': 'farkas', 'sense': s, 'multipliers': {label: q}}   methods 2, 3
  {'method': 'hyp', 'member': i} | {'method': 'hyp', 'chain': (i, ...)}
  {'method': 'sign', 'sense': s, 'const': c0, 'squares': ((c, t, k), ...)}
  {'method': 'sign product', 'sense': s, 'content': c,
   'factors': ((f, r, cert), ...)}
  {'method': 'cite', 'entry': name, 'inst': {v: t}, 'hyps': ((h, cert), ...)}
  {'method': 'norm_num'}                                         a leaf

Rationals are int or Fraction, terms are Terms, and a field the checker does
not know rejects. `verdict(key, cert)` gives (tag, None) on acceptance and
(None, reason) on rejection, the reason being the first rule the certificate
breaks (REASONS). `check(key, cert)` gives the tag or None. Acceptance means
the key's proposition holds at every point of its domain where its terms
are defined; definedness is owed separately, by the keys the formers charged
(E6, E26). Rejection only withholds a discharge.

`exact_values(key)` is E31: every ENTRIES equation with no schema variable
and no hypothesis, matched as rewrite matches (REWRITE_RULE steps 3-4),
rewritten everywhere in the key to a fixed point. The dispatcher applies it
first, to the key and to every sub-obligation.

Nothing here searches, and nothing raises a refusal of its own: a
terms.Refused met inside a check (ring meeting an Int or D node, a zero
divisor) is a rejection (E30).

**Seams** (kernel/ARCHITECTURE.md §7). Each rule a planted bug removes is
its own small function, looked up by name at call time: `_ends`,
`_is_fact`, `_multiplier_ok`, `_goal_used`, `_contradicts`, `_square_ok`,
`_constant_ok`, `_sign_identity`, `_parity_ok`, `_factors_hold`,
`_hyps_hold`. Keep their names and signatures, and call them only as
written here.
"""

from dataclasses import replace
from fractions import Fraction

import field as FD
import poly as P
from entries import ENTRIES
from terms import (Add, App, Const, Interval, Mul, Neg, NonZero, Num, Pow,
                   Refused, Rel, Term, Var, _kids, _map, check_goal, fv, lit,
                   subst, trees, with_domain)

GOAL = ("goal",)
ZERO = Num(0)
ORDERINGS = ("<", "<=", ">", ">=")

# The reasons a certificate is rejected, in the order DISCHARGE_RULE states
# the rules. A rejected child is "child-rejected/" + its own reason.
REASONS = (
    "not-a-proposition", "equation", "malformed", "unknown-method",
    "unknown-field", "bad-sense", "unknown-label", "multiplier-not-positive",
    "goal-unused", "not-constant", "positive-constant", "zero-without-strict",
    "unknown-item", "not-hypothesis-item", "not-member", "not-ordering",
    "chain-broken", "chain-ends", "chain-not-strict", "bad-square",
    "constant-too-small", "identity-fails", "non-strict-target",
    "zero-content", "bad-relation", "parity", "unknown-entry",
    "entry-not-ordering", "bad-instance", "schema-not-in-conclusion",
    "conclusion-does-not-imply", "hypothesis-count", "hypothesis-mismatch",
    "not-literal-true", "child-rejected", "refused")


class _Reject(Exception):
    def __init__(self, reason):
        super().__init__(reason)
        self.reason = reason


def _need(ok, reason):
    if not ok:
        raise _Reject(reason)


# ---------------------------------------------------------------- dispatcher

def check(key, cert):
    """The tag (method, cites) when `cert` is accepted for `key`, else
    None."""
    return verdict(key, cert)[0]


def verdict(key, cert):
    """(tag, None) when `cert` is accepted for `key`, else (None, reason).
    Never raises for a well-formed key."""
    try:
        return _decide(key, cert), None
    except _Reject as r:
        return None, r.reason
    except Refused as r:
        return None, "refused " + r.code


def _decide(key, cert):
    """The exact values first (E31), then the certificate's own checker.
    The entries used are prepended to the checker's cites."""
    _need(type(key) in (Rel, NonZero), "not-a-proposition")
    _need(type(key) is NonZero or key.op in ORDERINGS, "equation")
    key, used = exact_values(key)
    _need(type(cert) is dict and type(cert.get("method")) is str, "malformed")
    checker = _CHECKERS.get(cert["method"])
    _need(checker is not None, "unknown-method")
    method, cites = checker(key, cert)
    return method, _dedup(used + tuple(cites))


def _fields(cert, *names):
    _need(set(cert) == {"method", *names}, "unknown-field")


def _dedup(xs):
    return tuple(dict.fromkeys(xs))


def _prop(key):
    """The key's proposition, without its domain."""
    return replace(key, dom=())


def _rational(q):
    return type(q) is int or type(q) is Fraction


def _plain(t):
    """t is a well-formed Term (check_goal accepts it as a side) with no
    ?A, oo, Int or D node, so ring reads it and nothing is left unstated."""
    if not isinstance(t, Term):
        return False
    try:
        check_goal((Rel("==", t, t),))
    except Refused:
        return False
    return not any(trees(t))


def _polys(*terms):
    """Ring normal forms, one shared atom table (atoms opaque, §6.2)."""
    return FD.ring_polys(list(terms))[0]


# ---------------------------------------------------------------- targets

def _reading(rel):
    """An ordering a REL b read as g > 0 or g >= 0, with g = x - y: the
    pair ((x, y), strict)."""
    _need(type(rel) is Rel and rel.op in ORDERINGS, "not-ordering")
    a, b = rel.lhs, rel.rhs
    return {">": ((a, b), True), ">=": ((a, b), False),
            "<": ((b, a), True), "<=": ((b, a), False)}[rel.op]


def _target(key, sense):
    """The key read as g > 0 or g >= 0 (DISCHARGE_RULE, Targets). A # 0 key
    needs the sense '>' (g = e) or '<' (g = -e); an ordering takes none."""
    if type(key) is NonZero:
        _need(sense in (">", "<"), "bad-sense")
        return ((key.e, ZERO) if sense == ">" else (ZERO, key.e)), True
    _need(sense is None, "bad-sense")
    return _reading(_prop(key))


# ---------------------------------------------------------------- the constraint set

def _constants(x):
    """The named constants in a term, judgement, interval or tuple."""
    if type(x) is Const:
        return frozenset((x.name,))
    return frozenset().union(*map(_constants, _kids(x)))


def _ends(i, iv):
    """('dom', i, 'lo') and ('dom', i, 'hi') for Interval item i on v:
    v - lo and hi - v, each strict at an open end, and none for an infinite
    end. A seam (ARCHITECTURE.md §7)."""
    v, out = Var(iv.var), {}
    if isinstance(iv.lo, Term):
        out[("dom", i, "lo")] = (v, iv.lo, not iv.lo_closed)
    if isinstance(iv.hi, Term):
        out[("dom", i, "hi")] = (iv.hi, v, not iv.hi_closed)
    return out


def _is_fact(entry, consts):
    """An entry is a ('fact', name) constraint for a key when it has no
    schema variable and no hypothesis, states an ordering between closed
    terms, and mentions a constant the key does (pi_pos, e_gt_one). A seam
    (ARCHITECTURE.md §7)."""
    st = entry.statement
    return (not entry.schema and not entry.hyps and type(st) is Rel
            and st.op in ORDERINGS and not fv(st)
            and bool(_constants(st) & consts))


def _constraint_set(key, sense):
    """label -> (x, y, strict), meaning x - y > 0 (strict) or >= 0, built
    from the key alone (DISCHARGE_RULE, The constraint set). ('goal',) is
    the negated target; a NonZero or == item, and an index the domain does
    not have, is no label."""
    (a, b), strict = _target(key, sense)
    cs = {GOAL: (b, a, not strict)}
    for i, item in enumerate(key.dom):
        if type(item) is Interval:
            cs.update(_ends(i, item))
        elif type(item) is Rel and item.op in ORDERINGS:
            (x, y), s = _reading(item)
            cs[("dom", i, "rel")] = (x, y, s)
    consts = _constants(key)
    for name, entry in ENTRIES.items():
        if _is_fact(entry, consts):
            (x, y), s = _reading(entry.statement)
            cs[("fact", name)] = (x, y, s)
    return cs


# ---------------------------------------------------------------- Farkas (methods 2, 3)

def _multiplier_ok(m):
    """A multiplier is a rational > 0; zero is written by omission. A seam
    (ARCHITECTURE.md §7)."""
    return _rational(m) and m > 0


def _goal_used(mults):
    """The negated goal has a multiplier, so the witness is not about the
    domain alone. A seam (ARCHITECTURE.md §7)."""
    return GOAL in mults


def _contradicts(k, strict):
    """The combination, >= 0 (or > 0 when a strict constraint is used),
    equals the constant k: a contradiction when k < 0, or k = 0 with a
    strict constraint. A seam (ARCHITECTURE.md §7)."""
    return k < 0 or (k == 0 and strict)


def _farkas(key, cert):
    """E29: a positive combination of the key's constraints, the negated
    goal among them, that ring-normalises to a contradictory constant. Sound
    for polynomials over opaque atoms: a positive combination of
    non-negative quantities is non-negative. Tag 'range' when a domain
    constraint is used, else 'linear'; cites the facts used, ENTRIES
    order."""
    _fields(cert, "sense", "multipliers")
    cs = _constraint_set(key, cert["sense"])
    mults = cert["multipliers"]
    _need(type(mults) is dict, "malformed")
    for label, m in mults.items():
        _need(label in cs, "unknown-label")
        _need(_multiplier_ok(m), "multiplier-not-positive")
    _need(_goal_used(mults), "goal-unused")
    labels = list(mults)
    terms = [t for label in labels for t in cs[label][:2]]
    polys = _polys(*terms) if terms else []
    total = {}
    for j, label in enumerate(labels):
        h = P.sub(polys[2 * j], polys[2 * j + 1])
        total = P.add(total, P.scale(h, Fraction(mults[label])))
    _need(P.is_const(total), "not-constant")
    k = P.const_value(total)
    if not _contradicts(k, any(cs[label][2] for label in labels)):
        raise _Reject("positive-constant" if k > 0 else "zero-without-strict")
    used = any(label[0] == "dom" for label in labels)
    cites = tuple(n for n in ENTRIES if ("fact", n) in mults)
    return ("range" if used else "linear"), cites


# ---------------------------------------------------------------- hyp (method 1)

def _item(dom, i):
    """Domain item i, which must be a relation or NonZero: an Interval is a
    range, and belongs to a Farkas certificate."""
    _need(type(i) is int and 0 <= i < len(dom), "unknown-item")
    _need(type(dom[i]) in (Rel, NonZero), "not-hypothesis-item")
    return dom[i]


def _order(rel):
    """An ordering read as (lo, hi, strict): lo < hi or lo <= hi."""
    (hi, lo), strict = _reading(rel)
    return lo, hi, strict


def _hyp(key, cert):
    """§5.3 method 1. member: the proposition is item i as a tree, or it is
    e # 0 and item i is e > 0, e < 0, 0 < e or 0 > e. chain: items linked
    hi to lo as trees, giving lo1 R hin, strict when some link is; the
    proposition has the same two ends and is strict only if R is, and e # 0
    needs a strict chain between e and 0."""
    prop = _prop(key)
    if "member" in cert:
        _fields(cert, "member")
        item = _item(key.dom, cert["member"])
        signed = (type(prop) is NonZero and type(item) is Rel
                  and item.op in ("<", ">")
                  and (item.lhs, item.rhs) in ((prop.e, ZERO), (ZERO, prop.e)))
        _need(item == prop or signed, "not-member")
        return "hyp", ()
    _fields(cert, "chain")
    chain = cert["chain"]
    _need(type(chain) is tuple and len(chain) > 0, "malformed")
    links = [_order(_item(key.dom, i)) for i in chain]
    for (_, hi, _), (lo, _, _) in zip(links, links[1:]):
        _need(hi == lo, "chain-broken")
    lo, hi, strict = links[0][0], links[-1][1], any(s for _, _, s in links)
    if type(prop) is NonZero:
        _need((lo, hi) in ((prop.e, ZERO), (ZERO, prop.e)), "chain-ends")
        _need(strict, "chain-not-strict")
    else:
        plo, phi, pstrict = _order(prop)
        _need((plo, phi) == (lo, hi), "chain-ends")
        _need(strict or not pstrict, "chain-not-strict")
    return "hyp", ()


# ---------------------------------------------------------------- sign (method 4)

def _square_ok(c, s, k):
    """A term c * s^k of a sign certificate: c a rational > 0, k an even
    integer >= 2, s a plain term. A seam (ARCHITECTURE.md §7)."""
    return (_rational(c) and c > 0 and type(k) is int and k >= 2
            and k % 2 == 0 and _plain(s))


def _constant_ok(c0, strict):
    """c0 > 0 for a strict target, c0 >= 0 for a non-strict one (E20). A
    seam (ARCHITECTURE.md §7)."""
    return c0 > 0 if strict else c0 >= 0


def _sign_identity(g, total):
    """ring_equal(g, total), as polynomials over opaque atoms. A seam
    (ARCHITECTURE.md §7)."""
    p, q = _polys(g, total)
    return p == q


def _sign(key, cert):
    """§5.3 method 4: g = c0 + sum ci*si^ki, a polynomial identity over
    opaque atoms, so it holds whatever value an atom takes. The quadratic's
    discriminant is the search's rule; the certificate is the completed
    square."""
    _fields(cert, "sense", "const", "squares")
    (a, b), strict = _target(key, cert["sense"])
    c0, squares = cert["const"], cert["squares"]
    _need(_rational(c0) and type(squares) is tuple, "malformed")
    total = lit(c0)
    for sq in squares:
        _need(type(sq) is tuple and len(sq) == 3, "malformed")
        _need(_square_ok(*sq), "bad-square")
        c, s, k = sq
        total = Add(total, Mul(lit(c), Pow(s, k)))
    _need(_constant_ok(c0, strict), "constant-too-small")
    _need(_sign_identity(Add(a, Neg(b)), total), "identity-fails")
    return "sign", ()


# ---------------------------------------------------------------- sign product (method 5)

def _product_identity(g, total):
    """ring_equal(g, c * f1 * ... * fn), over opaque atoms."""
    p, q = _polys(g, total)
    return p == q


def _parity_ok(c, rels):
    """sign(c) times (-1) to the number of '<' factors is +1. A seam
    (ARCHITECTURE.md §7)."""
    return (c > 0) == (sum(r == "<" for r in rels) % 2 == 0)


def _factors_hold(dom, factors):
    """Each factor's sub-obligation, fj # 0, fj > 0 or fj < 0 at the
    parent's domain, accepted by its own certificate. Returns the union of
    their cites. A seam (ARCHITECTURE.md §7)."""
    cites = ()
    for f, r, cert in factors:
        prop = NonZero(f) if r == "# 0" else Rel(r, f, ZERO)
        tag, why = verdict(with_domain(prop, dom), cert)
        if tag is None:
            raise _Reject("child-rejected/" + why)
        cites += tag[1]
    return cites


def _product(key, cert):
    """§5.3 method 5, for >, < and # 0 keys: g = c * f1 * ... * fn by ring,
    each factor's sign by its own certificate, and for an ordering the
    parity. E18's content split is the one-factor case. 'Strictly lower
    degree' is the search's termination rule; this check terminates by
    recursion on a finite certificate (E30)."""
    _fields(cert, "sense", "content", "factors")
    sense, c, factors = cert["sense"], cert["content"], cert["factors"]
    nonzero = type(key) is NonZero
    if nonzero:
        _need(sense == "#", "bad-sense")
        g = key.e
    else:
        _need(key.op in (">", "<"), "non-strict-target")
        (a, b), _ = _target(key, sense)
        g = Add(a, Neg(b))
    _need(_rational(c) and c != 0, "zero-content")
    _need(type(factors) is tuple, "malformed")
    total = lit(c)
    for fac in factors:
        _need(type(fac) is tuple and len(fac) == 3 and _plain(fac[0]),
              "malformed")
        _need(fac[1] == "# 0" if nonzero else fac[1] in (">", "<"),
              "bad-relation")
        total = Mul(total, fac[0])
    _need(_product_identity(g, total), "identity-fails")
    if not nonzero:
        _need(_parity_ok(c, [r for _, r, _ in factors]), "parity")
    return "sign product", _factors_hold(key.dom, factors)


# ---------------------------------------------------------------- cite (method 6)

def _implies(conclusion, prop):
    """TAG_RULES' syntactic implication: the same tree, or a conclusion
    `a > 0` / `0 < a` for a proposition `a # 0`, `a >= 0` or `0 <= a`."""
    if conclusion == prop:
        return True
    if type(conclusion) is not Rel:
        return False
    if conclusion.op == ">" and conclusion.rhs == ZERO:
        a = conclusion.lhs
    elif conclusion.op == "<" and conclusion.lhs == ZERO:
        a = conclusion.rhs
    else:
        return False
    return prop in (NonZero(a), Rel(">=", a, ZERO), Rel("<=", ZERO, a))


def _hyps_hold(dom, hyps, children):
    """Exactly one child per instantiated hypothesis, in the entry's order,
    each naming that hypothesis and accepted at the key's domain. Returns
    their cites. A seam (ARCHITECTURE.md §7)."""
    _need(type(children) is tuple and len(children) == len(hyps),
          "hypothesis-count")
    cites = ()
    for h, child in zip(hyps, children):
        _need(type(child) is tuple and len(child) == 2, "malformed")
        _need(child[0] == h, "hypothesis-mismatch")
        tag, why = verdict(with_domain(h, dom), child[1])
        if tag is None:
            raise _Reject("child-rejected/" + why)
        cites += tag[1]
    return cites


def _cite(key, cert):
    """§5.3 method 6: an ENTRIES ordering or NonZero statement, its schema
    bound exactly, every schema variable in its conclusion, the instantiated
    conclusion implying the proposition, and each instantiated hypothesis
    accepted. Each inst value is then a subterm of the proposition, whose
    formers were charged where it entered, so a cite charges none (E10)."""
    _fields(cert, "entry", "inst", "hyps")
    name, inst = cert["entry"], cert["inst"]
    entry = ENTRIES.get(name) if type(name) is str else None
    _need(entry is not None, "unknown-entry")
    st = entry.statement
    _need(type(st) is NonZero or (type(st) is Rel and st.op in ORDERINGS),
          "entry-not-ordering")
    _need(type(inst) is dict and set(inst) == set(entry.schema)
          and all(_plain(t) for t in inst.values()), "bad-instance")
    _need(set(entry.schema) <= fv(_prop(st)), "schema-not-in-conclusion")
    st = subst(st, inst)
    _need(_implies(_prop(st), _prop(key)), "conclusion-does-not-imply")
    return "cite", _dedup((name,) + _hyps_hold(key.dom, st.dom, cert["hyps"]))


# ---------------------------------------------------------------- the leaf

def _norm_num(key, cert):
    """A literal proposition that norm_num decides True (E7)."""
    _fields(cert)
    _need(FD.norm_num(key) is True, "not-literal-true")
    return "norm_num", ()


_CHECKERS = {"farkas": _farkas, "hyp": _hyp, "sign": _sign,
             "sign product": _product, "cite": _cite, "norm_num": _norm_num}


# ---------------------------------------------------------------- exact values (E31)

def _exact_entries():
    """ENTRIES' equations with no schema variable and no hypothesis, in
    ENTRIES order: §6.8's exact values (EXACT_VALUE_ENTRIES)."""
    return [(name, e.statement) for name, e in ENTRIES.items()
            if type(e.statement) is Rel and e.statement.op == "=="
            and not e.schema and not e.hyps]


def _matches(lhs, s):
    """REWRITE_RULE steps 3-4, as kernel._rewrite applies them: an
    application matches h(b) for the same builtin h when the arguments have
    the same ring normal form; anything else matches as a tree."""
    if type(lhs) is App:
        if type(s) is not App or s.fn != lhs.fn:
            return False
        p, q = _polys(lhs.arg, s.arg)
        return p == q
    return s == lhs


def exact_values(key):
    """E31: (key', entries used) where key' is `key` (proposition and
    domain) with every exact value rewritten, children before parents, to a
    fixed point, and rebuilt with E5. The entries are listed in first-use
    order. Each rewrite replaces an application by a right side holding no
    application (true of every exact value in ENTRIES), so it terminates.
    It preserves the key's truth: each exact value is an equation of the
    cite library, matched only where the argument is ring-equal to its own.
    Raises Refused like ring, when a matched argument holds an Int or D
    node, and like a constructor when a rewrite makes an RPow's exponent
    literal (D17)."""
    values, used = _exact_entries(), []

    def rewrite(x):
        x = _map(rewrite, x)
        for name, st in values:
            if _matches(st.lhs, x):
                used.append(name)
                return st.rhs
        return x

    while True:
        new = rewrite(key)
        if new == key:
            break
        key = new
    if type(key) in (Rel, NonZero):
        key = with_domain(_prop(key), key.dom)
    return key, _dedup(used)
