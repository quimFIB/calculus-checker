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
  {'method': 'sign node', 'parts': ((r, cert), ...)}           method 5b
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
`_is_fact`, `_atom_fact`, `_multiplier_ok`, `_goal_used`, `_contradicts`,
`_square_ok`,
`_constant_ok`, `_sign_identity`, `_parity_ok`, `_relation_ok`, `_factors_hold`,
`_hyps_hold`, and the regularity checker's `_reg_class_ok`, `_reg_fields`,
`_reg_rule`, `_reg_children`, `_interior`, `_reg_sides`,
`_reg_side_count_ok`, `_reg_side_prop` and `_reg_side_holds`. Keep their names and signatures, and call them only as
written here.
"""

from dataclasses import replace
from fractions import Fraction
from types import MappingProxyType

import field as FD
import poly as P
from entries import ENTRIES
import domains
from terms import (Add, App, BUILTINS, Const, Div, Interval, Mul, Neg, NonZero,
                   Num, Pow, RPow, Refused, Reg, Rel, Term, Var, _kids,
                   check_goal, fv, lit, subst, trees, with_domain)
from terms import _fields as _node_fields

GOAL = ("goal",)
ZERO = Num(0)
ORDERINGS = ("<", "<=", ">", ">=")
SQRT_FACT = "sqrt_nonneg"  # E49: the sign fact read for each sqrt atom
# ATOM_FACT_RULE (E54, generalising E49): each atom sign fact and the head
# of the atoms it is read for. Its constraint is the entry's statement at
# the atom's argument, read as a target, non-strict. Each one's hypotheses
# are its atom's definedness (sqrt_nonneg) or none (cos is total), so a
# label needs no child. sin_nonneg_on and cos_nonneg_on are not here: their
# hypotheses are real conditions, and cite is their route. Read-only, as
# ENTRIES is: a row added here would extend what the checker assumes.
ATOM_FACTS = MappingProxyType({SQRT_FACT: "sqrt", "cos_le_one": "cos",
                               "cos_ge_neg_one": "cos"})

# The reasons a certificate is rejected, in the order DISCHARGE_RULE states
# the rules. A rejected child is "child-rejected/" + its own reason.
REASONS = (
    "not-a-proposition", "equation", "malformed", "unknown-method",
    "unknown-field", "bad-sense", "unknown-label", "multiplier-not-positive",
    "goal-unused", "not-constant", "positive-constant", "zero-without-strict",
    "unknown-item", "not-hypothesis-item", "not-member", "not-ordering",
    "chain-broken", "chain-ends", "chain-not-strict", "bad-square",
    "constant-too-small", "identity-fails",
    "zero-content", "bad-relation", "parity", "unknown-entry",
    "entry-not-ordering", "bad-instance", "schema-not-in-conclusion",
    "conclusion-does-not-imply", "hypothesis-count", "hypothesis-mismatch",
    "not-literal-true", "child-rejected", "refused", "too-deep",
    # the regularity checker's own (p1_expected REG_REASONS, in its order:
    # class-not-built, malformed, no-rule, wrong-rule, arity, side-count,
    # wrong-side, child-rejected, too-deep)
    "class-not-built", "no-rule", "wrong-rule", "arity", "side-count",
    "wrong-side")


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
    except RecursionError:  # a key or certificate deeper than the stack
        return None, "too-deep"


def _decide(key, cert):
    """The exact values first (E31), then the certificate's own checker.
    The entries used are prepended to the checker's cites. A Reg key goes
    to the regularity checker alone (E60): the exact values apply inside
    its sides, never to the Reg itself."""
    if type(key) is Reg:
        return _reg(key, cert)
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
    for name, head in ATOM_FACTS.items():
        for w in _atom_arguments(key, head):
            label = ("fact", name, w)
            c = _atom_fact(key, label)
            if c is not None:
                cs[label] = c
    return cs


def _atom_arguments(x, head):
    """The argument w of every atom head(w) in a term, judgement, interval
    or tuple."""
    out = [x.arg] if type(x) is App and x.fn == head else []
    for k in _kids(x):
        out += _atom_arguments(k, head)
    return out


def _atom_fact(key, label):
    """ATOM_FACT_RULE's label ('fact', name, u) (E49, E54): when name is one
    of ATOM_FACTS and in ENTRIES, and an atom h(w) of its head h occurs in
    the key's proposition or domain with ring_nf(w) = ring_nf(u), the
    constraint is the entry's statement at u read as a target, non-strict:
    sqrt u >= 0, 1 - cos u >= 0 or cos u + 1 >= 0. Else None. No child: at a
    point where the key's terms are defined that atom is defined, which is
    sqrt_nonneg's hypothesis u >= 0 (the former E26 charged where the sqrt
    entered), and the cos bounds have none. A seam (ARCHITECTURE.md §7)."""
    if not (type(label) is tuple and len(label) == 3
            and type(label[1]) is str and label[1] in ATOM_FACTS
            and label[1] in ENTRIES and _plain(label[2])):
        return None
    name, u = label[1], label[2]
    entry = ENTRIES[name]
    for w in _atom_arguments(key, ATOM_FACTS[name]):
        p, q = _polys(u, w)
        if p == q:
            (x, y), _ = _reading(_prop(subst(entry.statement,
                                             {entry.schema[0]: u})))
            return (x, y, False)
    return None


def _constraint(cs, key, label):
    """A label's constraint: from the set, or an atom label ('fact', name,
    u) matched by the ring normal form of its argument (ATOM_FACT_RULE)."""
    if label in cs:
        return cs[label]
    if type(label) is tuple and len(label) == 3 and label[0] == "fact":
        return _atom_fact(key, label)
    return None


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
    used = {}
    for label, m in mults.items():
        used[label] = _constraint(cs, key, label)
        _need(used[label] is not None, "unknown-label")
        _need(_multiplier_ok(m), "multiplier-not-positive")
    _need(_goal_used(mults), "goal-unused")
    labels = list(mults)
    terms = [t for label in labels for t in used[label][:2]]
    polys = _polys(*terms) if terms else []
    total = {}
    for j, label in enumerate(labels):
        h = P.sub(polys[2 * j], polys[2 * j + 1])
        total = P.add(total, P.scale(h, Fraction(mults[label])))
    _need(P.is_const(total), "not-constant")
    k = P.const_value(total)
    if not _contradicts(k, any(used[label][2] for label in labels)):
        raise _Reject("positive-constant" if k > 0 else "zero-without-strict")
    ranged = any(label[0] == "dom" for label in labels)
    facts = {label[1] for label in labels if label[0] == "fact"}
    cites = tuple(n for n in ENTRIES if n in facts)
    return ("range" if ranged else "linear"), cites


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
    """sign(c) times (-1) to the number of '<' and '<=' factors is +1. A
    seam (ARCHITECTURE.md §7)."""
    return (c > 0) == (sum(r in ("<", "<=") for r in rels) % 2 == 0)


def _relation_ok(r, nonzero, strict):
    """A factor's relation (SIGN_PRODUCT_NONSTRICT_RULE (a), E53): '# 0'
    under a # 0 key; '>' or '<' under a strict target; any of '>', '<',
    '>=' and '<=' under a non-strict one. A non-strict factor under a
    strict target could be 0, and the product with it. A seam
    (ARCHITECTURE.md §7)."""
    if nonzero:
        return r == "# 0"
    return r in ((">", "<") if strict else ORDERINGS)


def _factors_hold(dom, factors):
    """Each factor's sub-obligation, fj # 0 or fj rj 0 at the parent's
    domain, accepted by its own certificate. Returns the union of
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
    """§5.3 method 5, for every ordering and # 0 key (E53): g = c * f1 *
    ... * fn by ring, each factor's relation allowed by the target
    (_relation_ok), each factor's sign by its own certificate, and for an
    ordering the parity. Where the terms are defined each factor has its
    certified sign, so the product's sign is sign(c) times theirs: positive
    when every factor is strict, non-negative when one may be 0. E18's
    content split is the one-factor case. 'Strictly lower degree' is the
    search's termination rule; this check terminates by recursion on a
    finite certificate (E30)."""
    _fields(cert, "sense", "content", "factors")
    sense, c, factors = cert["sense"], cert["content"], cert["factors"]
    nonzero = type(key) is NonZero
    if nonzero:
        _need(sense == "#", "bad-sense")
        g, strict = key.e, True
    else:
        (a, b), strict = _target(key, sense)
        g = Add(a, Neg(b))
    _need(_rational(c) and c != 0, "zero-content")
    _need(type(factors) is tuple, "malformed")
    total = lit(c)
    for fac in factors:
        _need(type(fac) is tuple and len(fac) == 3 and _plain(fac[0]),
              "malformed")
        _need(_relation_ok(fac[1], nonzero, strict), "bad-relation")
        total = Mul(total, fac[0])
    _need(_product_identity(g, total), "identity-fails")
    if not nonzero:
        _need(_parity_ok(c, [r for _, r, _ in factors]), "parity")
    return "sign product", _factors_hold(key.dom, factors)


# ---------------------------------------------------------------- sign node (method 5b)
#
# E81, E82: the sign of a syntactic node from its children's certified
# signs, as sets of signs. Sound where the key's terms are defined, which is
# all any certificate claims: there a divisor is non-zero.

SIGN_SETS = {">": frozenset({1}), ">=": frozenset({1, 0}),
             "<": frozenset({-1}), "<=": frozenset({-1, 0}),
             "# 0": frozenset({1, -1})}


def _node_target(key):
    """(g, allowed signs): the key read as g # 0, or an ordering read as g
    against 0 on either side (E81, E82)."""
    if type(key) is NonZero:
        return key.e, SIGN_SETS["# 0"]
    (x, y), strict = _reading(_prop(key))
    if y == ZERO:
        return x, SIGN_SETS[">" if strict else ">="]
    if x == ZERO:
        return y, SIGN_SETS["<" if strict else "<="]
    raise _Reject("not-a-node")


def _node_children(g):
    if type(g) in (Div, Mul, Add):
        return (g.a, g.b)
    if type(g) in (Pow, Neg):
        return (g.base,) if type(g) is Pow else (g.a,)
    raise _Reject("not-a-node")


def _node_signs(g, sets):
    """The exact set of signs g can take where it is defined, from its
    children's sets (E82)."""
    t = type(g)
    if t is Neg:
        return frozenset(-s for s in sets[0])
    if t in (Mul, Div):
        a, b = sets
        if t is Div:
            b = b - {0}
        return frozenset(x * y for x in a for y in b)
    if t is Pow:
        if not sets:  # an even power with no sub-certificate
            _need(g.n % 2 == 0 and g.n != 0, "odd-power")
            return frozenset({1, 0})
        b = sets[0] - {0} if g.n < 0 else sets[0]
        return frozenset(1 if g.n == 0 else x ** abs(g.n) for x in b)
    a, b = sets  # Add
    for sign in (1, -1):
        if a <= {sign, 0} and b <= {sign, 0}:
            strict = a == {sign} or b == {sign}
            return frozenset({sign}) if strict else frozenset({sign, 0})
    raise _Reject("mixed-sum")


def _node(key, cert):
    """E82: one sub-certificate per child, each at the key's own domain."""
    _fields(cert, "parts")
    g, allowed = _node_target(key)
    kids, parts = _node_children(g), cert["parts"]
    _need(type(parts) is tuple, "malformed")
    _need(len(parts) == len(kids) or (type(g) is Pow and parts == ()),
          "malformed")
    for part in parts:
        _need(type(part) is tuple and len(part) == 2 and part[0] in SIGN_SETS,
              "bad-relation")
    signs = _node_signs(g, [SIGN_SETS[r] for r, _ in parts])
    _need(signs <= allowed, "parity")
    return "sign node", _factors_hold(key.dom, tuple(
        (k, r, c) for k, (r, c) in zip(kids, parts)))


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
             "sign product": _product, "sign node": _node,
             "cite": _cite, "norm_num": _norm_num}


# ---------------------------------------------------------------- regularity (E60-E62)
#
# p1_expected REG_CHECK_RULE, one function per paragraph, each a seam that
# REG_PLANTED_BUGS names (ARCHITECTURE.md §7). A certificate is
# {'method': 'reg', 'tree': NODE}, NODE = {'rule': name, 'args': (NODE, ...),
# 'side': ((prop, cert), ...)}. The checker walks the key's term and the
# certificate together, dispatches on the TERM's head, rebuilds every side
# proposition from the term and k (a builtin's from domains.NATURAL_DOMAINS
# and domains.C1_EXTRA, the one table the formers read), and decides each
# side at the Reg's whole domain by this module's own dispatcher. Sound per
# rule, in E59's reading (REG_SOUNDNESS): if the children are C^k on D and
# the sides hold on D, the node is C^k on D.

_REG_ARITY = {"const": 0, "var": 0, "neg": 1, "add": 2, "mul": 2, "div": 2,
              "pow": 1, "pow_neg": 1, "rpow": 2}


def _reg_class_ok(k):
    """k is an int from 0 to domains.REG_MAX_CLASS (E100); for k >= 1 the
    sides are C^1's. C^omega is not built. A seam (ARCHITECTURE.md §7)."""
    return type(k) is int and 0 <= k <= domains.REG_MAX_CLASS


def _reg_fields(x, names):
    """x is a dict with exactly the fields `names`: one the checker does not
    know rejects. A seam (ARCHITECTURE.md §7)."""
    return type(x) is dict and set(x) == set(names)


def _reg_rule(t, node):
    """The rule the term's head determines, or None (Integral, Deriv, Call,
    MVar and anything else): const for Num and Const, var for Var, neg,
    add, mul, div, pow (n >= 0), pow_neg (n < 0), rpow, and a builtin's own
    name for App. Never read from the certificate (`node` is unused here).
    A seam (ARCHITECTURE.md §7)."""
    k = type(t)
    if k is Num or k is Const:
        return "const"
    if k is Var:
        return "var"
    if k is Pow:
        return "pow" if t.n >= 0 else "pow_neg"
    if k is App and t.fn in BUILTINS:
        return t.fn
    return {Neg: "neg", Add: "add", Mul: "mul", Div: "div", RPow: "rpow"}.get(k)


def _reg_kids(t, rule):
    """The term's children the rule consumes, in GRAMMAR.md §7's order."""
    if rule in ("const", "var"):
        return ()
    if rule == "neg":
        return (t.a,)
    if rule in ("add", "mul", "div"):
        return (t.a, t.b)
    if rule in ("pow", "pow_neg"):
        return (t.base,)
    if rule == "rpow":
        return (t.base, t.exp)
    return (t.arg,)


def _interior(props):
    """C^1's sides from a natural-domain row: its interior (domains). A
    seam (ARCHITECTURE.md §7)."""
    return domains.interior(props)


def _reg_sides(t, rule, k):
    """The node's side propositions, rebuilt from the term and k
    (REG_RULES): div b # 0, pow_neg a # 0, rpow a > 0, a builtin's
    natural-domain row at k = 0 and its interior plus C1_EXTRA at every
    k >= 1 (E100), nothing else. A seam (ARCHITECTURE.md §7)."""
    if rule == "div":
        return (NonZero(t.b),)
    if rule == "pow_neg":
        return (NonZero(t.base),)
    if rule == "rpow":
        return (Rel(">", t.base, ZERO),)
    if rule in BUILTINS:
        row = domains.NATURAL_DOMAINS.get(rule)
        props = row(t.arg) if row else ()
        if k == 0:
            return tuple(props)
        extra = domains.C1_EXTRA.get(rule)
        return tuple(_interior(props)) + (tuple(extra(t.arg)) if extra else ())
    return ()


def _reg_side_count_ok(given, rebuilt):
    """Exactly one pair per rebuilt side. A seam (ARCHITECTURE.md §7)."""
    return len(given) == len(rebuilt)


def _reg_side_prop(rebuilt, given):
    """The proposition to decide: the rebuilt one, which the certificate's
    must equal as a tree, else 'wrong-side'. A seam (ARCHITECTURE.md §7)."""
    _need(given == rebuilt, "wrong-side")
    return rebuilt


def _reg_side_holds(prop, cert, dom):
    """One side, keyed with_domain(prop, dom) (E5) at the Reg's whole
    domain, decided by this module's dispatcher, exact values first, as a
    child is; its cites, or 'child-rejected/<reason>'. A seam
    (ARCHITECTURE.md §7)."""
    tag, why = verdict(with_domain(prop, dom), cert)
    if tag is None:
        raise _Reject("child-rejected/" + why)
    return tag[1]


def _reg_children(t, rule, node, k, dom, cites):
    """'args' has exactly the rule's number of children, else 'arity', and
    each is checked, recursively, against the term's own child. A seam
    (ARCHITECTURE.md §7)."""
    kids = _reg_kids(t, rule)
    _need(len(node["args"]) == len(kids), "arity")
    for kid, sub in zip(kids, node["args"]):
        _reg_node(kid, sub, k, dom, cites)


def _reg_node(t, node, k, dom, cites):
    _need(_reg_fields(node, ("rule", "args", "side"))
          and type(node["args"]) is tuple and type(node["side"]) is tuple
          and all(type(p) is tuple and len(p) == 2 for p in node["side"]),
          "malformed")
    rule = _reg_rule(t, node)
    _need(rule is not None, "no-rule")
    _need(node["rule"] == rule, "wrong-rule")
    own, kids = [], []
    try:
        _reg_children(t, rule, node, k, dom, kids)
        rebuilt = _reg_sides(t, rule, k)
    except AttributeError:  # a rule forced onto a term it does not fit
        raise _Reject("malformed") from None
    _need(_reg_side_count_ok(node["side"], rebuilt), "side-count")
    for want, (prop, cert) in zip(rebuilt, node["side"]):
        own += list(_reg_side_holds(_reg_side_prop(want, prop), cert, dom))
    cites += own + kids  # a node's own sides before its children's


def _reg(key, cert):
    """§6.9's closure rules as a checked derivation (E60, REG_CHECK_RULE):
    ('reg', cites), cites the side certificates' in pre-order first use."""
    _need(_reg_class_ok(key.k), "class-not-built")
    _need(_reg_fields(cert, ("method", "tree")) and cert["method"] == "reg",
          "malformed")
    cites = []
    _reg_node(key.e, cert["tree"], key.k, key.dom, cites)
    return "reg", _dedup(cites)


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


def _rebuild(x, fn):
    """x rebuilt children first, as terms._map rebuilds it, with fn applied
    to every node after its children (a tuple field's items one by one, the
    tuple itself never). Iterative, so a key of any depth is walked without
    exhausting the stack."""
    todo, done = [(x, False)], []
    while todo:
        node, ready = todo.pop()
        fields = _node_fields(node)
        if not ready:
            todo.append((node, True))
            kids = [k for _, v in fields for k in (v if isinstance(v, tuple) else (v,))]
            todo.extend((k, False) for k in reversed(kids))
            continue
        count = sum(len(v) if isinstance(v, tuple) else 1 for _, v in fields)
        rebuilt = done[len(done) - count:] if count else []
        del done[len(done) - count:]
        new, i = {}, 0
        for n, v in fields:  # the children, in the order they were pushed
            width = len(v) if isinstance(v, tuple) else 1
            new[n] = tuple(rebuilt[i:i + width]) if isinstance(v, tuple) else rebuilt[i]
            i += width
        done.append(fn(replace(node, **new) if new else node))
    return done[0]


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
        for name, st in values:
            if _matches(st.lhs, x):
                used.append(name)
                return st.rhs
        return x

    while True:
        new = _rebuild(key, rewrite)
        if new == key:
            break
        key = new
    if type(key) in (Rel, NonZero):
        key = with_domain(_prop(key), key.dom)
    return key, _dedup(used)
