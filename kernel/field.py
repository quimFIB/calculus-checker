"""`ring`, `field` and `norm_num` (DESIGN.md §6.2), promoted from the spike.

Trusted (§15.2 item 4): the three reflective procedures. `field`'s divisor
obligations and its reduction modulo facts are the behaviour that soundness
rests on.

`ring` and `field` decide lhs ≐ rhs the way spike/ring/field.py does. They
normalise lhs − rhs and ask whether the numerator is the zero polynomial.
Everything that is not a ring or field operation is an **opaque atom**, and
two atoms are one atom when their heads agree and their arguments normalise
to the same form. That is congruence, and nothing more.

  ring   equality in ℚ[atoms]. A divisor whose normal form is a nonzero
         constant is a coefficient. Any other divisor d gives an atom inv(d),
         keyed by d's normal form (p1_expected E3). ring cancels nothing and
         charges nothing.

  field  equality in the fraction field. It returns every divisor in its
         input: the d of `e / d` and of `d ^ n` with n < 0, including inside
         atom arguments (§6.2 rev 7). The equation holds wherever all of
         them are nonzero. It reduces the numerator modulo `facts` before
         the zero test.

**What changed from the spike, and why (WHAT.md Scope).**
- There is no `Result` and no `holds` flag. A check either returns `Checked`,
  whose `divisors` the caller must emit, or raises `NotEqual`. So "it holds"
  cannot be read without also receiving what it owes.
- Obligations are structural. `Checked.divisors` holds each divisor as a
  Term, first-seen order, deduplicated by `==`, not a string. The kernel
  attaches domains, E5 and norm_num. This module knows no domains. A
  literal divisor is returned like any other, and the kernel's norm_num
  discharges it (E7), where the spike marked it discharged itself.
- Facts are equations the kernel took from verified handles. This module
  never sees a handle. The kernel emits each fact's hypotheses (source
  `fact_hyp`), so the result inherits them. A fact is part of the input,
  so its own divisors are returned with the rest: they are what makes
  `reduce`'s Q nonzero.
- Residual formatting moved to residual.py. `NotEqual` carries the raw
  normal form (`Residual`), and the atom names and `_Normaliser.residual`
  are gone.
- Terms are terms.py's dataclasses, not the spike's tuples. `MVar` and the
  infinities never reach here: the kernel refuses them first, and meeting
  one is a TypeError, a kernel bug and not a refusal.
- **`Deriv` and `Integral` are not atoms** (p1_expected E26 (b)). The spike
  keyed them by their tree, so ring cancelled them like any atom and proved
  (Int[x = 0 .. oo] 1) - (Int[x = 0 .. oo] 1) == 0, whose left side is
  undefined. An atom's identity a = b holds only where every atom is
  defined, and neither node has a definedness condition the kernel can
  state until regularity and `diverges` exist. So the normaliser refuses
  'Int-or-D-not-normalisable' at the first one it meets (`_Normaliser.tree`),
  atom arguments included. Every entry point goes through the normaliser
  (ring, field, fact reduction, ring_equal, ring_is_zero, ring_polys), and
  it visits every node of a side before it returns, so no verdict, divisor
  list or zero test is produced for a side holding one. `norm_num` refuses
  the same nodes in a judgement's proposition or its domain (E7).
  **Since regularity (p1_expected E64, E66 (1))** a statable Integral and
  every Deriv node is an opaque atom again, keyed by its tree exactly: its
  definedness is now owed where it enters (the kernel's Int and D formers),
  so the identity holds wherever the atom denotes. Only an unstatable
  Integral (an infinite limit, or a limit holding an Int or D node, whose
  convergence no rule states yet, E65) is still refused. `norm_num`'s
  refusal is unchanged (E66 (2)).

The `_Normaliser` (atoms, factors, add/mul/pow/invert, facts, reduce) is the
spike's, ported to the new node classes. Its soundness argument for `reduce`
stays with it, word for word.

**The representation** (unchanged from the spike). A normal form is a
numerator polynomial over a multiset of denominator *factors*. A factor is
the polynomial of some divisor, scaled to leading coefficient 1, and
interned: two divisors that normalise to the same polynomial share a factor,
so a sum over a common denominator stays over that denominator instead of
squaring it. Monomial divisors are split into one factor per atom. No
polynomial gcd is ever computed; nothing needs one to decide equality,
because N/F = 0 exactly when N = 0.
"""

import math
import operator
from dataclasses import dataclass
from fractions import Fraction

import poly as P
from terms import (Add, App, Call, Const, Deriv, Div, Integral, Mul, Neg,
                   NonZero, Num, Pow, Refused, Rel, RPow, Var, show, statable,
                   trees)

TREE_CODE = "Int-or-D-not-normalisable"  # p1_expected E26 (b)

# The literal powers ring, field and norm_num expand, bounded so that no
# input makes them compute without end (x := t^1000000000 at t = 3) or
# build a number no message can print. A power b^n is refused
# 'power-too-large' when |n| exceeds POWER_BOUND, when its value's bit size
# (n times the largest coefficient's) would exceed BITS_BOUND, or when the
# expansion of a sum would have more than TERMS_BOUND monomials. A refusal
# withholds a result, never makes one.
POWER_CODE = "power-too-large"
POWER_BOUND = 10 ** 4
BITS_BOUND = 2 ** 13
TERMS_BOUND = 10 ** 5


def _power_ok(poly, n):
    """poly^n stays within the bounds above (poly a poly.py polynomial)."""
    n = abs(n)
    if n > POWER_BOUND:
        return False
    bits = max((max(c.numerator.bit_length(), c.denominator.bit_length())
                for c in poly.values()), default=0)
    if bits * n > BITS_BOUND:
        return False
    k = len(poly)
    return k <= 1 or math.comb(n + k - 1, k - 1) <= TERMS_BOUND


def _too_large(t):
    return Refused(POWER_CODE, f"a literal power with exponent {t.n} is beyond "
                   f"the bounds ring and norm_num expand (|n| <= {POWER_BOUND}, "
                   f"{BITS_BOUND} bits, {TERMS_BOUND} monomials)")


class NotEqual(Exception):
    """lhs − rhs does not normalise to zero. `residual` is its normal form,
    after fact reduction, for residual.residual_term to render."""

    def __init__(self, residual):
        super().__init__("the equation does not normalise to zero")
        self.residual = residual


@dataclass(frozen=True)
class Checked:
    """A successful check. Equality holds wherever every divisor is nonzero.
    `divisors` is () for ring."""
    divisors: tuple


@dataclass(frozen=True)
class Residual:
    """A normal form lhs − rhs = num / Π den.

    num   a poly.py polynomial over atom indices;
    den   ((poly, exponent), ...): the denominator factors, followed by each
          fact's Q^top multiplier where Q is not constant (spike `reduce`);
    atoms atom index -> the first Term seen for that atom. An inv atom's
          term is Div(Num 1, d).
    """
    num: dict
    den: tuple
    atoms: tuple


class _Frac:
    __slots__ = ("num", "den")

    def __init__(self, num, den):
        self.num = num  # polynomial
        self.den = den  # {factor id: exponent}


class _Normaliser:
    def __init__(self, is_field):
        self.is_field = is_field
        self.atom_index = {}
        self.atom_terms = []  # the first term seen for each atom
        self.factor_index = {}
        self.factor_polys = []
        self.divisors = {}  # Term -> None: an ordered set

    # -- atoms, factors, divisors

    def atom(self, key, term):
        i = self.atom_index.get(key)
        if i is None:
            i = len(self.atom_terms)
            self.atom_index[key] = i
            self.atom_terms.append(term)
        return _Frac(P.atom(i), {})

    def key(self, t):
        return self.frac_key(self.norm(t))

    @staticmethod
    def frac_key(f):
        return (P.frozen(f.num), tuple(sorted(f.den.items())))

    def factor(self, p):
        k = P.frozen(p)
        fid = self.factor_index.get(k)
        if fid is None:
            fid = len(self.factor_polys)
            self.factor_index[k] = fid
            self.factor_polys.append(p)
        return fid

    def expand(self, den):
        out = P.const(1)
        for fid, e in den.items():
            out = P.mul(out, P.power(self.factor_polys[fid], e))
        return out

    def divisor(self, d):
        """Record the divisor term d. field returns every one; ring none."""
        if self.is_field:
            self.divisors.setdefault(d, None)

    # -- arithmetic on normal forms

    def add(self, a, b):
        if not a.num:
            return b
        if not b.num:
            return a
        if a.den == b.den:
            return _Frac(P.add(a.num, b.num), dict(a.den))
        lcm = dict(a.den)
        for fid, e in b.den.items():
            if e > lcm.get(fid, 0):
                lcm[fid] = e
        na = P.mul(a.num, self.expand(
            {f: e - a.den.get(f, 0) for f, e in lcm.items() if e > a.den.get(f, 0)}))
        nb = P.mul(b.num, self.expand(
            {f: e - b.den.get(f, 0) for f, e in lcm.items() if e > b.den.get(f, 0)}))
        return _Frac(P.add(na, nb), lcm)

    def mul(self, a, b):
        if not a.num or not b.num:
            return _Frac({}, {})
        den = dict(a.den)
        for fid, e in b.den.items():
            den[fid] = den.get(fid, 0) + e
        return _Frac(P.mul(a.num, b.num), den)

    def pow(self, a, n):
        if n == 0:
            return _Frac(P.const(1), {})
        return _Frac(P.power(a.num, n), {f: e * n for f, e in a.den.items()})

    def invert(self, a, divisor):
        """1 / a, where a is the normal form of the term `divisor`.

        E25: a numerator of zero is refused, in ring's normal form or in
        field's, before the divisor is recorded or anything else is done.
        """
        if not a.num:
            raise Refused("divisor-normalises-to-zero",
                          f"the divisor {show(divisor)} normalises to zero")
        self.divisor(divisor)
        if P.is_const(a.num) and not a.den:
            return _Frac(P.const(1 / P.const_value(a.num)), {})
        if not self.is_field:
            return self.atom(("inv", self.frac_key(a)), Div(Num(1), divisor))
        c, rest = P.content_normal(a.num)
        g = P.monomial_gcd(rest)
        den = {}
        if g:
            rest = {P.mono_div(m, g): v for m, v in rest.items()}
            for i, e in g:
                fid = self.factor(P.atom(i))
                den[fid] = den.get(fid, 0) + e
        if not P.is_const(rest):
            fid = self.factor(rest)
            den[fid] = den.get(fid, 0) + 1
        return _Frac(P.scale(self.expand(a.den), 1 / c), den)

    # -- terms to normal forms

    def norm(self, t):
        k = type(t)
        if k is Num:
            return _Frac(P.const(t.n), {})
        if k is Var or k is Const:
            return self.atom(t, t)
        if k is Add:
            return self.add(self.norm(t.a), self.norm(t.b))
        if k is Neg:
            a = self.norm(t.a)
            return _Frac(P.neg(a.num), a.den)
        if k is Mul:
            return self.mul(self.norm(t.a), self.norm(t.b))
        if k is Div:
            return self.mul(self.norm(t.a), self.invert(self.norm(t.b), t.b))
        if k is Pow:
            base, n = self.norm(t.base), t.n
            if not (_power_ok(base.num, n) and all(
                    _power_ok(self.factor_polys[f], n * e) for f, e in base.den.items())):
                raise _too_large(t)
            if n < 0:
                base, n = self.invert(base, t.base), -n
            return self.pow(base, n)
        if k is RPow:
            return self.atom(("rpow", self.key(t.base), self.key(t.exp)), t)
        if k is App:
            return self.atom(("app", t.fn, self.key(t.arg)), t)
        if k is Call:
            return self.atom(("call", t.fn, tuple(map(self.key, t.args))), t)
        if k is Deriv or k is Integral:
            return self.tree(t)
        raise TypeError(f"ring and field cannot read {t!r}")

    def tree(self, t):
        """E66 (1): a statable Integral and every Deriv node is an opaque
        atom, keyed by its tree exactly (no alpha equivalence, no
        normalisation under the binder: incomplete, never unsound), since
        its definedness is owed where it entered (E64's formers). An
        unstatable Integral (an infinite limit, or a limit holding an Int
        or D node) is not an atom, so the side holding it is refused, as
        E26 (b) had it.

        A seam (kernel/ARCHITECTURE.md §7): norm calls it by this name for
        each such node, and the definedness mutations ring_reads_Int_as_atom
        and field_reads_Int_as_atom (and the planted bug
        improper_Int_as_atom) replace it, in a child process, with one that
        returns an atom for an unstatable Int too. Keep the name and
        signature."""
        if statable(t):
            return self.atom(("tree", t), t)
        raise Refused(TREE_CODE, f"{show(t)} has no definedness condition the "
                      "kernel can state, so ring and field do not read it as "
                      "an atom (E26 (b))")

    # -- facts

    def facts(self, eqs):
        """Normalise fact equations into reducers (atom, k, P, Q): a^k = P/Q."""
        parsed = []
        for lhs, rhs in eqs:
            fl, fr = self.norm(lhs), self.norm(rhs)
            ok = not fl.den and len(fl.num) == 1
            if ok:
                (m, c), = fl.num.items()
                ok = c == 1 and len(m) == 1
            if not ok:
                raise Refused("field-fact-shape",
                              f"fact {show(lhs)} == {show(rhs)}: the left "
                              "side must normalise to a power of one atom")
            (i, k), = m
            parsed.append((i, k, fr, lhs, rhs))
        fact_atoms = {i for i, *_ in parsed}
        if len(fact_atoms) != len(parsed):
            raise Refused("field-fact-shape", "two facts about the same atom")
        reducers = []
        for i, k, fr, lhs, rhs in parsed:
            q = self.expand(fr.den)
            for p in (fr.num, q):
                if any(j in fact_atoms for m in p for j, _ in m):
                    raise Refused("field-fact-shape",
                                  f"fact {show(lhs)} == {show(rhs)}: the "
                                  "right side mentions a fact atom")
            reducers.append((i, k, fr.num, q))
        return reducers

    @staticmethod
    def reduce(n, i, k, p_num, q):
        """n with every a^k replaced by P/Q, times Q^qmax to stay polynomial.

        Writing n = Σ_j n_j·a^(jk), with no a-power ≥ k inside any n_j, gives
        n·Q^J = Σ_j n_j·P^j·Q^(J−j) where J is the largest j. Q ≠ 0 follows
        from the fact's own obligations, so n = 0 exactly when the result is.
        """
        buckets = {}
        for m, c in n.items():
            e = dict(m).get(i, 0)
            j, r = divmod(e, k)
            m2 = tuple((a, r if a == i else x) for a, x in m if a != i or r)
            b = buckets.setdefault(j, {})
            b[m2] = b.get(m2, 0) + c
        top = max(buckets, default=0)
        if top == 0:
            return n, 0
        out = {}
        for j, part in buckets.items():
            part = {m: c for m, c in part.items() if c}
            out = P.add(out, P.mul(part, P.mul(P.power(p_num, j),
                                               P.power(q, top - j))))
        return out, top


def _decide(is_field, lhs, rhs, facts=()):
    nz = _Normaliser(is_field)
    lf, rf = nz.norm(lhs), nz.norm(rhs)
    diff = nz.add(lf, _Frac(P.neg(rf.num), rf.den))
    n, extra = diff.num, []
    for i, k, p_num, q in nz.facts(facts):
        n, top = nz.reduce(n, i, k, p_num, q)
        extra.append((q, top))
    if n:
        den = tuple((nz.factor_polys[f], e) for f, e in diff.den.items() if e)
        den += tuple((q, e) for q, e in extra if e and not P.is_const(q))
        raise NotEqual(Residual(n, den, tuple(nz.atom_terms)))
    return Checked(tuple(nz.divisors))


def ring(lhs, rhs):
    """Decide lhs ≐ rhs in ℚ[atoms]. Returns Checked(()) or raises NotEqual.

    Raises Refused 'divisor-normalises-to-zero' when some divisor's ring
    normal form is the zero polynomial (E25; the spike's `invert`), and
    'Int-or-D-not-normalisable' when a side holds an unstatable Integral
    (E26 (b), E66 (1)), whichever the walk meets first.
    """
    return _decide(False, lhs, rhs)


def field(lhs, rhs, facts=()):
    """Decide lhs ≐ rhs in the fraction field, modulo `facts`.

    `facts` is a sequence of (a_k, r) Term pairs. Each must normalise to a
    power of one atom on the left, with a right side mentioning no fact's
    atom (§6.2 facts), and no two facts may be about the same atom.
    Otherwise it raises Refused 'field-fact-shape'. Each divisor is tested as
    it is met, before the zero test. A numerator of zero in its field normal
    form raises Refused 'divisor-normalises-to-zero' (E25), so `x/x - 1` is
    refused here although ring sees it as nonzero. A side or fact holding an
    unstatable Integral raises Refused 'Int-or-D-not-normalisable' (E26 (b),
    E66 (1)). Returns Checked(divisors), or raises NotEqual.
    """
    return _decide(True, lhs, rhs, facts)


def ring_equal(a, b):
    """True when a and b have the same ring normal form, both normalised by
    one normaliser so that atom indices agree. This is REWRITE_RULE steps
    3–4's matcher test, and a predicate, not a proof. Raises Refused like
    `ring`.

    A seam (kernel/ARCHITECTURE.md §7): kernel's rewrite calls it by this
    name, and the suite's BACKSTOPS case rewrite_closing_check_goal
    replaces it in a child process. Keep the name and signature."""
    nz = _Normaliser(False)
    return nz.norm(a).num == nz.norm(b).num


def ring_is_zero(t):
    """True when t's ring normal form is the zero polynomial. E25's
    charge-time test for a divisor d (E6, route_div). A zero divisor inside t
    raises Refused 'divisor-normalises-to-zero'. That is the refusal the
    caller would give anyway, so it may let it propagate."""
    return not _Normaliser(False).norm(t).num


def ring_polys(terms):
    """Ring-normalise several terms with one shared atom table.

    Returns (polys, atoms), where polys[i] is the normal form of terms[i]
    and atoms maps each index to its Term. This is for the untrusted tagger,
    which reads monomials as Fourier–Motzkin variables. Raises Refused like
    `ring`.
    """
    nz = _Normaliser(False)
    polys = [nz.norm(t).num for t in terms]
    return polys, tuple(nz.atom_terms)


# ---------------------------------------------------------------- norm_num

_OPS = {"==": operator.eq, "<=": operator.le, "<": operator.lt,
        ">=": operator.ge, ">": operator.gt}


def _value(t):
    k = type(t)
    if k is Num:
        return Fraction(t.n)
    if k is Neg:
        a = _value(t.a)
        return None if a is None else -a
    if k is Add or k is Mul or k is Div:
        a, b = _value(t.a), _value(t.b)
        if a is None or b is None:
            return None
        return a + b if k is Add else a * b if k is Mul else a / b
    if k is Pow:
        b = _value(t.base)
        if b is not None and not _power_ok({(): b} if b else {}, t.n):
            raise _too_large(t)
        return None if b is None else b ** t.n
    return None


def rational_value(t):
    """t's value when t is built from Num, Neg, Add, Mul, Div and Pow alone,
    i.e. a rational literal expression. Otherwise None, and None also when
    some divisor, or a negatively powered base, evaluates to 0."""
    try:
        return _value(t)
    except ZeroDivisionError:  # a / 0, or 0 ** n with n < 0
        return None
    except Refused:  # a power beyond the bounds: not read as a literal here;
        return None  # ring and norm_num refuse it (POWER_CODE)


def norm_num_tree(node, in_domain):
    """E7 with E26 (b): an obligation holding an Integral or Deriv node,
    in its proposition or (in_domain) in its domain, is refused, never
    decided and never admitted. An obligation about such a node's value
    presupposes that it exists, which nothing can state yet. Returns
    nothing, ever.

    A seam (kernel/ARCHITECTURE.md §7): only norm_num calls it, by this
    name, for each such node, and the mutations norm_num_admits_Int,
    norm_num_admits_D and norm_num_ignores_domain replace it in a child
    process. install's gate on the goal's hypotheses is hypothesis_tree, a
    separate seam, so each can be weakened alone. Keep the name and
    signature."""
    raise Refused(TREE_CODE, f"an obligation about {show(node)} presupposes "
                  "that it exists, which nothing can state yet (E26 (b))")


def hypothesis_tree(node):
    """E26 (b) at install: a goal hypothesis holding an Integral or Deriv
    node is refused, whether or not any obligation's domain carries it,
    because a hypothesis about such a node's value presupposes that it
    exists. Returns nothing, ever. It raises what norm_num_tree raises but
    is a separate seam (kernel/ARCHITECTURE.md §7): kernel.install calls it
    by this name, and a mutation that weakens it leaves E7's own check in
    norm_num intact. Keep the name and signature."""
    raise Refused(TREE_CODE, f"a hypothesis about {show(node)} presupposes "
                  "that it exists, which nothing can state yet (E26 (b))")


def norm_num(j):
    """Decide a judgement over rational literals exactly (§6.2; E7).

    A Rel or NonZero holding an Integral or Deriv node anywhere, its domain
    included, raises Refused 'Int-or-D-not-normalisable' through
    norm_num_tree (E26 (b)), whether or not it is literal or closed. For a
    Rel or NonZero with dom == () whose every term has a rational_value,
    return True or False. Return None for anything else, Reg included (the
    kernel never asks about a Reg: E7 does not run on one). The kernel calls
    this on every emission. True is DISCHARGED and False refuses the step
    'obligation-refuted'.
    """
    if type(j) not in (Rel, NonZero):
        return None
    sides = (j.lhs, j.rhs) if type(j) is Rel else (j.e,)
    for part, in_domain in ((sides, False), (j.dom, True)):
        for node in trees(part):
            norm_num_tree(node, in_domain)
    if j.dom != ():
        return None
    try:  # a literal power beyond the bounds refuses (POWER_CODE)
        vals = [_value(s) for s in sides]
    except ZeroDivisionError:
        vals = [rational_value(s) for s in sides]
    if any(v is None for v in vals):
        return None
    if type(j) is NonZero:
        return vals[0] != 0
    return _OPS[j.op](*vals)
