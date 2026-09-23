"""`ring` and `field`: the stage 0c spike (DESIGN.md §6.2, §17).

Both decide an equation lhs ≐ rhs by normalising lhs − rhs and asking whether
the numerator is the zero polynomial. Everything that is not a ring or field
operation — sin u, sqrt u, a real power, a declared f(u) — is an **opaque
atom**, and two atoms are the same atom when their heads agree and their
arguments normalise to the same form (congruence, never anything more).

  ring   equality in ℚ[atoms]. Division by a nonzero literal is a coefficient;
         division by anything else is *itself* an opaque atom, so
         m * (1/m) ≐ 1 is not provable — it is not a ring fact (§6.5).

  field  equality in the fraction field. Every divisor it meets — the d of
         `e / d`, or of `d ^ n` with n < 0, including inside atom arguments —
         becomes an obligation `d # 0`, and the equation is shown to hold
         only wherever every obligation does. A divisor that is a nonzero
         literal is recorded as discharged by norm_num; one that normalises to
         zero is refused outright.

         `facts` are proven equations `a ^ k ≐ r`, a power of one atom on the
         left and a right-hand side free of every fact atom — the shape of
         §6.8's `sqrt_sq_val`, `(sqrt 3)^2 ≐ 3`. The numerator is reduced
         modulo them before the zero test. In the kernel these would be
         theorem handles (§15.3); the spike takes the equations on trust.

**What `holds` means.** `Result.holds` is true when lhs = rhs at every point
where all of `obligations` hold. It is *not* the kernel's `Proved`: that is
`holds` with no open obligation, after §5.3's discharge has run, which is not
part of this spike. A caller that reads `holds` alone has made the one mistake
§6.2 says this rule exists to prevent.

**The representation.** A normal form is a numerator polynomial over a
multiset of denominator *factors*. A factor is the polynomial of some divisor,
scaled to leading coefficient 1, and interned: two divisors that normalise to
the same polynomial share a factor, so a sum over a common denominator stays
over that denominator instead of squaring it. Monomial divisors are split
into one factor per atom. No polynomial gcd is ever computed; nothing needs
one to decide equality, because N/F = 0 exactly when N = 0.
"""

from dataclasses import dataclass

import poly as P
from terms import ONE, parse, show


class Refused(Exception):
    """The equation is ill-formed or outside the rule's fragment."""


@dataclass(frozen=True)
class Obligation:
    divisor: str
    discharged_by: str | None = None

    def __str__(self):
        how = f"by {self.discharged_by}" if self.discharged_by else "open"
        return f"{self.divisor} # 0    [{how}]"


@dataclass(frozen=True)
class Result:
    rule: str
    holds: bool
    obligations: tuple
    residual: str | None
    numerator_terms: int  # the largest numerator built, a proxy for work
    denominator_factors: int

    @property
    def open_obligations(self):
        return tuple(o for o in self.obligations if o.discharged_by is None)

    def __str__(self):
        head = f"{self.rule}: " + ("holds" if self.holds else "does not hold")
        lines = [head]
        lines += [f"  obl  {o}" for o in self.obligations]
        if self.residual is not None:
            lines.append(f"  residual  {self.residual}")
        return "\n".join(lines)


class _Frac:
    __slots__ = ("num", "den")

    def __init__(self, num, den):
        self.num = num  # polynomial
        self.den = den  # {factor id: exponent}


class _Normaliser:
    def __init__(self, rule):
        self.is_field = rule == "field"
        self.atom_index = {}
        self.atom_names = []
        self.atom_terms = []  # the first term seen for each atom
        self.factor_index = {}
        self.factor_polys = []
        self.obligations = {}

    # -- atoms, factors, obligations

    def atom(self, key, term):
        i = self.atom_index.get(key)
        if i is None:
            i = len(self.atom_names)
            self.atom_index[key] = i
            s = show(term)
            simple = term[0] in ("var", "const", "app")
            self.atom_names.append(s if simple else f"({s})")
            self.atom_terms.append(term)
        return _Frac(P.atom(i), {})

    def key(self, t):
        f = self.norm(t)
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

    def oblige(self, divisor, discharged_by=None):
        s = show(divisor)
        if s not in self.obligations:
            self.obligations[s] = Obligation(s, discharged_by)

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
        if not a.num:
            raise Refused(f"the divisor {show(divisor)} is identically zero")
        if P.is_const(a.num) and not a.den:
            self.oblige(divisor, "norm_num")
            return _Frac(P.const(1 / P.const_value(a.num)), {})
        if not self.is_field:
            key = (P.frozen(a.num), tuple(sorted(a.den.items())))
            return self.atom(("inv", key), ("div", ONE, divisor))
        self.oblige(divisor)
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
        k = t[0]
        if k == "num":
            return _Frac(P.const(t[1]), {})
        if k in ("var", "const"):
            return self.atom(t, t)
        if k == "add":
            return self.add(self.norm(t[1]), self.norm(t[2]))
        if k == "neg":
            a = self.norm(t[1])
            return _Frac(P.neg(a.num), a.den)
        if k == "mul":
            return self.mul(self.norm(t[1]), self.norm(t[2]))
        if k == "div":
            return self.mul(self.norm(t[1]), self.invert(self.norm(t[2]), t[2]))
        if k == "pow":
            base, n = self.norm(t[1]), t[2]
            if n < 0:
                base, n = self.invert(base, t[1]), -n
            return self.pow(base, n)
        if k == "rpow":
            return self.atom(("rpow", self.key(t[1]), self.key(t[2])), t)
        if k == "app":
            return self.atom(("app", t[1], tuple(self.key(a) for a in t[2])), t)
        raise Refused(f"{k} is not a term ring or field can read")

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
                raise Refused(f"fact {show(lhs)} ≐ {show(rhs)}: the left side "
                              "must normalise to a power of a single atom")
            (i, k), = m
            parsed.append((i, k, fr, lhs, rhs))
        fact_atoms = {i for i, *_ in parsed}
        if len(fact_atoms) != len(parsed):
            raise Refused("two facts about the same atom")
        reducers = []
        for i, k, fr, lhs, rhs in parsed:
            q = self.expand(fr.den)
            for p in (fr.num, q):
                if any(j in fact_atoms for m in p for j, _ in m):
                    raise Refused(f"fact {show(lhs)} ≐ {show(rhs)}: the right "
                                  "side mentions a fact atom")
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

    # -- display

    def residual(self, n, den, extra):
        den = dict(den)
        for fid in sorted(den):
            while den[fid] and n:
                q = P.divide_exact(n, self.factor_polys[fid])
                if q is None:
                    break
                n = q
                den[fid] -= 1
        name = self.atom_names.__getitem__
        parts = [(self.factor_polys[f], e) for f, e in den.items() if e]
        parts += [(q, e) for q, e in extra if e and not P.is_const(q)]
        num_s = P.to_str(n, name)
        if not parts:
            return num_s
        den_s = " * ".join(f"({P.to_str(p, name)})" + (f"^{e}" if e > 1 else "")
                           for p, e in parts)
        return f"({num_s}) / {den_s}"


def _term(t):
    return parse(t) if isinstance(t, str) else t


def _decide(rule, lhs, rhs, facts=()):
    nz = _Normaliser(rule)
    lhs, rhs = _term(lhs), _term(rhs)
    lf, rf = nz.norm(lhs), nz.norm(rhs)
    diff = nz.add(lf, _Frac(P.neg(rf.num), rf.den))
    reducers = nz.facts([(_term(a), _term(b)) for a, b in facts])
    n, extra = diff.num, []
    for i, k, p_num, q in reducers:
        n, top = nz.reduce(n, i, k, p_num, q)
        extra.append((q, top))
    holds = not n
    return Result(
        rule=rule,
        holds=holds,
        obligations=tuple(nz.obligations.values()),
        residual=None if holds else nz.residual(n, diff.den, extra),
        numerator_terms=max(len(lf.num), len(rf.num), len(diff.num)),
        denominator_factors=sum(diff.den.values()),
    )


def ring(lhs, rhs):
    """Decide lhs ≐ rhs in ℚ[atoms]. Terms or strings in §5.1 syntax."""
    return _decide("ring", lhs, rhs)


def field(lhs, rhs, facts=()):
    """Decide lhs ≐ rhs in the fraction field, modulo the returned obligations.

    `facts` is a sequence of (lhs, rhs) equations of the shape a^k ≐ r.
    """
    return _decide("field", lhs, rhs, facts)
