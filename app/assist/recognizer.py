"""The recognizer table (DESIGN.md §8.5; app/assist/RECOGNIZER.md).

Rows as data, one matcher each, in RECOGNIZER.md's order: the first row
that matches is the one rung 2 names. A row names a technique; it never
proves one applies. The learner still types the move and the kernel
checks it, so a row can be as heuristic as it likes and the cost column
is advice, not an obligation.

Untrusted (tier 2). Every matcher reads the integrand through shapes.py,
on the kernel's `field` normal form.
"""

from dataclasses import dataclass
from typing import Callable

from assist import shapes as S
from assist.shapes import (ONE, LINEAR_FNS, App, Div, Mul, Pow, RPow, Var,
                           depends, deriv, free_of, fv, is_linear, poly_in,
                           replace_term, shape, sqrt_quadratic, sqrt_subterms,
                           subterms, summands)
from terms import show

NO_ROW = frozenset(("guess and verify", "reduction formula", "other"))


@dataclass(frozen=True)
class Row:
    name: str
    family: str       # what a label is compared against
    category: str     # rung 1: the kind of move, without the move
    technique: str    # rung 2: the row
    cost: str         # what the move will ask for in return
    match: Callable   # (term, x) -> params dict, or None
    detail: Callable  # params -> rung 3 text


def _app(a, fns):
    return type(a) is App and a.fn in fns


# ---------------------------------------------------------------- 1 identity

def m_identity(t, x):
    """A trig polynomial of degree ≥ 2 in sin/cos of one linear angle."""
    s = shape(t, x)
    if s is None or s.den_x:
        return None
    used = {i for m in s.num for i, _ in m if i in s.dep}
    if not used or s.xi in used:
        return None
    if not all(_app(s.atom(i), ("sin", "cos")) for i in used):
        return None
    angles = [s.atom(i).arg for i in used]
    try:
        keys = {s.nz.key(a) for a in angles}
    except Exception:
        return None
    if len(keys) != 1 or not is_linear(angles[0], x):
        return None
    degree = max(sum(e for i, e in m if i in s.dep) for m in s.num)
    if degree < 2:
        return None
    return {"angle": angles[0], "degree": degree}


def _trig_linear(a, x):
    return _app(a, ("sin", "cos")) and is_linear(a.arg, x)


def m_identity_product(t, x):
    """Revision 2's product clause: a numerator monomial with sin or cos
    factors of linear arguments, any angles, of total degree >= 2, times
    anything; no sin or cos in the denominator; row 15's pattern left to
    it."""
    s = shape(t, x)
    if s is None:
        return None
    for f in s.den_x:
        if any(_app(s.atom(i), ("sin", "cos"))
               for m in s.factor(f) for i, _ in m):
            return None
    best = None
    for m in s.num:
        trig = [(s.atom(i), e) for i, e in m
                if i in s.dep and _trig_linear(s.atom(i), x)]
        degree = sum(e for _, e in trig)
        if degree >= 2 and (best is None or degree > best[1]):
            best = (trig, degree)
    if best is None or m_orthogonality(t, x) is not None:
        return None
    return {"factors": [a for a, _ in best[0]], "degree": best[1]}


def m_identity_any(t, x):
    """Row 1: the one-angle trig polynomial (version 1), else the product
    clause (revision 2)."""
    p = m_identity(t, x)
    if p is not None:
        return p
    return m_identity_product(t, x)


# ---------------------------------------------------------------- 2 the card

def _quadratic_form(q):
    """Which card form 1/q is, for a quadratic q, or None."""
    lead, b = q.sign(2), q.coeff(1)
    if not b and lead * q.sign(0) < 0:
        return "1/(a² − x²): artanh"
    lc = lead * q.completed_sign()
    if lc > 0 or (lc == 0 and not b):
        return "1/(x² + a²): arctan"
    return None


def card_form(u, x):
    """Which standard form one summand is, if any."""
    s = shape(u, x)
    if s is None:
        return None
    if not s.num:
        return "constant"
    dx = s.den_x
    if not dx and s.x_only():
        return "polynomial: the power rule" if s.num_in_x().degree > 0 \
            else "constant"
    sep = s.separable()
    if sep is None:
        return None
    if not dx:
        if len(sep) != 1:
            return None
        (i, e), = sep.items()
        a = s.atom(i)
        if e == 1 and _app(a, LINEAR_FNS) and is_linear(a.arg, x):
            return f"{a.fn} of a linear argument"
        if e == 1 and _app(a, ("sqrt",)) and is_linear(a.arg, x):
            return "√(linear): the power rule"  # revision 2
        if e == 1 and type(a) is RPow and a.base == Var(x) \
                and not depends(a.exp, x):
            return "x^p: the power rule"
        return None
    if sep or len(dx) != 1:
        return None
    (f, k), = dx.items()
    ft = s.factor_term(f)
    q = poly_in(ft, x)
    if q is not None and q.degree == 1 and k >= 2:
        return "c/(linear)^k: the power rule"
    if q is not None and q.degree == 2 and k == 1:
        return _quadratic_form(q)
    if _app(ft, ("sqrt",)) and k == 1 and is_linear(ft.arg, x):
        return "1/√(linear): the power rule"  # revision 2
    if _app(ft, ("sqrt",)) and k == 1:
        r = sqrt_quadratic(ft, x)
        if r is not None and not r.coeff(1) and r.sign(2) < 0 \
                and r.sign(0) > 0:
            return "1/√(a² − x²): arcsin"
    return None


def m_card(t, x):
    forms = [card_form(u, x) for u in summands(t)]
    if all(forms):
        return {"forms": sorted(set(f for f in forms if f != "constant"))
                or ["constant"]}
    return None


# ---------------------------------------------------------------- 3 log

def m_log(t, x):
    s = shape(t, x)
    if s is None:
        return None
    dx = s.den_x
    if not dx:
        sep = s.separable()
        if sep and len(sep) == 1:
            (i, e), = sep.items()
            a = s.atom(i)
            if e == 1 and _app(a, ("tan", "tanh")) and is_linear(a.arg, x):
                inner = App("cos" if a.fn == "tan" else "cosh", a.arg)
                return {"f": inner, "via": a.fn}
        return None
    for f, e in dx.items():
        if e != 1:
            continue
        ft = s.factor_term(f)
        try:
            df = deriv(ft, x)
        except S.Unreadable:
            continue
        if free_of(df, x) and not is_linear(ft, x):
            continue  # f′ constant but f not linear: f′ ≐ 0
        if free_of(Div(Mul(t, ft), df), x):
            return {"f": ft, "via": "linear" if is_linear(ft, x) else "f'/f"}
    return None


# ---------------------------------------------------------------- 4 chain rule

def _candidates(t, x):
    seen = []
    for u in subterms(t):
        for c in ((u.arg,) if type(u) is App else
                  (u.base,) if type(u) in (Pow, RPow) else ()):
            if depends(c, x) and c not in seen:
                seen.append(c)
    return seen


def m_chain(t, x):
    """Some nonlinear u with integrand[u := U]/u′ free of x."""
    U = Var("U_" + "_".join(sorted(fv(t))))
    for u in _candidates(t, x):
        q = poly_in(u, x)
        if q is not None and q.degree <= 1:
            continue
        g = replace_term(t, u, U)
        if g == t:
            continue
        try:
            du = deriv(u, x)
        except S.Unreadable:
            continue
        if free_of(Div(g, du), x):
            return {"u": u}
    return None


# ---------------------------------------------------------------- 5, 6 parts

def _non_x_parts(s):
    """The numerator monomials' x-dependent parts other than x itself."""
    return {tuple((i, e) for i, e in m if i in s.dep and i != s.xi)
            for m in s.num}


def m_parts_cycle(t, x):
    s = shape(t, x)
    if s is None or s.den_x:
        return None
    sep = s.separable()
    if not sep or len(sep) != 2 or set(sep.values()) != {1}:
        return None
    a, b = sorted((s.atom(i) for i in sep), key=lambda a: a.fn != "exp") \
        if all(type(s.atom(i)) is App for i in sep) else (None, None)
    if a is None or a.fn != "exp" or b.fn not in ("sin", "cos"):
        return None
    if not (is_linear(a.arg, x) and is_linear(b.arg, x)):
        return None
    return {"e": a, "g": b}


PARTS_ONCE = ("ln", "atan", "asin")


def m_parts(t, x):
    s = shape(t, x)
    if s is None or s.den_x:
        return None
    parts = _non_x_parts(s)
    if len(parts) != 1:
        return None
    part = parts.pop()
    if len(part) != 1 or part[0][1] != 1:
        return None
    a = s.atom(part[0][0])
    if type(a) is not App or not is_linear(a.arg, x):
        return None
    degree = s.num_in_x().degree if s.xi is not None else 0
    if a.fn in LINEAR_FNS and degree >= 1:
        return {"g": a, "degree": degree, "u": "poly"}
    if a.fn in PARTS_ONCE:
        return {"g": a, "degree": degree, "u": "g"}
    return None


# ---------------------------------------------------------------- 7, 8 fractions

def _rational(t, x):
    s = shape(t, x)
    if s is None or not s.den_x or not s.x_only():
        return None
    return s


def m_split(t, x):
    s = _rational(t, x)
    if s is None or list(s.den_x.values()) != [1]:
        return None
    num, den = s.num_in_x(), s.den_in_x()
    if num.degree != 1 or den.degree != 2:
        return None
    if den.sign(2) * den.completed_sign() < 0:
        return None  # it factors over the reals: partial fractions
    return {"den": den.term(x)}


def m_partial(t, x):
    s = _rational(t, x)
    if s is None:
        return None
    den = s.den_in_x()
    if den.degree < 2:
        return None
    return {"den": den.term(x), "degree": den.degree}


# ---------------------------------------------------------------- 9, 10 roots

def _root_quadratics(t, x):
    for r in sqrt_subterms(t, x):
        q = sqrt_quadratic(r, x)
        if q is not None:
            yield r, q


def _x_divides(t, x):
    """x itself is a factor of t's denominator."""
    s = shape(t, x)
    if s is None:
        return False
    for f in s.den_x:
        q = poly_in(s.factor_term(f), x)
        if q is not None and q.degree == 1 and not q.coeff(0):
            return True
    return False


def m_trig_sub(t, x):
    for r, q in _root_quadratics(t, x):
        if q.sign(2) < 0:
            return {"root": r, "shift": bool(q.coeff(1)), "kind": "sin"}
        if q.sign(2) > 0 and q.completed_sign() < 0 and _x_divides(t, x):
            return {"root": r, "shift": bool(q.coeff(1)), "kind": "sec"}
    return None


def m_hyp_sub(t, x):
    for r, q in _root_quadratics(t, x):
        if q.sign(2) > 0:
            c = q.completed_sign()
            kind = "sinh" if c > 0 else "cosh" if c < 0 else "sinh or cosh"
            return {"root": r, "shift": bool(q.coeff(1)), "kind": kind}
    return None


# ---------------------------------------------------------------- 11 Weierstrass

def m_weierstrass(t, x):
    sv, cv = Var("S_w"), Var("C_w")
    u = replace_term(replace_term(t, App("sin", Var(x)), sv),
                     App("cos", Var(x)), cv)
    if u == t or depends(u, x):
        return None
    for sub in subterms(u):
        if type(sub) in (App, RPow) and fv(sub) & {"S_w", "C_w"}:
            return None
    return {"theta": x}


# ---------------------------------------------------------------- 12 root sub

def m_root_sub(t, x):
    s = shape(t, x)
    for r in sqrt_subterms(t, x):
        if sqrt_quadratic(r, x) is not None:
            continue
        for outer in subterms(t):
            if type(outer) is App and outer.fn != "sqrt" \
                    and r in subterms(outer.arg):
                return {"u": r.arg, "inside": outer.fn}
        if s is not None:
            used = {i for m in s.num for i, _ in m if i in s.dep}
            used |= {i for f in s.den_x for m in s.factor(f) for i, _ in m
                     if i in s.dep}
            if any(s.atom(i) != r for i in used):
                return {"u": r.arg, "inside": None}
    return None


# ---------------------------------------------------------------- 13 parameter

def m_param(t, x):
    s = shape(t, x)
    if s is None or s.separable() != {}:
        return None
    dx = s.den_x
    if len(dx) != 1:
        return None
    (f, k), = dx.items()
    if k < 2:
        return None
    d = s.factor_term(f)
    if not fv(d) - {x}:
        return None  # no parameter to differentiate by
    inner = Div(ONE, d)
    for row in ROWS:
        if row.match is not m_param and row.match(inner, x) is not None:
            return {"D": d, "k": k, "via": row.family}
    return None


# ---------------------------------------------------------------- 14 Beta

def m_beta(t, x):
    for r in sqrt_subterms(t, x):
        s = shape(r.arg, x)
        if s is None or s.den_x:
            continue
        free = [m for m in s.num if not any(i in s.dep for i, _ in m)]
        dep = [m for m in s.num if any(i in s.dep for i, _ in m)]
        if not free or len(dep) != 1:
            continue
        part = [(i, e) for i, e in dep[0] if i in s.dep]
        if len(part) == 1 and part[0][1] == 1:
            a = s.atom(part[0][0])
            if type(a) is RPow and a.base == Var(x) and not depends(a.exp, x):
                return {"n": a.exp}
    return None


# ---------------------------------------------------------------- 15 orthogonality

def m_orthogonality(t, x):
    s = shape(t, x)
    if s is None or s.den_x:
        return None
    sep = s.separable()
    if not sep or s.xi in sep:
        return None
    trig = [(s.atom(i), e) for i, e in sep.items()]
    if sum(e for _, e in trig) != 2 or len(trig) != 2:
        return None
    ks = []
    for a, _ in trig:
        if not _app(a, ("sin", "cos")):
            return None
        q = poly_in(a.arg, x)
        if q is None or q.degree != 1 or q.coeff(0):
            return None
        if S.P.is_const(q.coeff(1)):
            return None  # numeric frequency: an identity, not orthogonality
        ks.append(a)
    return {"f": ks[0], "g": ks[1]}


# ---------------------------------------------------------------- the table

def _shift(p):
    return "Complete the square in " if p["shift"] else "In "


ROWS = [
    Row("identity first", "identity first",
        "Rewrite it with an identity before integrating.",
        "A power or product of sin and cos of one angle: reduce it "
        "(double angle, product to sum) first.",
        "— (rewrite: no side condition)", m_identity_any,
        lambda p: (f"It is degree {p['degree']} in sin and cos of "
                   f"{show(p['angle'])}; rewrite with the double-angle "
                   "entries until each term is linear in sin or cos of a "
                   "multiple of it." if "angle" in p else
                   "The product " + "·".join(show(a) for a in p["factors"])
                   + " has degree " + str(p["degree"]) + " in sin and cos:"
                   " product to sum (or the double angle) makes each term a"
                   " single sin or cos, then integrate term by term.")),
    Row("card", "standard", "It is already a standard form.",
        "Read it off the antiderivative card.", "—", m_card,
        lambda p: "Standard: " + "; ".join(p["forms"]) + "."),
    Row("log", "log", "It is a logarithm.",
        "f′(x)/f(x) integrates to ln|f|.", "f # 0 on the range", m_log,
        lambda p: (f"It is f′/f with f = {show(p['f'])}"
                   + (f" (after writing {p['via']} as sin/cos)"
                      if p["via"] in ("tan", "tanh") else "")
                   + ": the integral is a constant times ln|f|.")),
    Row("parameter differentiation", "parameter differentiation",
        "Relate it to an easier integral.",
        "c/Dᵏ with k ≥ 2 → differentiate ∫ 1/D by a parameter in D.",
        "leibniz: continuity on a compact set", m_param,
        lambda p: f"∫ 1/({show(p['D'])}) is a {p['via']} integral; put a "
                  f"parameter in it and differentiate {p['k'] - 1} time(s)."),
    Row("chain rule", "chain-rule substitution", "A substitution.",
        "The integrand is g(u)·u′ for an inner u: substitute u.",
        "u′ continuous on the range", m_chain,
        lambda p: f"Put u = {show(p['u'])}: the integrand is a function "
                  "of u times du/dx."),
    Row("parts cycle", "parts cycle",
        "A product that comes back to itself under parts.",
        "e^{ax}·sin bx or cos bx: parts twice, then solve for the integral.",
        "—", m_parts_cycle,
        lambda p: f"Integrate by parts twice with u = {show(p['g'])}; the "
                  "original integral reappears, so solve for it."),
    Row("parts", "parts",
        "A product where one factor gets simpler when differentiated.",
        "P(x)·g(x) → parts, differentiating the part that simplifies.",
        "—", m_parts,
        lambda p: (f"u = the polynomial (degree {p['degree']}), dv = "
                   f"{show(p['g'])} dx; repeat {p['degree']} time(s)."
                   if p["u"] == "poly" else
                   f"u = {show(p['g'])}, dv = the rest: its derivative "
                   "is algebraic.")),
    Row("split numerator", "split numerator",
        "Algebra first: rewrite the fraction.",
        "(linear)/(irreducible quadratic) → c·f′/f plus a constant over f.",
        "—", m_split,
        lambda p: f"Write the numerator as c·(d/dx of {show(p['den'])}) + d:"
                  " a logarithm plus an arctangent."),
    Row("partial fractions", "partial fractions",
        "Algebra first: rewrite the fraction.",
        "Rational function → factor the denominator, then partial fractions.",
        "each factor # 0", m_partial,
        lambda p: f"Factor the denominator {show(p['den'])} (degree "
                  f"{p['degree']}) over the reals, then split."),
    Row("trig substitution", "trig substitution", "A substitution.",
        "√(a² − x²) → x = a sin θ; √(x² − a²) over x → x = a sec θ.",
        "closing needs pyth", m_trig_sub,
        lambda p: _shift(p) + f"{show(p['root'])}, then x = a·{p['kind']} θ."),
    Row("hyperbolic substitution", "hyperbolic substitution",
        "A substitution.",
        "√(x² + a²) → x = a sinh u; √(x² − a²) → x = a cosh u.",
        "inverse: asinh or acosh", m_hyp_sub,
        lambda p: _shift(p) + f"{show(p['root'])}, then x = a·{p['kind']} u."),
    Row("Weierstrass", "Weierstrass", "A substitution.",
        "R(sin θ, cos θ) → t = tan(θ/2).", "cos(θ/2) # 0 on the range",
        m_weierstrass,
        lambda p: f"t = tan({p['theta']}/2): sin = 2t/(1+t²), "
                  f"cos = (1−t²)/(1+t²), d{p['theta']} = 2 dt/(1+t²)."),
    Row("root substitution", "root substitution", "A substitution.",
        "√(u) inside something else → u = t², which removes the root.",
        "u ≥ 0", m_root_sub,
        lambda p: f"Put {show(p['u'])} = t²"
                  + (f" inside {p['inside']}(…)." if p["inside"] else ".")),
    Row("Beta substitution", "Beta substitution", "A special function.",
        "√(A − B·xⁿ), n symbolic → scale to the turning point, then u = xⁿ:"
        " a Beta function.", "convergence at the endpoint", m_beta,
        lambda p: f"Scale x so A − B·xⁿ becomes 1 − σⁿ, then u = "
                  f"σ^{show(p['n'])}."),
    Row("orthogonality", "orthogonality", "It is an orthogonality integral.",
        "sin or cos(m x) times sin or cos(n x) → product to sum, then the "
        "cases m = n and m ≠ n.", "m ≠ n and m = n are separate cases",
        m_orthogonality,
        lambda p: f"Write {show(p['f'])}·{show(p['g'])} as a sum with "
                  "product to sum; each term integrates over a period to "
                  "0 unless the frequencies agree."),
]
FAMILIES = [r.family for r in ROWS]


def recognize(t, x):
    """Every row that matches t as a function of x, in table order, with
    its parameters."""
    out = []
    for row in ROWS:
        try:
            p = row.match(t, x)
        except (S.Unreadable, RecursionError, ArithmeticError):
            p = None
        if p is not None:
            out.append((row, p))
    return out


def first(t, x):
    """The first matching (row, params), or None."""
    for row in ROWS:
        try:
            p = row.match(t, x)
        except (S.Unreadable, RecursionError, ArithmeticError):
            p = None
        if p is not None:
            return row, p
    return None


def ladder(t, x):
    """Rungs 1–3 and the cost for the first matching row, or None."""
    hit = first(t, x)
    if hit is None:
        return None
    row, p = hit
    return {"row": row.name, "family": row.family, 1: row.category,
            2: row.technique, 3: row.detail(p), "cost": row.cost}
