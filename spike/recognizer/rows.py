"""The recognizer table (DESIGN.md §8.5), as data plus one matcher per row.

Two versions, kept apart on purpose:

  V1  exactly the rows §8.5 states, plus the antiderivative card it
      describes ("the twenty forms from the inside cover") cut down to the
      forms the corpus touches. This is what the design says; the corpus
      score of V1 is the measurement.
  V2  V1 plus the rows the V1 misses asked for. V2 was written *after*
      looking at the corpus, so its score on that corpus is not evidence —
      `corpus.HELD_OUT` is.

A row names a technique; it never proves one applies. The kernel is what
refuses a bad move (§7), so a row can be as heuristic as it likes, and the
cost column is advice, not an obligation.

Order matters: the first row that matches is the one rung 2 names. The card
comes first, because recognising that nothing needs doing is the first
recognition (§8.5, rung 0).
"""

from dataclasses import dataclass
from typing import Callable

from shapes import (TRANSCENDENTAL, completed_constant_sign, depends, deriv,
                    is_constant_ratio, is_linear, is_zero, poly_in, quadratic,
                    rational_in, show, show_poly, sign, split_constant,
                    sqrt_subterms, summands)
from terms import ONE, app, free_vars, replace, subterms


@dataclass(frozen=True)
class Row:
    name: str
    family: str       # what a corpus label is compared against
    category: str     # rung 1: the kind of move, without the move
    technique: str    # rung 2: the row
    cost: str         # what the move will ask for in return
    match: Callable   # (term, x) -> params dict, or None
    detail: Callable  # params -> rung 3 text


# ------------------------------------------------------------ the card

def _card_form(s, x):
    """Which standard form a single summand is, if any."""
    cs, g = split_constant(s, x)
    if not g:
        return "constant"
    whole = g[0] if len(g) == 1 else None
    q = poly_in(s, x)
    if q is not None:
        return "polynomial: the power rule"
    if whole is None:
        return None
    k = whole[0]
    if k == "app" and whole[1] in TRANSCENDENTAL and is_linear(whole[2][0], x):
        return f"{whole[1]} of a linear argument"
    if k == "rpow" and whole[1] == ("var", x) and not depends(whole[2], x):
        return "x^p: the power rule"
    if k == "pow" and whole[1] == ("var", x) and whole[2] <= -2:
        return "x^n: the power rule"
    if k == "div" and whole[1] == ONE:
        d = whole[2]
        q = quadratic(d, x)
        if q is not None:
            lead, rest = sign(q.coeff(2)), completed_constant_sign(q)
            if lead * rest < 0:
                return "1/(a² − x²): artanh"
            return "1/(x² + a²): arctan"
        if d[0] == "app" and d[1] == "sqrt":
            q = quadratic(d[2][0], x)
            if q is not None and not q.coeff(1) and sign(q.coeff(2)) < 0 \
                    and sign(q.coeff(0)) > 0:
                return "1/√(a² − x²): arcsin"
    return None


def m_card(t, x):
    forms = [_card_form(s, x) for s in summands(t)]
    if all(forms) and any(f != "constant" for f in forms):
        return {"forms": sorted(set(f for f in forms if f != "constant"))}
    return None


def m_log_linear(t, x):
    _, g = split_constant(t, x)
    if len(g) == 1 and g[0][0] == "div" and g[0][1] == ONE and is_linear(g[0][2], x):
        return {"f": g[0][2]}
    return None


# ------------------------------------------------------------ §8.5's rows

def m_log_derivative(t, x):
    """f′(x)/f(x), up to a constant factor."""
    _, g = split_constant(t, x)
    divisors = [f for f in g if f[0] == "div" and f[1] == ONE]
    if len(divisors) != 1:
        return None
    f = divisors[0][2]
    rest = [h for h in g if h is not divisors[0]]
    num = ONE
    for h in rest:
        num = ("mul", num, h)
    try:
        df = deriv(f, x)
    except NotImplementedError:
        return None
    if is_zero(df):
        return None
    if is_constant_ratio(num, df, x):
        return {"f": f}
    return None


def m_parts(t, x):
    _, g = split_constant(t, x)
    trans = [f for f in g if f[0] == "app" and f[1] in TRANSCENDENTAL
             and is_linear(f[2][0], x)]
    if len(trans) != 1:
        return None
    rest = [f for f in g if f is not trans[0]]
    if not rest:
        return None
    p = rest[0]
    for f in rest[1:]:
        p = ("mul", p, f)
    q = poly_in(p, x)
    if q is None or q.degree < 1:
        return None
    return {"P": p, "g": trans[0], "degree": q.degree, "x": x}


def m_partial_fractions(t, x):
    r = rational_in(t, x)
    if r is None:
        return None
    num, den = r
    if den.degree < 2:
        return None
    return {"den": show_poly(den, x), "degree": den.degree}


def m_weierstrass(t, x):
    s, c = ("var", "__S"), ("var", "__C")
    u = replace(replace(t, app("sin", ("var", x)), s), app("cos", ("var", x)), c)
    if u == t or depends(u, x):
        return None
    for sub in subterms(u):
        if sub[0] in ("app", "rpow") and free_vars(sub) & {"__S", "__C"}:
            return None
    return {"theta": x}


def _sqrt_quadratics(t, x):
    for s in sqrt_subterms(t, x):
        q = quadratic(s[2][0], x)
        if q is not None:
            yield s, q


def m_trig_sub(t, x):
    for s, q in _sqrt_quadratics(t, x):
        if sign(q.coeff(2)) < 0:
            return {"root": s, "shift": bool(q.coeff(1))}
    return None


def m_sinh_sub(t, x):
    for s, q in _sqrt_quadratics(t, x):
        if sign(q.coeff(2)) > 0 and completed_constant_sign(q) > 0:
            return {"root": s, "shift": bool(q.coeff(1))}
    return None


def m_root_sub(t, x):
    for outer in subterms(t):
        if outer[0] != "app" or outer[1] == "sqrt":
            continue
        for s in sqrt_subterms(outer, x):
            if quadratic(s[2][0], x) is None:
                return {"u": s[2][0], "inside": outer[1]}
    return None


# ------------------------------------------------------------ V2's rows

def m_log_tan(t, x):
    """tan u and tanh u are f′/f in disguise: −(cos u)′/cos u, (cosh u)′/cosh u."""
    _, g = split_constant(t, x)
    if len(g) == 1 and g[0][0] == "app" and g[0][1] in ("tan", "tanh") \
            and is_linear(g[0][2][0], x):
        inner = "cos" if g[0][1] == "tan" else "cosh"
        return {"f": app(inner, g[0][2][0])}
    return None


def m_split_numerator(t, x):
    """(linear)/(irreducible quadratic): c·f′/f plus an arctan."""
    r = rational_in(t, x)
    if r is None:
        return None
    num, den = r
    if num.degree != 1 or den.degree != 2:
        return None
    if sign(den.coeff(2)) * completed_constant_sign(den) < 0:
        return None  # it factors over the reals: partial fractions instead
    return {"den": show_poly(den, x)}


def m_cosh_sub(t, x):
    for s, q in _sqrt_quadratics(t, x):
        if sign(q.coeff(2)) > 0 and completed_constant_sign(q) < 0:
            return {"root": s, "shift": bool(q.coeff(1))}
    return None


def m_param_diff(t, x):
    """c / D^k with k ≥ 2, where 1/D is itself recognised: differentiate a
    parameter of ∫ 1/D instead of attacking the power."""
    _, g = split_constant(t, x)
    if len(g) != 1:
        return None
    h = g[0]
    if h[0] == "div" and h[1] == ONE and h[2][0] == "pow" and h[2][2] >= 2:
        base, k = h[2][1], h[2][2]
    elif h[0] == "pow" and h[2] <= -2:
        base, k = h[1], -h[2]
    else:
        return None
    if not free_vars(base) - {x}:
        return None  # no parameter to differentiate by
    inner = ("div", ONE, base)
    for row in V1:
        if row.name != "card" and row.match(inner, x):
            return {"D": base, "k": k, "via": row.name}
    return None


def m_beta(t, x):
    """(A − B·x^n)^(±1/2) with a symbolic n: u = x^n turns it into a Beta."""
    for s in sqrt_subterms(t, x):
        parts = summands(s[2][0])
        const = [p for p in parts if not depends(p, x)]
        powers = [p for p in parts if depends(p, x)]
        if len(const) == 1 and len(powers) == 1:
            _, g = split_constant(powers[0], x)
            if len(g) == 1 and g[0][0] == "rpow" and g[0][1] == ("var", x) \
                    and not depends(g[0][2], x):
                return {"n": g[0][2]}
    return None


# ------------------------------------------------------------ the tables

def _forms(p):
    return "; ".join(p["forms"])


CARD = Row("card", "standard", "It is already a standard form.",
           "Read it off the antiderivative card.", "—",
           m_card, lambda p: f"Standard: {_forms(p)}.")
LOG_LINEAR = Row("log-linear", "log", "It is a logarithm.",
                 "1/(linear) integrates to a logarithm.", "f # 0",
                 m_log_linear, lambda p: f"∫ = c·ln|{show(p['f'])}|.")
LOG_DERIVATIVE = Row("f′/f", "log", "It is a logarithm.",
                     "f′(x)/f(x) → ln f, with f > 0.", "f > 0",
                     m_log_derivative,
                     lambda p: f"The numerator is a constant times the derivative of "
                               f"f = {show(p['f'])}; ∫ = c·ln f.")
PARTS = Row("parts", "parts",
            "A product where one factor gets simpler each time it is differentiated.",
            "P(x)·e^{ax}, P(x)·sin ax → parts, reducing deg P each time.", "—",
            m_parts,
            lambda p: f"u = {show(p['P'])} (degree {p['degree']}), "
                      f"dv = {show(p['g'])} d{p['x']}; repeat {p['degree']} time(s).")
PARTIAL_FRACTIONS = Row("partial fractions", "partial fractions",
                        "Algebra first: rewrite the fraction.",
                        "Rational function → factor, then partial fractions.",
                        "each factor # 0",
                        m_partial_fractions,
                        lambda p: f"Factor the denominator {p['den']} "
                                  f"(degree {p['degree']}) over the reals, then split.")
WEIERSTRASS = Row("Weierstrass", "Weierstrass", "A substitution.",
                  "R(sin θ, cos θ) → t = tan(θ/2).", "cos(θ/2) # 0 on the range",
                  m_weierstrass,
                  lambda p: f"t = tan({p['theta']}/2): sin = 2t/(1+t²), "
                            f"cos = (1−t²)/(1+t²), d{p['theta']} = 2 dt/(1+t²).")
TRIG_SUB = Row("√(a² − x²)", "trig substitution", "A substitution.",
               "√(a² − x²) → x = a sin θ.", "closing needs pyth",
               m_trig_sub,
               lambda p: ("Complete the square in " if p["shift"] else "In ")
               + f"{show(p['root'])}, then x = a·sin θ.")
SINH_SUB = Row("√(x² + a²)", "hyperbolic substitution", "A substitution.",
               "√(x² + a²) → x = a sinh u.", "inverse: asinh",
               m_sinh_sub,
               lambda p: ("Complete the square in " if p["shift"] else "In ")
               + f"{show(p['root'])}, then x = a·sinh u.")
ROOT_SUB = Row("√u inside f", "root substitution", "A substitution.",
               "√(u) inside f(·) → u = t², kill the root.", "u ≥ 0",
               m_root_sub,
               lambda p: f"Put {show(p['u'])} = t² inside {p['inside']}(…).")

V1 = [CARD, LOG_LINEAR, LOG_DERIVATIVE, PARTS, PARTIAL_FRACTIONS,
      WEIERSTRASS, TRIG_SUB, SINH_SUB, ROOT_SUB]

LOG_TAN = Row("tan / tanh", "log", "It is a logarithm.",
              "tan u → −ln cos u; tanh u → ln cosh u (f′/f after tan_def).",
              "cos u # 0", m_log_tan,
              lambda p: f"It is f′/f with f = {show(p['f'])}.")
SPLIT = Row("linear / quadratic", "split numerator",
            "Algebra first: rewrite the fraction.",
            "(linear)/(irreducible quadratic) → c·f′/f plus a constant over f.",
            "—", m_split_numerator,
            lambda p: f"Write the numerator as c·(d/dx of {p['den']}) + d: "
                      f"a logarithm plus an arctangent.")
COSH_SUB = Row("√(x² − a²)", "hyperbolic substitution", "A substitution.",
               "√(x² − a²) → x = a cosh u.", "x ≥ a; inverse: acosh",
               m_cosh_sub,
               lambda p: ("Complete the square in " if p["shift"] else "In ")
               + f"{show(p['root'])}, then x = a·cosh u.")
PARAM_DIFF = Row("1/Dᵏ", "parameter differentiation",
                 "Relate it to an easier integral.",
                 "c/Dᵏ with k ≥ 2 → differentiate ∫ 1/D by a parameter in D.",
                 "leibniz: continuity on a compact set",
                 m_param_diff,
                 lambda p: f"∫ 1/({show(p['D'])}) is a '{p['via']}' integral; put a "
                           f"parameter in it and differentiate {p['k'] - 1} time(s).")
BETA = Row("(A − Bxⁿ)^½", "Beta substitution", "A special function.",
           "√(A − B·xⁿ), n symbolic → scale to the turning point, then u = xⁿ: "
           "a Beta function.", "convergence at the endpoint",
           m_beta, lambda p: f"Scale x so A − B·xⁿ becomes 1 − σⁿ, then u = σ^{show(p['n'])}.")

V2 = [CARD, LOG_LINEAR, LOG_DERIVATIVE, LOG_TAN, PARAM_DIFF, SPLIT, PARTS,
      PARTIAL_FRACTIONS, WEIERSTRASS, TRIG_SUB, SINH_SUB, COSH_SUB, ROOT_SUB, BETA]


def recognize(t, x, table):
    """Every row that matches, in table order, with its parameters."""
    out = []
    for row in table:
        try:
            p = row.match(t, x)
        except (NotImplementedError, RecursionError):
            p = None
        if p is not None:
            out.append((row, p))
    return out


def ladder(t, x, table):
    """Rungs 1–3 for the first matching row (§8.5, 'The ladder, implemented')."""
    hits = recognize(t, x, table)
    if not hits:
        return None
    row, p = hits[0]
    return {"rung 1": row.category, "rung 2": row.technique,
            "rung 3": row.detail(p), "costs": row.cost}

