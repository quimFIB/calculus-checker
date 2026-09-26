"""Terms laid out in two dimensions as Unicode text (app/GOALS2D.md).

Untrusted: it only draws, for editors that cannot show KaTeX. The
parenthesisation is tex.py's (terms.show's precedence, with fractions and
roots grouping themselves), so a drawing groups exactly as the TeX does.
"""

from session import KERNEL  # noqa: F401  (puts kernel/ on the path)
from terms import (Add, App, Call, Const, Deriv, Div, Integral, Interval,
                   Judgement, MVar, Mul, Neg, NegInf, NonZero, Num, PosInf,
                   Pow, Reg, Rel, RPow, Term, Var, _d13_free)
from tex import _level

GREEK = {"alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ",
         "epsilon": "ε", "zeta": "ζ", "eta": "η", "theta": "θ", "iota": "ι",
         "kappa": "κ", "lambda": "λ", "mu": "μ", "nu": "ν", "xi": "ξ",
         "rho": "ρ", "sigma": "σ", "tau": "τ", "upsilon": "υ", "phi": "φ",
         "chi": "χ", "psi": "ψ", "omega": "ω"}
RELS = {"==": "=", "<=": "≤", "<": "<", ">=": "≥", ">": ">"}
SUP = str.maketrans("0123456789-", "⁰¹²³⁴⁵⁶⁷⁸⁹⁻")


class Box:
    """Rows of equal width; `base` is the row the box sits on."""

    def __init__(self, rows, base=0):
        w = max((len(r) for r in rows), default=0)
        self.rows = [r.ljust(w) for r in rows]
        self.base = base

    @property
    def w(self):
        return len(self.rows[0]) if self.rows else 0

    @property
    def h(self):
        return len(self.rows)


def text(s):
    return Box([s])


def hcat(*boxes):
    up = max(b.base for b in boxes)
    down = max(b.h - b.base for b in boxes)
    rows = [""] * (up + down)
    for b in boxes:
        top = up - b.base
        for i in range(up + down):
            j = i - top
            rows[i] += b.rows[j] if 0 <= j < b.h else " " * b.w
    return Box(rows, up)


def _centre(b, w):
    left = (w - b.w) // 2
    return [" " * left + r + " " * (w - b.w - left) for r in b.rows]


def frac(a, b):
    w = max(a.w, b.w)
    return Box(_centre(a, w) + ["─" * w] + _centre(b, w), a.h)


def paren(b, lo="(", hi=")"):
    if b.h == 1:
        return Box([lo + b.rows[0] + hi], 0)
    tall = {"(": "⎛⎜⎝", ")": "⎞⎟⎠", "│": "│││"}
    def side(c):
        t, m, e = tall[c]
        return [t] + [m] * (b.h - 2) + [e]
    return Box([l + r + e for l, r, e in zip(side(lo), b.rows, side(hi))],
               b.base)


def sqrt(a):
    h, rows = a.h, []
    left = h + 2  # the diagonal, then a space before the radicand
    rows.append(" " * (left - 1) + "_" * (a.w + 1))
    for r in range(1, h + 1):
        col = left - 1 - r
        s = [" "] * left
        s[col] = "╱"
        if r == h:
            s[col - 1] = "╲"
        rows.append("".join(s) + a.rows[r - 1])
    return Box(rows, a.base + 1)


def sup(base, exp):
    """exp raised a row above base's top, to its right."""
    rows = [" " * base.w + r for r in exp.rows]
    rows += [r + " " * exp.w for r in base.rows]
    return Box(rows, base.base + exp.h)


def _name(v):
    head, _, rest = v.partition("_")
    for g, c in GREEK.items():
        if head == g or head.startswith(g) and head[len(g):].isdigit():
            head = c + head[len(g):]
            break
    return head + ("_" + rest if rest else "")


def _t(t, need=0, left=True):
    if (_level(t) < need or type(t) is Neg and not left) and not (
            type(t) is Div):
        return paren(_t(t))
    k = type(t)
    if k is Num:
        return text(str(t.n))
    if k is Var:
        return text(_name(t.name))
    if k is Const:
        return text("π" if t.name == "pi" else "e")
    if k is MVar:
        return text("?" + t.name)
    if k is Add:
        if type(t.b) is Neg:
            return hcat(_t(t.a, 1, left), text(" - "), _t(t.b.a, 2, False))
        return hcat(_t(t.a, 1, left), text(" + "), _t(t.b, 2, False))
    if k is Mul:
        return hcat(_t(t.a, 2, left), text("⋅"), _t(t.b, 4, False))
    if k is Div:
        return frac(_t(t.a), _t(t.b))
    if k is Neg:
        return hcat(text("-"), _t(t.a, 4, False))
    if k in (Pow, RPow):
        base = (paren(_t(t.base)) if type(t.base) in (Div, App)
                else _t(t.base, 6, False))
        if k is Pow:
            s = str(t.n).translate(SUP)
            return Box([r + (s if i == 0 else " " * len(s))
                        for i, r in enumerate(base.rows)], base.base)
        return sup(base, _t(t.exp))
    if k is App:
        if t.fn == "sqrt":
            return sqrt(_t(t.arg))
        if t.fn == "abs":
            return paren(_t(t.arg), "│", "│")
        if type(t.arg) in (Num, Var, Const):
            return hcat(text(t.fn + " "), _t(t.arg))
        return hcat(text(t.fn), paren(_t(t.arg)))
    if k is Deriv:
        return hcat(frac(text("d"), text("d" + _name(t.var))),
                    paren(_t(t.body)))
    if k is Call:
        args = [_t(a) for a in t.args]
        parts = []
        for i, a in enumerate(args):
            parts += [text(", "), a] if i else [a]
        return hcat(text(t.fn), paren(hcat(*parts)))
    if k is Integral:
        return integral(_end(t.lo), _end(t.hi), _t(t.body), _name(t.var))
    raise TypeError(f"not a term: {t!r}")


def integral(lo, hi, body, var):
    s = max(3, body.h + 2)
    sign = ["⌠"] + ["⎮"] * (s - 2) + ["⌡"]
    w = max(lo.w, hi.w, 1)
    rows = [r.ljust(w) for r in hi.rows] + [c.ljust(w) for c in sign] \
        + [r.ljust(w) for r in lo.rows]
    mid = hi.h + s // 2
    col = Box(rows, mid)
    # the body sits centred on the sign's middle row
    return hcat(col, text(" "), body, text(" d" + var))


def _end(e):
    if isinstance(e, PosInf):
        return text("∞")
    if isinstance(e, NegInf):
        return text("-∞")
    return _t(e, 1)


def _interval(iv, named):
    s = hcat(text("[" if iv.lo_closed else "("), _end(iv.lo), text(", "),
             _end(iv.hi), text("]" if iv.hi_closed else ")"))
    return hcat(text(_name(iv.var) + " ∈ "), s) if named else s


def _judgement(j, top=True):
    sides = (j.lhs, j.rhs) if type(j) is Rel else (j.e,)
    b = [_t(s, 0 if top else 1) for s in sides]
    if type(j) is Rel:
        head = hcat(b[0], text(f" {RELS[j.op]} "), b[1])
    elif type(j) is NonZero:
        head = hcat(b[0], text(" ≠ 0"))
    else:
        k = "ω" if j.k == "omega" else str(j.k)
        head = hcat(b[0], text(f" ∈ C^{k}"))
    free = _d13_free(sides, j.dom)
    items = []
    for i in j.dom:
        if items:
            items.append(text(", "))
        items.append(_interval(i, free != {i.var}) if isinstance(i, Interval)
                     else _judgement(i, top=False))
    if type(j) is Reg:
        return hcat(head, paren(hcat(*items) if items else text("true")))
    return hcat(head, text("  for "), *items) if items else head


def layout(x):
    """A Term, Judgement or goal (a tuple of judgements) as a Box."""
    if isinstance(x, Term):
        return _t(x)
    if isinstance(x, Judgement):
        return _judgement(x)
    if isinstance(x, tuple):
        parts = []
        for j in x:
            parts += [text("  ∧  "), _judgement(j)] if parts else \
                [_judgement(j)]
        return hcat(*parts)
    raise TypeError(f"cannot lay out {x!r}")


def pretty(x):
    """layout(x) as text, the rows joined by newlines, trailing blanks
    kept so every row has the same width."""
    return "\n".join(layout(x).rows)
