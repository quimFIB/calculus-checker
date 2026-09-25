"""Terms as TeX for KaTeX (app/UI.md §1), and a reader for exactly that TeX.

Untrusted: it draws. A wrong renderer is worse than none (API.md), so the
printer is checked by a round trip, `read(tex(t)) == t`, rather than by eye:
`read` turns the TeX this module emits back into GRAMMAR.md text and hands
it to the trusted parser. Parentheses follow `terms.show`'s precedence
(its _LEVEL table), except that \\frac, \\sqrt and |...| group by
themselves and so need none.
"""

import re

from session import KERNEL  # noqa: F401  (puts kernel/ on the path)
from terms import (Add, App, Call, Const, Deriv, Div, Integral, Interval,
                   Judgement, MVar, Mul, Neg, NegInf, NonZero, Num, PosInf,
                   Pow, Reg, Rel, RPow, Term, Var, _d13_free, parse_goal,
                   parse_judgement, parse_term)

GREEK = ("alpha beta gamma delta epsilon zeta eta theta iota kappa lambda mu "
         "nu xi rho sigma tau upsilon phi chi psi omega").split()
FNS = {"sin": r"\sin", "cos": r"\cos", "tan": r"\tan", "exp": r"\exp",
       "ln": r"\ln", "asin": r"\arcsin", "acos": r"\arccos",
       "atan": r"\arctan", "sinh": r"\sinh", "cosh": r"\cosh",
       "tanh": r"\tanh", "asinh": r"\operatorname{arsinh}",
       "acosh": r"\operatorname{arcosh}", "atanh": r"\operatorname{artanh}"}
RELS = {"==": "=", "<=": r"\le", "<": "<", ">=": r"\ge", ">": ">"}

# show's levels; Div is 6 here, since \frac groups itself
_LEVEL = {Integral: 0, Add: 1, Mul: 2, Neg: 3, App: 4, Deriv: 4,
          Pow: 5, RPow: 5}


def _level(t):
    if type(t) is App and t.fn in ("sqrt", "abs"):
        return 6
    return _LEVEL.get(type(t), 6)


def _name(v):
    """x, x1, v_0, theta, theta_1: the base (a letter or a Greek word),
    its digits inline, its _suffixes as one subscript."""
    m = re.fullmatch(r"(%s|[A-Za-z])([0-9]*)((?:_[A-Za-z0-9]+)*)"
                     % "|".join(GREEK), v)
    if m is None:
        return r"\mathit{%s}" % v.replace("_", r"\_")
    base, digits, suffix = m.groups()
    out = ("\\" + base + " " if base in GREEK else base) + digits
    if suffix:
        out += "_{" + suffix[1:].replace("_", r"\_") + "}"
    return out


def _paren(s):
    return r"\left(" + s + r"\right)"


def _t(t, need=0, left=True):
    if (_level(t) < need or type(t) is Neg and not left) and not (
            type(t) is Div):
        return _paren(_t(t))
    k = type(t)
    if k is Num:
        return str(t.n)
    if k is Var:
        return _name(t.name)
    if k is Const:
        return r"\pi" if t.name == "pi" else r"\mathrm{e}"
    if k is MVar:
        return "?" + t.name
    if k is Add:
        if type(t.b) is Neg:
            return _t(t.a, 1, left) + " - " + _t(t.b.a, 2, False)
        return _t(t.a, 1, left) + " + " + _t(t.b, 2, False)
    if k is Mul:
        return _t(t.a, 2, left) + r" \cdot " + _t(t.b, 4, False)
    if k is Div:
        return r"\frac{" + _t(t.a) + "}{" + _t(t.b) + "}"
    if k is Neg:
        return "-" + _t(t.a, 4, False)
    if k in (Pow, RPow):
        base = (_paren(_t(t.base)) if type(t.base) in (Div, App)
                else _t(t.base, 6, False))
        exp = str(t.n) if k is Pow else _t(t.exp)
        return base + "^{" + exp + "}"
    if k is App:
        if t.fn == "sqrt":
            return r"\sqrt{" + _t(t.arg) + "}"
        if t.fn == "abs":
            return r"\left|" + _t(t.arg) + r"\right|"
        head = FNS[t.fn]
        if type(t.arg) in (Num, Var, Const):
            return head + " " + _t(t.arg)
        return head + _paren(_t(t.arg))
    if k is Deriv:
        return (r"\frac{\mathrm{d}}{\mathrm{d}{" + _name(t.var) + "}}"
                + _paren(_t(t.body)))
    if k is Call:
        return (r"\operatorname{" + t.fn + "}"
                + _paren(", ".join(_t(a) for a in t.args)))
    if k is Integral:
        return (r"\int_{" + _end(t.lo) + "}^{" + _end(t.hi) + "} {"
                + _t(t.body) + r"} \,\mathrm{d}{" + _name(t.var) + "}")
    raise TypeError(f"not a term: {t!r}")


def _end(e):
    if isinstance(e, PosInf):
        return r"\infty"
    if isinstance(e, NegInf):
        return r"-\infty"
    return _t(e, 1)


def _interval(iv, named):
    s = (("[" if iv.lo_closed else "(") + _end(iv.lo) + ", " + _end(iv.hi)
         + ("]" if iv.hi_closed else ")"))
    return _name(iv.var) + r" \in " + s if named else s


def _judgement(j, top=True):
    sides = (j.lhs, j.rhs) if type(j) is Rel else (j.e,)
    text = [_t(s, 0 if top else 1) for s in sides]
    if type(j) is Rel:
        head = f"{text[0]} {RELS[j.op]} {text[1]}"
    elif type(j) is NonZero:
        head = text[0] + r" \neq 0"
    else:
        k = r"\omega" if j.k == "omega" else str(j.k)
        head = text[0] + r" \in C^{" + k + "}"
    free = _d13_free(sides, j.dom)
    items = r",\; ".join(
        _interval(i, free != {i.var}) if isinstance(i, Interval)
        else _judgement(i, top=False) for i in j.dom)
    if type(j) is Reg:
        return head + _paren(items or r"\text{true}")
    return head + (r" \quad\text{for}\; " + items if items else "")


def tex(x):
    """A Term, Judgement or goal (a tuple of judgements) as TeX."""
    if isinstance(x, Term):
        return _t(x)
    if isinstance(x, Judgement):
        return _judgement(x)
    if isinstance(x, tuple):
        return r" \;\wedge\; ".join(_judgement(j) for j in x)
    raise TypeError(f"cannot print {x!r} as TeX")


# ---------------------------------------------------------------- reading

_TOKEN = re.compile(r"\\[A-Za-z]+|\\[,;|_]|[A-Za-z0-9]+|\S")
_BACK = {v: k for k, v in FNS.items() if not v.startswith(r"\operatorname")}
_BACK_OP = {"arsinh": "asinh", "arcosh": "acosh", "artanh": "atanh"}
_WORDS = {r"\cdot": " * ", r"\pi": "pi", r"\infty": "oo", r"\le": " <= ",
          r"\ge": " >= ", r"\in": " in ", r"\wedge": " /\\ ",
          r"\quad": "", r"\,": " ", r"\;": " ", r"\omega": "omega"}


class _Reader:
    def __init__(self, s):
        self.toks = _TOKEN.findall(s)
        self.i = 0

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def take(self, want=None):
        tok = self.peek()
        if tok is None or want is not None and tok != want:
            raise ValueError(f"TeX: expected {want!r}, found {tok!r}")
        self.i += 1
        return tok

    def group(self):
        self.take("{")
        out = self.seq("}")
        self.take("}")
        return out

    def raw_group(self):
        """A {...} group's tokens joined, for \\mathit, \\text and names."""
        self.take("{")
        depth, out = 0, []
        while not (self.peek() == "}" and depth == 0):
            tok = self.take()
            depth += {"{": 1, "}": -1}.get(tok, 0)
            out.append(tok)
        self.take("}")
        return "".join(out)

    def seq(self, stop=None):
        out = []
        while self.peek() is not None and self.peek() != stop:
            if stop is None and self.peek() == "}":
                raise ValueError("TeX: unbalanced }")
            out.append(self.one())
        return "".join(out)

    def one(self):
        tok = self.take()
        if tok == r"\frac":
            if self.toks[self.i:self.i + 4] == ["{", r"\mathrm", "{", "d"]:
                self.raw_group()
                self.take("{")
                self.take(r"\mathrm")
                self.raw_group()
                v = self.group()
                self.take("}")
                return f"D[{v}]" + self.one()
            a = self.group()
            b = self.group()
            return f"(({a})/({b}))"
        if tok == r"\sqrt":
            return f"sqrt({self.group()})"
        if tok == r"\left":
            open_ = self.take()
            inner = self.seq(r"\right")
            self.take(r"\right")
            close = self.take()
            if open_ == "|" and close == "|":
                return f"abs({inner})"
            if open_ == "(" and close == ")":
                return f"({inner})"
            raise ValueError(f"TeX: \\left{open_} ... \\right{close}")
        if tok == "^":
            return f"^({self.group()})"
        if tok == "_":
            return "_" + self.raw_group().replace("\\_", "_")
        if tok == r"\int":
            self.take("_")
            lo = self.group()
            self.take("^")
            hi = self.group()
            body = self.group()
            self.take(r"\,")
            self.take(r"\mathrm")
            self.raw_group()
            v = self.group()
            return f"Int[{v} = {_wrap(lo)} .. {_wrap(hi)}] ({body})"
        if tok == r"\mathrm":
            g = self.raw_group()
            if g != "e":
                raise ValueError(f"TeX: \\mathrm{{{g}}}")
            return "e_const"
        if tok == r"\mathit":
            return self.raw_group().replace("\\_", "_")
        if tok == r"\operatorname":
            g = self.raw_group()
            return _BACK_OP.get(g, g) + " "
        if tok == r"\text":
            g = self.raw_group()
            return {"for": " @ ", "true": "true"}[g]
        if tok == r"\neq":
            self.take("0")
            return " # 0"
        if tok in _BACK:
            return _BACK[tok] + " "
        if tok in _WORDS:
            return _WORDS[tok]
        if tok[0] == "\\" and tok[1:] in GREEK:
            return tok[1:]
        if tok == "=":
            return " == "
        if tok == "C" and self.peek() == "^":
            self.take("^")
            return "C^" + self.group().strip()
        if tok in ("+", "-", "<", ">", ",", "[", "]", "(", ")", "?"):
            return {"+": " + ", "-": " -", "<": " < ", ">": " > ",
                    ",": ", "}.get(tok, tok)
        if re.fullmatch(r"[A-Za-z0-9]+", tok):
            return tok
        raise ValueError(f"TeX: unexpected {tok!r}")


def _wrap(end):
    return end.strip() if end.strip() in ("oo", "-oo") else f"({end})"


def ascii_of(s):
    """The GRAMMAR.md text for TeX that `tex` printed."""
    r = _Reader(s)
    out = r.seq()
    return re.sub(r"\s+", " ", out).strip()


def read(s, kind="term", sig=None):
    """Parse TeX that `tex` printed: a term, a judgement or a goal."""
    text = ascii_of(s)
    return {"term": parse_term, "judgement": parse_judgement,
            "goal": parse_goal}[kind](text, sig)
