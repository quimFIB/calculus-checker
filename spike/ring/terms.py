"""Terms of DESIGN.md §5.1 — the part of the grammar `ring` and `field` see.

A term is a tuple whose first element names its former:

    ('num', Fraction)            rational literal
    ('const', 'pi' | 'e_const')  named constant
    ('var', name)                variable
    ('add', a, b)   ('mul', a, b)   ('neg', a)   ('div', a, b)
    ('pow', a, n)                integer power, n an int (negative: field op)
    ('rpow', a, b)               real power a ^ b — opaque to ring and field
    ('app', f, (args...))        sin u, sqrt u, … or a declared f(u, …)

`a - b` is parsed as ('add', a, ('neg', b)); §5.1 has no subtraction former.
Binders (D, Int, Sum, lim) are out of scope for the spike.

The parser is spike-grade: enough to write §11's goals as the document does,
including juxtaposed application (`sin t * (2*t)` is (sin t)·(2t), and
`sin t^2` is (sin t)^2). It is not §15.6's parser.
"""

import re
from fractions import Fraction

FUNCTIONS = {
    "sin", "cos", "tan", "asin", "acos", "atan",
    "exp", "ln", "sqrt", "abs",
    "sinh", "cosh", "tanh", "asinh", "acosh", "atanh",
}
CONSTANTS = {"pi", "e_const"}


def num(q):
    return ("num", Fraction(q))


def var(x):
    return ("var", x)


def app(f, *args):
    return ("app", f, tuple(args))


ZERO = num(0)
ONE = num(1)


# ---------------------------------------------------------------- parsing

_TOKEN = re.compile(r"\s*(?:(\d+(?:\.\d+)?)|([A-Za-z_][A-Za-z0-9_]*)|(.))")


def _tokenize(s):
    out = []
    for m in _TOKEN.finditer(s):
        n, ident, op = m.groups()
        if n is not None:
            out.append(("num", n))
        elif ident is not None:
            out.append(("id", ident))
        elif op is not None and not op.isspace():
            if op not in "+-*/^(),":
                raise SyntaxError(f"unexpected character {op!r} in {s!r}")
            out.append(("op", op))
    out.append(("end", None))
    return out


class _Parser:
    def __init__(self, s):
        self.src = s
        self.toks = _tokenize(s)
        self.i = 0

    def peek(self):
        return self.toks[self.i]

    def take(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def expect(self, op):
        t = self.take()
        if t != ("op", op):
            raise SyntaxError(f"expected {op!r}, got {t[1]!r} in {self.src!r}")

    def at(self, op):
        return self.peek() == ("op", op)

    def expr(self):
        t = self.term()
        while self.at("+") or self.at("-"):
            op = self.take()[1]
            rhs = self.term()
            t = ("add", t, rhs if op == "+" else ("neg", rhs))
        return t

    def term(self):
        t = self.unary()
        while self.at("*") or self.at("/"):
            op = self.take()[1]
            rhs = self.unary()
            t = ("mul" if op == "*" else "div", t, rhs)
        return t

    def unary(self):
        if self.at("-"):
            self.take()
            return ("neg", self.unary())
        return self.power()

    def power(self):
        base = self.application()
        if self.at("^"):
            self.take()
            e = self.unary()  # right-associative, and x^-1 is allowed
            n = _int_literal(e)
            return ("pow", base, n) if n is not None else ("rpow", base, e)
        return base

    def application(self):
        kind, val = self.peek()
        if kind == "id" and val in FUNCTIONS:
            self.take()
            return ("app", val, (self.application(),))
        if kind == "id" and self.toks[self.i + 1] == ("op", "(") \
                and val not in CONSTANTS:
            self.take()
            self.take()
            args = [self.expr()]
            while self.at(","):
                self.take()
                args.append(self.expr())
            self.expect(")")
            return ("app", val, tuple(args))
        return self.primary()

    def primary(self):
        kind, val = self.take()
        if kind == "num":
            return ("num", Fraction(val))
        if kind == "id":
            return ("const", val) if val in CONSTANTS else ("var", val)
        if (kind, val) == ("op", "("):
            e = self.expr()
            self.expect(")")
            return e
        raise SyntaxError(f"unexpected {val!r} in {self.src!r}")


def _int_literal(t):
    if t[0] == "num" and t[1].denominator == 1:
        return int(t[1])
    if t[0] == "neg" and t[1][0] == "num" and t[1][1].denominator == 1:
        return -int(t[1][1])
    return None


def parse(s):
    p = _Parser(s)
    t = p.expr()
    if p.peek()[0] != "end":
        raise SyntaxError(f"trailing input {p.peek()[1]!r} in {s!r}")
    return t


# ---------------------------------------------------------------- printing

_PREC = {"add": 1, "mul": 2, "div": 2, "neg": 3, "pow": 4, "rpow": 4}


def _prec(t):
    if t[0] == "num":
        return 5 if t[1] >= 0 and t[1].denominator == 1 else 2
    return _PREC.get(t[0], 5)


def show(t):
    """Print t so that parse(show(t)) denotes t.

    Not always the identical tuple: a fraction literal prints as `1/3` and
    reads back as a division of two literals.
    """
    k = t[0]
    if k == "num":
        q = t[1]
        s = str(abs(q)) if q.denominator == 1 else f"{abs(q.numerator)}/{q.denominator}"
        return s if q >= 0 else f"-{s}" if q.denominator == 1 else f"-({s})"
    if k in ("var", "const"):
        return t[1]
    if k == "add":
        a = show(t[1])
        if t[2][0] == "neg":
            return f"{a} - {_wrap(t[2][1], 2)}"
        return f"{a} + {_wrap(t[2], 1, strict=True)}"
    if k == "mul":
        return f"{_wrap(t[1], 2)} * {_wrap(t[2], 2, strict=True)}"
    if k == "div":
        return f"{_wrap(t[1], 2)} / {_wrap(t[2], 2, strict=True)}"
    if k == "neg":
        return f"-{_wrap(t[1], 3, strict=True)}"
    if k == "pow":
        e = str(t[2]) if t[2] >= 0 else f"({t[2]})"
        return f"{_wrap(t[1], 4, strict=True)}^{e}"
    if k == "rpow":
        return f"{_wrap(t[1], 4, strict=True)}^{_wrap(t[2], 4)}"
    if k == "app":
        return f"{t[1]}({', '.join(show(a) for a in t[2])})"
    raise ValueError(f"not a term: {t!r}")


def _wrap(t, prec, strict=False):
    p = _prec(t)
    need = p < prec or (strict and p == prec)
    # A negative literal is printed with a leading minus, which the parser
    # reads as unary: parenthesise it anywhere but at the far left.
    if t[0] == "num" and t[1] < 0:
        need = need or strict or prec > 1
    s = show(t)
    return f"({s})" if need else s


# ---------------------------------------------------------------- utilities

def free_vars(t, acc=None):
    acc = set() if acc is None else acc
    k = t[0]
    if k == "var":
        acc.add(t[1])
    elif k in ("add", "mul", "div", "rpow"):
        free_vars(t[1], acc)
        free_vars(t[2], acc)
    elif k in ("neg", "pow"):
        free_vars(t[1], acc)
    elif k == "app":
        for a in t[2]:
            free_vars(a, acc)
    return acc


def subterms(t):
    yield t
    k = t[0]
    if k in ("add", "mul", "div", "rpow"):
        yield from subterms(t[1])
        yield from subterms(t[2])
    elif k in ("neg", "pow"):
        yield from subterms(t[1])
    elif k == "app":
        for a in t[2]:
            yield from subterms(a)


def replace(t, old, new):
    """Replace every syntactic occurrence of `old` in t — a rewrite's shape."""
    if t == old:
        return new
    k = t[0]
    if k in ("add", "mul", "div", "rpow"):
        return (k, replace(t[1], old, new), replace(t[2], old, new))
    if k == "neg":
        return (k, replace(t[1], old, new))
    if k == "pow":
        return (k, replace(t[1], old, new), t[2])
    if k == "app":
        return (k, t[1], tuple(replace(a, old, new) for a in t[2]))
    return t


def evaluate(t, env, funcs=None):
    """Exact value of t, with `env` for variables and `funcs` for any app.

    Raises ZeroDivisionError where a divisor vanishes. Used by the tests as an
    independent oracle: any assignment of rationals to variables and any
    rational function standing in for an opaque atom is a model of ℚ[atoms].
    """
    funcs = funcs or {}
    k = t[0]
    if k == "num":
        return t[1]
    if k == "var":
        return env[t[1]]
    if k == "const":
        return env[t[1]]
    if k == "add":
        return evaluate(t[1], env, funcs) + evaluate(t[2], env, funcs)
    if k == "mul":
        return evaluate(t[1], env, funcs) * evaluate(t[2], env, funcs)
    if k == "neg":
        return -evaluate(t[1], env, funcs)
    if k == "div":
        return evaluate(t[1], env, funcs) / evaluate(t[2], env, funcs)
    if k == "pow":
        b = evaluate(t[1], env, funcs)
        if t[2] < 0 and b == 0:
            raise ZeroDivisionError("negative power of zero")
        return b ** t[2]
    if k == "app":
        return funcs[t[1]](*(evaluate(a, env, funcs) for a in t[2]))
    raise ValueError(f"cannot evaluate {t[0]}")
