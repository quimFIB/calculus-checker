"""The speculative probe (DESIGN.md §8.6; app/UI.md §4): floating point,
navigation only, never evidence.

Untrusted, and further from the kernel than anything else here: it
evaluates a goal's side in doubles, integrals by adaptive Gauss–Kronrod,
and compares the value before and after a step. It never enters the
obligation pane and the page marks it `~`, never `✓`.
"""

import math

from assist.shapes import KERNEL  # noqa: F401  (puts kernel/ on the path)

from terms import (Add, App, Const, Deriv, Div, Integral, MVar, Mul, Neg,
                   NegInf, Num, PosInf, Pow, RPow, Var, fv)

BUDGET = 50_000  # integrand evaluations per value
TOL = 1e-12
MAX_DEPTH = 40
AGREE = 8  # significant digits for "agree"
CAP = 12

# Gauss–Kronrod 7–15 nodes and weights on [-1, 1]
_XK = [0.991455371120812639206854697526329, 0.949107912342758524526189684047851,
       0.864864423359769072789712788640926, 0.741531185599394439863864773280788,
       0.586087235467691130294144845693013, 0.405845151377397166906606412076961,
       0.207784955007898467600689403773245, 0.0]
_WK = [0.022935322010529224963732008058970, 0.063092092629978553290700663189204,
       0.104790010322250183839876322541518, 0.140653259715525918745189590510238,
       0.169004726639267902826583426598550, 0.190350578064785409913256402421014,
       0.204432940075298892414161999234649, 0.209482141084727828012999174891714]
_WG = [0.129484966168869693270611432679082, 0.279705391489276667901467771423780,
       0.381830050505118944950369775488975, 0.417959183673469387755102040816327]


class Skip(Exception):
    """The value cannot be probed; the message says why."""


class _Budget:
    def __init__(self):
        self.left = BUDGET

    def spend(self, n):
        self.left -= n
        if self.left < 0:
            raise Skip("over its evaluation budget")


def _gk(f, a, b):
    c, h = (a + b) / 2, (b - a) / 2
    fc = f(c)
    k, g = _WK[7] * fc, _WG[3] * fc
    for i in range(7):
        x = h * _XK[i]
        s = f(c - x) + f(c + x)
        k += _WK[i] * s
        if i % 2 == 1:
            g += _WG[i // 2] * s
    return k * h, abs((k - g) * h)


def _adapt(f, a, b, budget, depth=0):
    budget.spend(15)
    v, err = _gk(f, a, b)
    if err <= max(TOL * abs(v), 1e-15) or depth >= MAX_DEPTH:
        if depth >= MAX_DEPTH and err > 1e-8 * max(1.0, abs(v)):
            raise Skip("the integral does not settle")
        return v
    m = (a + b) / 2
    return (_adapt(f, a, m, budget, depth + 1)
            + _adapt(f, m, b, budget, depth + 1))


def _integral(t, env, budget):
    lo, hi = t.lo, t.hi
    body = lambda x: _ev(t.body, {**env, t.var: x}, budget)  # noqa: E731
    if isinstance(lo, NegInf) and isinstance(hi, PosInf):
        return (_half(body, 0.0, 1, budget) - _half(body, 0.0, -1, budget))
    if isinstance(hi, PosInf):
        return _half(body, _ev(lo, env, budget), 1, budget)
    if isinstance(lo, NegInf):
        return -_half(body, _ev(hi, env, budget), -1, budget)
    return _adapt(body, _ev(lo, env, budget), _ev(hi, env, budget), budget)


def _half(f, a, sign, budget):
    """∫ from a to sign·∞, by x = a + sign·s/(1 − s), s in [0, 1)."""
    def g(s):
        return f(a + sign * s / (1 - s)) / (1 - s) ** 2
    return sign * _adapt(g, 0.0, 1.0, budget)


_FNS = {"sin": math.sin, "cos": math.cos, "tan": math.tan, "exp": math.exp,
        "ln": math.log, "sqrt": math.sqrt, "abs": abs, "asin": math.asin,
        "acos": math.acos, "atan": math.atan, "sinh": math.sinh,
        "cosh": math.cosh, "tanh": math.tanh, "asinh": math.asinh,
        "acosh": math.acosh, "atanh": math.atanh}


def _ev(t, env, budget):
    k = type(t)
    if k is Num:
        return float(t.n)
    if k is Const:
        return math.pi if t.name == "pi" else math.e
    if k is Var:
        if t.name not in env:
            raise Skip(f"symbol {t.name}")
        return env[t.name]
    if k is Neg:
        return -_ev(t.a, env, budget)
    if k is Add:
        return _ev(t.a, env, budget) + _ev(t.b, env, budget)
    if k is Mul:
        return _ev(t.a, env, budget) * _ev(t.b, env, budget)
    if k is Div:
        return _ev(t.a, env, budget) / _ev(t.b, env, budget)
    if k is Pow:
        return _ev(t.base, env, budget) ** t.n
    if k is RPow:
        return _ev(t.base, env, budget) ** _ev(t.exp, env, budget)
    if k is App:
        return _FNS[t.fn](_ev(t.arg, env, budget))
    if k is Integral:
        return _integral(t, env, budget)
    if k is Deriv:
        raise Skip("a derivative node")
    raise Skip(f"a {k.__name__} node")


def side(goal):
    """The goal's value side: lhs when the right side is ?A, else lhs − rhs."""
    g = goal[0]
    return g.lhs if isinstance(g.rhs, MVar) else Add(g.lhs, Neg(g.rhs))


def value(goal):
    """The float value of the goal's value side, or raises Skip."""
    t = side(goal)
    free = fv(t)
    if free:
        raise Skip("symbols " + ", ".join(sorted(free)))
    try:
        v = _ev(t, {}, _Budget())
    except Skip:
        raise
    except (ArithmeticError, ValueError, OverflowError, RecursionError):
        raise Skip("it does not evaluate in floating point") from None
    if not math.isfinite(v):
        raise Skip("it does not evaluate to a finite number")
    return v


def digits(a, b):
    """Agreeing significant digits of a and b, 0 to CAP, on the scale
    max(|a|, |b|, 1), so float noise around a zero value (1.2e-16 for
    sin(2*(pi/2))) reads as agreement, not as a changed value."""
    if a == b:
        return CAP
    scale = max(abs(a), abs(b), 1.0)
    rel = abs(a - b) / scale
    return max(0, min(CAP, int(math.floor(-math.log10(rel)))))


def compare(before, after):
    """UI.md §4's probe object for two goals (tuples), or a skip."""
    try:
        a, b = value(before), value(after)
    except Skip as s:
        return {"skipped": str(s)}
    d = digits(a, b)
    return {"before": a, "after": b, "digits": d, "agree": d >= AGREE}
