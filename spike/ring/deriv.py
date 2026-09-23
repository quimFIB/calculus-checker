"""`deriv`, spike-grade: enough of §6.3 to produce what `field` is handed.

§6.3 makes `deriv` an untrusted tactic that walks the syntax applying the
table. This one applies the entries' output forms literally — it does not
tidy `0 * u` or `1 * D[x]u` away — because the point of the spike is to time
`field` on the terms it will really receive, not on hand-simplified ones.
Side conditions are not collected; they are §5.3's business, not §6.2's.

Three places where the table as written does not cover what it meets, each
bridged here in the obvious way and each noted in README.md:

- a subterm with no free x (pi, sqrt 3, another variable) differentiates
  to 0, though `d_const` is stated for a rational literal only;
- `-u` becomes `(-1) * u` and then `d_mul`: there is no `d_neg`;
- `u / v` becomes `u * (1/v)`, then `d_mul` and `d_inv`: there is no `d_div`.
"""

from terms import ONE, ZERO, app, free_vars, num

MINUS_ONE = num(-1)


def _mul(a, b):
    return ("mul", a, b)


def _div(a, b):
    return ("div", a, b)


def _neg(a):
    return ("neg", a)


def _add(a, b):
    return ("add", a, b)


def _sq(a):
    return ("pow", a, 2)


# name -> (u, du) -> D[x] f(u), as §6.3 states each output form
_TABLE = {
    "exp": lambda u, du: _mul(app("exp", u), du),
    "ln": lambda u, du: _div(du, u),
    "sqrt": lambda u, du: _div(du, _mul(num(2), app("sqrt", u))),
    "sin": lambda u, du: _mul(app("cos", u), du),
    "cos": lambda u, du: _mul(_neg(app("sin", u)), du),
    "tan": lambda u, du: _mul(_add(ONE, _sq(app("tan", u))), du),
    "asin": lambda u, du: _div(du, app("sqrt", _add(ONE, _neg(_sq(u))))),
    "acos": lambda u, du: _div(_neg(du), app("sqrt", _add(ONE, _neg(_sq(u))))),
    "atan": lambda u, du: _div(du, _add(ONE, _sq(u))),
    "sinh": lambda u, du: _mul(app("cosh", u), du),
    "cosh": lambda u, du: _mul(app("sinh", u), du),
    "tanh": lambda u, du: _mul(_add(ONE, _neg(_sq(app("tanh", u)))), du),
    "asinh": lambda u, du: _div(du, app("sqrt", _add(_sq(u), ONE))),
    "acosh": lambda u, du: _div(du, app("sqrt", _add(_sq(u), MINUS_ONE))),
    "atanh": lambda u, du: _div(du, _add(ONE, _neg(_sq(u)))),
    "abs": lambda u, du: _mul(_div(u, app("abs", u)), du),
}


def deriv(t, x):
    """D[x] t, by the §6.3 table."""
    if x not in free_vars(t):
        return ZERO
    k = t[0]
    if k == "var":
        return ONE
    if k == "add":
        return _add(deriv(t[1], x), deriv(t[2], x))
    if k == "neg":
        return deriv(_mul(MINUS_ONE, t[1]), x)
    if k == "mul":
        u, v = t[1], t[2]
        return _add(_mul(deriv(u, x), v), _mul(u, deriv(v, x)))
    if k == "div":
        u, v = t[1], t[2]
        if u == ONE:
            return _div(_neg(deriv(v, x)), _sq(v))
        return deriv(_mul(u, _div(ONE, v)), x)
    if k == "pow":
        u, n = t[1], t[2]
        if n == 0:
            return ZERO
        return _mul(_mul(num(n), ("pow", u, n - 1)), deriv(u, x))
    if k == "app" and t[1] in _TABLE and len(t[2]) == 1:
        u = t[2][0]
        return _TABLE[t[1]](u, deriv(u, x))
    raise NotImplementedError(f"deriv: no rule for {k} {t[1] if k == 'app' else ''}")
