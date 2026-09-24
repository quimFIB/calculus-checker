"""The `closed` answer schema, as a whitelist (DESIGN.md §9; p1_expected E23).

Untrusted: §9 puts the schema checker outside the trusted base. A
permissive schema gives a weaker true theorem, never a false one. The
trusted scope check (E19) runs before this in `close`, so bound names are
not this module's business and Var can be admitted.

Every P1 goal carries `answer schema closed` with no `+ f` extension. When a
problem adds one, `closed_ok` takes the extra declared symbols.
"""

from terms import (Add, App, BUILTINS, Call, Const, Div, Mul, Neg, Num, Pow,
                   RPow, Var, children)

# Admitted node kinds (E23). Refused: Call, Deriv, Integral, MVar, and anything
# else. App is admitted only over the sixteen builtins.
WHITELIST = (Num, Const, Var, Neg, Add, Mul, Div, Pow, RPow, App)


def closed_ok(value, extensions=()):
    """True when every node of `value`, checked raw with nothing unfolded
    (§9), is of a WHITELIST kind, every App is over BUILTINS, and every Call
    is to a symbol in `extensions`. P1 passes none."""
    todo = [value]
    while todo:
        t = todo.pop()
        # Exact types, so no subclass of an admitted kind slips through.
        if type(t) is Call and t.fn in extensions:
            todo.extend(t.args)
        elif type(t) in WHITELIST and (type(t) is not App or t.fn in BUILTINS):
            todo.extend(k for _, k in children(t))
        else:
            return False
    return True
