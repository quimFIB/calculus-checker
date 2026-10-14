"""`simpl` (SCRIPT.md): `close` with the value the goal names, computed.

Untrusted, like the parser: the computed value is proposed as a typed one
is, so the kernel's scope, schema, check and E27's evaluated-form test all
still run on it, and a bug here can only propose a wrong value, which the
check refuses.
"""

from dataclasses import replace
from types import SimpleNamespace

import script
import session  # noqa: F401  puts kernel/ on the path

import complexes as CX  # noqa: E402
import field as FD  # noqa: E402
import residual as RD  # noqa: E402
from terms import (App, Call, MVar, Num, RPow, Refused, children, fv,  # noqa: E402
                   show, trees)


def _calls(t):
    return isinstance(t, Call) or any(_calls(c) for _, c in children(t)
                                      if hasattr(c, "__dataclass_fields__"))


def _computed(t):
    """(t in field's normal form, whether a denominator stayed), with the
    argument of every function and real power in t computed first,
    innermost first. field reads sqrt(1 + 1) as an atom keyed by its
    argument's normal form but prints the term it first saw, so without
    this the arithmetic under a function would come back undone. A
    denominator staying inside an argument counts too: ring keys that
    argument without cancelling, so the check must be field."""
    if CX.has_complex(t):  # E174: a complex value as its two parts
        out, dens = [], False
        for x in CX.split(t):
            if x is None:
                out.append(None)
                continue
            v, d = _computed(x)
            out.append(None if v == Num(0) else v)
            dens = dens or d
        return CX.join(tuple(out)), dens
    t, inner = _args_computed(t)
    num, den, atoms = FD.field_parts(t)
    parts = SimpleNamespace(num=num, den=den, atoms=atoms)
    return RD.residual_term(parts), bool(den) or inner


def _args_computed(t):
    """(t with each function's and real power's arguments computed,
    whether a denominator stayed in one). Arithmetic around them is left
    for the one normal form _computed takes of the whole."""
    if type(t) in (App, RPow):
        kids = {n: _computed(c) for n, c in children(t)}
    else:
        kids = {n: _args_computed(c) for n, c in children(t)}
    if not kids:
        return t, False
    return (replace(t, **{n: c for n, (c, _) in kids.items()}),
            any(d for _, d in kids.values()))


def not_constant(lhs):
    """None when lhs is only constants, else what is not: an integral or
    derivative, a variable, or a declared function. simpl's test, and
    auto-simpl's trigger (AUTOSIMPL.md)."""
    return ("an integral or a derivative" if any(trees(lhs)) else
            f"the variable {', '.join(sorted(fv(lhs)))}" if fv(lhs) else
            "a declared function" if _calls(lhs) else None)


def filled(move, args, state, auto=False):
    """(move, args) as the kernel takes it: `simpl` becomes `close` with
    its value computed from state's goal, and anything else is unchanged.
    The value is the goal's left side in field's normal form, which evaluates literal
    arithmetic, inside a function's argument too (sqrt(1 + 1) is sqrt 2),
    and collects like terms and nothing else; an entry still to
    apply (exp 1, sqrt 8) is left for E27 to name. The check becomes field
    when the value keeps a denominator ring cannot clear. Raises
    TacticError when the left side is not a constant. With auto-simpl on
    (`auto`, E162) a `simpl` whose goal passes that test stays `simpl`,
    for the session to run AUTOSIMPL.md's chain."""
    if move != "simpl":
        return move, args
    if not state.goal:  # the kernel's proof-finished says it
        return move, args
    g = state.goal[0]
    lhs = g.lhs
    what = not_constant(lhs)
    if not isinstance(g.rhs, MVar) or what:
        raise script.TacticError(
            "simpl computes the value of a goal that is only constants, "
            f"and this one has {what or 'no ?A to name'}; make the move "
            "that removes it first, or name the value with close T")
    if auto:
        return move, args
    try:
        value, den = _computed(lhs)
    except Refused as r:
        raise script.TacticError(f"simpl: cannot compute the value "
                                 f"({r.message}); name it with close T") \
            from None
    out = {**args, "value": show(value)}
    if den:
        out["check"] = "field"
    return "close", out
