"""`simpl` (SCRIPT.md): `close` with the value the goal names, computed.

Untrusted, like the parser: the computed value is proposed as a typed one
is, so the kernel's scope, schema, check and E27's evaluated-form test all
still run on it, and a bug here can only propose a wrong value, which the
check refuses.
"""

from types import SimpleNamespace

import script
import session  # noqa: F401  puts kernel/ on the path

import field as FD  # noqa: E402
import residual as RD  # noqa: E402
from terms import Call, MVar, Refused, children, fv, show, trees  # noqa: E402


def _calls(t):
    return isinstance(t, Call) or any(_calls(c) for _, c in children(t)
                                      if hasattr(c, "__dataclass_fields__"))


def filled(move, args, state):
    """(move, args) as the kernel takes it: `simpl` becomes `close` with
    its value computed from state's goal, and anything else is unchanged.
    The value is the goal's left side in field's normal form, which evaluates literal
    arithmetic and collects like terms and nothing else; an entry still to
    apply (exp 1, sqrt 8) is left for E27 to name. The check becomes field
    when the value keeps a denominator ring cannot clear. Raises
    TacticError when the left side is not a constant."""
    if move != "simpl":
        return move, args
    g = state.goal[0]
    lhs = g.lhs
    what = ("an integral or a derivative" if any(trees(lhs)) else
            f"the variable {', '.join(sorted(fv(lhs)))}" if fv(lhs) else
            "a declared function" if _calls(lhs) else None)
    if not isinstance(g.rhs, MVar) or what:
        raise script.TacticError(
            "simpl computes the value of a goal that is only constants, "
            f"and this one has {what or 'no ?A to name'}; make the move "
            "that removes it first, or name the value with close T")
    try:
        num, den, atoms = FD.field_parts(lhs)
    except Refused as r:
        raise script.TacticError(f"simpl: cannot compute the value "
                                 f"({r.message}); name it with close T") \
            from None
    parts = SimpleNamespace(num=num, den=den, atoms=atoms)
    out = {**args, "value": show(RD.residual_term(parts))}
    if den:
        out["check"] = "field"
    return "close", out
