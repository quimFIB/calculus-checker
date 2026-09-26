"""Classify a force as F(t), F(v), F(x) or none (DESIGN.md §12.1;
app/assist/CLASSIFY.md).

Untrusted (tier 2): a tactic report, not a judgement (§5.2). It reads the
free variables of the force's term, as §12.1 decides `classify`, and uses
the kernel's `ring` only as a normaliser to see whether zeroing a
parameter removes a state variable. Nothing here enters a proof.
"""

from assist.shapes import KERNEL  # noqa: F401  (puts kernel/ on the path)
import field as FD
from terms import Add, Neg, Num, Refused, Var, fv, parse_term, subst

REDUCTION = {
    "F(t)": "integrate once, keeping the constant: v(t) = v(0) + "
            "Int[s = 0 .. t] F(s)/m",
    "F(v)": "separate: t = Int[w = v(0) .. v] m/F(w), and note where F "
            "vanishes",
    "F(x)": "multiply by the velocity: m v^2/2 + U(x) = E, with U' = -F",
}
_ROLE = {"t": "time", "v": "velocity", "x": "position"}


class Refusal(Exception):
    def __init__(self, code, message):
        super().__init__(f"{code}: {message}")
        self.code, self.message = code, message


def _depends(F, var):
    """F changes when var is shifted by 1: F[var := var + 1] - F is not
    ring-zero. An atom whose argument holds var counts as changed."""
    try:
        return not FD.ring_is_zero(Add(subst(F, {var: Add(Var(var),
                                                           Num(1))}),
                                       Neg(F)))
    except Refused:
        return True


def _case(state):
    return f"F({state})"


def classify(force, t="t", v="v", x="x", sig=None):
    """The report CLASSIFY.md describes, as a dict."""
    names = {"t": t, "v": v, "x": x}
    if len(set(names.values())) != 3:
        raise Refusal("bad-names", "t, v and x must be three different names")
    try:
        F = parse_term(force, sig or {})
    except Refused as r:
        raise Refusal("bad-term", r.message) from None
    free = [k for k in ("t", "v", "x") if names[k] in fv(F)
            and _depends(F, names[k])]
    shown = [names[k] for k in free]
    if not free:
        return {"case": "constant", "free": [], "reduction": REDUCTION["F(t)"],
                "why": "no state variable appears: every case applies, and "
                       "F(t)'s single integration is the shortest",
                "repairs": []}
    if len(free) == 1:
        k = free[0]
        return {"case": _case(k), "free": shown, "reduction": REDUCTION[_case(k)],
                "why": f"only the {_ROLE[k]} {names[k]} appears on the "
                       "right-hand side",
                "repairs": []}
    params = sorted(fv(F) - set(names.values()))
    repairs = []
    for p in params:
        G = subst(F, {p: Num(0)})
        left = [k for k in free if _depends(G, names[k])]
        if len(left) == 1:
            repairs.append({"parameter": p, "case": _case(left[0])})
    roles = " and ".join(f"the {_ROLE[k]} {names[k]}" for k in free)
    return {"case": "none", "free": shown, "reduction": None,
            "why": f"{roles} both appear, so no single reduction applies"
            if len(free) == 2 else f"{roles} all appear",
            "repairs": repairs}
