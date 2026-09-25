"""The progress signal (DESIGN.md §8.5; app/UI.md §3): after an accepted
move, what changed. A heuristic, never a judgement about the proof: it
says which measure fired, and a move it calls `worse` may be the right one.

Untrusted (tier 2). It runs the palette, the card and the recognizer once
more over the parent's goal and the new one.
"""

from assist import palette as PL
from assist import recognizer as R
from assist.shapes import shape
from terms import (App, Call, Const, Deriv, Integral, RPow, Term, Var,
                   children, show)


def _first_int(goal):
    ints = PL.integrals(goal)
    return ints[0] if ints else None


def _row(goal):
    i = _first_int(goal)
    if i is None:
        return None
    hit = R.first(i.body, i.var)
    return hit[0].family if hit else None


def _rational(i):
    s = shape(i.body, i.var)
    return s is not None and s.x_only()


def finishable(goal):
    """A named move closes it from here: close, when no Int or D is left
    under ?A; or the first Int's integrand is on the card or rational."""
    if not goal:
        return None
    if any(m["move"] == "close" for m in PL.moves(goal)):
        return "close names the value"
    i = _first_int(goal)
    if i is None:
        return None
    if R.m_card(i.body, i.var) is not None:
        return f"{show(i.body)} is on the card"
    if _rational(i):
        return f"{show(i.body)} is a rational function"
    return None


_ATOMIC = (Var, Const, App, RPow, Call, Integral, Deriv)


def _atoms(goal):
    """Distinct atom-like subterms of the sides (names, applications,
    real powers, calls, integrals and derivatives), iteratively."""
    seen, stack = set(), list(PL.sides(goal))
    while stack:
        u = stack.pop()
        if isinstance(u, _ATOMIC):
            seen.add(u)
        stack.extend(k for _, k in children(u) if isinstance(k, Term))
    return len(seen)


def _depth(t):
    """The term's depth, iteratively (terms can be deep)."""
    best, stack = 0, [(t, 1)]
    while stack:
        u, d = stack.pop()
        best = max(best, d)
        stack.extend((k, d + 1) for _, k in children(u)
                     if isinstance(k, Term))
    return best


def _goal_depth(goal):
    return max((_depth(s) for s in PL.sides(goal)), default=0)


def signal(before, after):
    """UI.md §3: {signal, detail} for a step from goal `before` to `after`."""
    if after is None:
        return {"signal": "closed", "detail": "the goal is closed"}
    fa = finishable(after)
    fewer = len(PL.integrals(after)) < len(PL.integrals(before))
    if fa and (fewer or not finishable(before)):
        return {"signal": "finishable", "detail": fa}
    old = {(r["entry"], r["at"]) for r in PL.rewrites(before)}
    new = [r for r in PL.rewrites(after) if (r["entry"], r["at"]) not in old]
    if new:
        return {"signal": "rule now matches",
                "detail": f"{new[0]['entry']} now matches at {new[0]['at']}"}
    ra, rb = _row(before), _row(after)
    if rb is not None and rb != ra:
        return {"signal": "technique named",
                "detail": f"the recognizer now names {rb}"
                          + (f" (was {ra})" if ra else "")}
    na, nb = _atoms(before), _atoms(after)
    da, db = _goal_depth(before), _goal_depth(after)
    if ((nb > na or db > da) and ra != "parts cycle"
            and PL.integrals(before) and PL.integrals(after)):
        what = f"atoms {na} -> {nb}" if nb > na else f"depth {da} -> {db}"
        return {"signal": "worse", "detail": what}
    return {"signal": "no progress",
            "detail": f"atoms {na} -> {nb}, depth {da} -> {db}"}
