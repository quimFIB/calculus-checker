"""Auto-simpl (AUTOSIMPL.md, p1_expected E162): the moves E27 would name,
in E27's order, then simpl's close, each one an ordinary kernel step.

Untrusted, like fill.py. Every move it proposes is fed to the kernel
exactly as a typed one is, so a bug here can propose a move the kernel
refuses, or stop early, and nothing else: the chain is kept only when it
closes the goal with every step accepted and no admission added.
"""

from types import SimpleNamespace

import fill
import session  # noqa: F401  puts kernel/ on the path

import entries  # noqa: E402
import field as FD  # noqa: E402
import residual as RD  # noqa: E402
import schema as SC  # noqa: E402
from terms import MVar, Neg, Num, show, subst  # noqa: E402

MAX_REWRITES, MAX_FACTS = 32, 8

# E27 counts these at f(b); u := the normal form of -b undoes the sign
_ODD = ("atan_odd", "sin_odd", "cos_even")

# Phase 2: the redex E27 names in the value -> the field fact that reduces
# it, as (entry, inst) built from the redex
_FACTS = {
    "sqrt_sq_val": lambda s: ("sqrt_sq_val", {"a": s.base.arg}),
    "pyth": lambda s: ("pyth_cos", {"u": s.b.base.arg}),
}


class Stopped(Exception):
    """The chain did not close the goal: `message` says why, and
    `residual` is the refused step's, if it carried one."""

    def __init__(self, message, residual=None):
        super().__init__(message)
        self.message, self.residual = message, residual


def constant_goal(state):
    """AUTOSIMPL.md's trigger on a state: an open goal `L == ?A` with L
    only constants (fill.not_constant)."""
    g = state.goal[0] if state.goal else None
    return (g is not None and isinstance(g.rhs, MVar)
            and fill.not_constant(g.lhs) is None)


def admissions(state):
    import kernel as K
    return sum(ob.status == K.ADMITTED for ob in state.obligations())


def _nf(t):
    num, den, atoms = FD.field_parts(t)
    return RD.residual_term(SimpleNamespace(num=num, den=den, atoms=atoms))


def _insts(e, s):
    """The instantiations to try for a rewrite by entry e at subterm s,
    which E27 counts, in order; [] when a rewrite cannot take it."""
    if not e.schema:
        return [{}]
    if e.name == "sqrt_sq":
        (p,), atoms = SC._ring(s.arg)
        c = RD.poly_term(SC._poly_sqrt(p), atoms)
        return [{"u": c}, {"u": _nf(Neg(c))}]
    if e.name in _ODD:
        return [{"u": _nf(Neg(s.arg))}]
    bound = {}
    if SC._tree_match(e.statement.lhs, s, frozenset(e.schema), bound):
        return [bound]
    return []


def redexes(side):
    """(entry name, subterm, [inst, ...]) for each redex in `side` that E27
    (a) counts and a rewrite can take, in E27's order: pre-order, and at
    each node the ENTRIES equations in order, then rpow_int (E163)."""
    eqs = [e for e in entries.ENTRIES.values() if e.statement.op == "=="]
    for s, _ in SC._preorder(side):
        for e in eqs:
            if SC._counts(e, s):
                insts = _insts(e, s)
                if insts:
                    yield e.name, s, insts
        n = SC.rpow_int_exponent(s)
        if n is not None:
            yield "rpow_int", s, [{"u": s.base, "n": Num(n) if n >= 0
                                   else Neg(Num(-n))}]


def _value(lhs, pairs):
    """lhs as simpl computes it, reduced by the facts `pairs` ((a^k, r)
    Terms, field's fact reduction), and whether a denominator stays."""
    v, den = fill._computed(lhs)
    if not pairs:
        return v, den
    w, _ = fill._args_computed(lhs)
    try:
        FD.field(w, Num(0), pairs)
        return Num(0), den
    except FD.NotEqual as ne:
        return RD.residual_term(ne.residual), den


def _text(inst):
    return {k: show(v) for k, v in inst.items()}


def run(state, handles, feed, facts=()):
    """_run, with anything but Stopped turned into Stopped: an untrusted
    computation that raises (a power too large to normalise, a kernel
    error on odd input) stops the chain, and the move before it stands
    (AUTOSIMPL.md, all or nothing)."""
    try:
        return _run(state, handles, feed, facts)
    except Stopped:
        raise
    except Exception as e:
        raise Stopped(f"{getattr(e, 'code', type(e).__name__)}: "
                      f"{getattr(e, 'message', e)}") from None


def _run(state, handles, feed, facts=()):
    """The chain from `state`, whose goal is constant (constant_goal).
    `feed(state, handles, move, args)` is the session's: it takes args in
    problem-file shapes and returns (new state, new handles), or raises
    session.Refusal. `facts` are fact refs the learner gave a typed
    simpl (`using h`), added to the close.

    Returns (steps, state, handles) when the goal closes: steps are the
    (move, args) fed, in order. Raises Stopped otherwise, and then nothing
    it fed is to be kept."""
    from session import Refusal
    base = admissions(state)
    steps = []

    def try_step(move, args):
        nonlocal state, handles
        try:
            st, hs = feed(state, handles, move, args)
        except Refusal as r:
            return r
        if admissions(st) > base:
            return Stopped(f"{script_text(move, args)} would add an "
                           "admitted obligation")
        state, handles = st, hs
        steps.append((move, args))
        return None

    # 1. rewrites, on the goal
    for _ in range(MAX_REWRITES + 1):
        found = next(redexes(state.goal[0].lhs), None)
        if found is None:
            break
        if len(steps) == MAX_REWRITES:
            raise Stopped(f"gave up after {MAX_REWRITES} rewrites")
        name, at, insts = found
        for inst in insts:
            why = try_step("rewrite", {"entry": name, "inst": _text(inst),
                                       "at": show(at)})
            if why is None:
                break
        else:
            raise _stopped(why)
    # 2. facts, on the value
    pairs, binds = [], []
    for _ in range(MAX_FACTS + 1):
        v, den = _value(state.goal[0].lhs, pairs)
        off = SC.evaluated_offence(v)
        if off is None:
            break
        clause, s, name = off
        if clause != "a" or name not in _FACTS:
            raise Stopped(SC.MESSAGES[clause[0]].format(term=show(s),
                                                         entry=name), s)
        if len(binds) == MAX_FACTS:
            raise Stopped(f"gave up after {MAX_FACTS} facts")
        fe, inst = _FACTS[name](s)
        bind = next(f"auto{k}" for k in range(1, len(handles) + 2)
                    if f"auto{k}" not in handles)
        why = try_step("fact", {"entry": fe, "inst": _text(inst),
                                "bind": bind})
        if why is not None:
            raise _stopped(why)
        st = entries.ENTRIES[fe].statement
        pairs.append((subst(st.lhs, inst), subst(st.rhs, inst)))
        binds.append(["handle", bind])
    # 3. close
    used = [list(f) for f in facts] + binds
    why = try_step("close", {"value": show(v),
                             "check": "field" if used or den else "ring",
                             "facts": used})
    if why is not None:
        raise _stopped(why)
    return steps, state, handles


def _stopped(why):
    if isinstance(why, Stopped):
        return why
    return Stopped(f"{why.code}: {why.message}", why.residual)


def script_text(move, args):
    import script
    try:
        return script.show(move, args)
    except Exception:  # a display nicety only
        return move


def sentences(steps):
    """The steps as script sentences, for display."""
    return [script_text(m, a) for m, a in steps]

