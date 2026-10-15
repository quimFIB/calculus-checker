"""Auto-simpl (AUTOSIMPL.md, p1_expected E162): the moves E27 would name,
in E27's order, then simpl's close, each one an ordinary kernel step.

Untrusted, like fill.py. Every move it proposes is fed to the kernel
exactly as a typed one is, so a bug here can propose a move the kernel
refuses, or stop early, and nothing else: the chain is kept only when it
closes the goal with every step accepted and no admission added.
"""

from fractions import Fraction
from types import SimpleNamespace

import fill
import session  # noqa: F401  puts kernel/ on the path

import complexes as CX  # noqa: E402
import entries  # noqa: E402
import field as FD  # noqa: E402
import poly as P  # noqa: E402
import residual as RD  # noqa: E402
import schema as SC  # noqa: E402
from terms import Const, MVar, Mul, Neg, Num, Pow, fv, lit, show, subst  # noqa: E402

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
    p = SC.arg_parts(s)  # E172: the parts of a principal Arg's argument
    if p is not None and e.name.startswith("arg_"):
        re, im = CX.split(s.arg)  # E239: the parts as terms, surds kept
        a, b = (Num(0) if x is None else _nf(CX._real(x)) for x in (re, im))
        two = e.name in ("arg_right", "arg_left_up", "arg_left_down")
        return [{"u": a, "v": b} if two else
                {"u": b if e.name.startswith("arg_i") else a}]
    bound = {}
    if SC._tree_match(e.statement.lhs, s, frozenset(e.schema), bound):
        return [bound]
    return []


def redexes(side):
    """(entry name, subterm, [inst, ...]) for each redex in `side` that E27
    (a) counts and a rewrite can take, in E27's order: pre-order, and at
    each node the ENTRIES equations in order, then rpow_int (E163)."""
    eqs = [e for e in entries.ENTRIES.values() if e.statement.op == "=="]
    nodes = list(SC._preorder(side))
    for s, _ in nodes:
        if not CX.real_form(s):  # (a) reads real-form subterms (E173)
            continue
        for e in eqs:
            if SC._counts_safe(e, s):
                insts = _insts(e, s)
                if insts:
                    yield e.name, s, insts
        per = SC.period_shift(s)  # E181: sin, cos of a multiple of pi
        if per is not None:
            q, k = per
            c = q - 2 * k
            yield f"{s.fn}_period", s, [{
                "u": Num(0) if c == 0 else Const("pi") if c == 1
                else Mul(lit(c), Const("pi")),
                "k": Num(k) if k >= 0 else Neg(Num(-k))}]
        q = SC.table_q(s)  # E239: sin, cos at pi/6 and pi/4 steps
        if q is not None:
            yield f"{s.fn}_table", s, [{"q": lit(q)}]
        bk = SC.branch_k(s)  # E239: a closed non-principal arg
        if bk is not None:
            th, k = bk
            yield "arg_branch", s, [{"theta": th, "w": s.arg,
                                     "k": Num(k) if k >= 0 else Neg(Num(-k))}]
        n = SC.rpow_int_exponent(s)
        if n is not None:
            yield "rpow_int", s, [{"u": s.base, "n": Num(n) if n >= 0
                                   else Neg(Num(-n))}]
    for s, _ in nodes:  # (c): a closed complex term not yet rectangular
        if not fv(s) and not CX.real_form(s) and not SC._rect(s):
            yield "parts", s, [{}]


def _value(lhs, pairs):
    """lhs as simpl computes it, reduced by the facts `pairs` ((a^k, r)
    Terms, field's fact reduction), and whether a denominator stays."""
    v, den = fill._computed(lhs)
    if not pairs:
        return v, den
    w, _ = fill._args_computed(lhs)
    if CX.has_complex(w):  # E239: each part reduced, then rejoined
        parts = []
        for part in CX.split(w):
            if part is None:
                parts.append(None)
                continue
            r = _reduced(CX._real(part), pairs)
            parts.append(None if r == Num(0) else r)
        return CX.join(tuple(parts)), den
    return _reduced(w, pairs), den


def _reduced(w, pairs):
    try:
        FD.field(w, Num(0), pairs)
        return Num(0)
    except FD.NotEqual as ne:
        return RD.residual_term(_rationalised(ne.residual, pairs))


def _reduce_poly(p, sq):
    """p with each atom^k of a fact's atom (atom^2 == q) written
    q^(k//2)*atom^(k%2)."""
    out = {}
    for mono, c in p.items():
        new = []
        for i, k in mono:
            if i in sq:
                c = c * sq[i] ** (k // 2)
                k = k % 2
            if k:
                new.append((i, k))
        out = P.add(out, {tuple(new): c})
    return out


def _rationalised(res, pairs):
    """The residual with each denominator power of a fact's atom reduced
    as the fact reduces the numerator: (sqrt q)^e is q^(e//2)*(sqrt
    q)^(e%2), the constant moved into the numerator (E210). Field reduces
    only the numerator, so without this (sqrt 2)^3 stays below the line
    and the next fact asked for is the same one."""
    sq = {}
    for lhs, rhs in pairs:
        q = FD.rational_value(rhs)
        if type(lhs) is Pow and lhs.n == 2 and lhs.base in res.atoms \
                and q is not None and q > 0:
            sq[res.atoms.index(lhs.base)] = q
    if not sq:
        return res
    den, scale = [], Fraction(1)
    for p, e in res.den:
        mono = next(iter(p)) if len(p) == 1 else None
        idx = mono[0][0] if mono and len(mono) == 1 and mono[0][1] == 1 \
            and p[mono] == 1 else None
        if idx in sq:
            scale *= sq[idx] ** (e // 2)
            if e % 2:
                den.append((p, 1))
            continue
        r = _reduce_poly(p, sq)  # E239: a factor holding atom^2 inside a sum
        if P.is_const(r):
            scale *= P.const_value(r) ** e
        else:
            den.append((r, e))
    return SimpleNamespace(num=P.scale(res.num, 1 / scale), den=tuple(den),
                           atoms=res.atoms)


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

    # 1. rewrites, on the goal: the first redex, in E27's order, whose
    # rewrite the kernel accepts; a refused candidate yields to the next
    for _ in range(MAX_REWRITES + 1):
        first, done = None, False
        for name, at, insts in redexes(state.goal[0].lhs):
            if len(steps) == MAX_REWRITES:
                raise Stopped(f"gave up after {MAX_REWRITES} rewrites")
            for inst in insts:
                why = try_step("rewrite", {"entry": name, "inst": _text(inst),
                                           "at": show(at)})
                if why is None:
                    done = True
                    break
                first = first or why
            if done:
                break
        if not done:
            if first is not None:
                raise _stopped(first)
            break
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

