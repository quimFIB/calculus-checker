"""Three kinds of stuck (DESIGN.md §8.7; app/STUCK.md).

Untrusted (tier 2). The kernel's refusal is shown as it was; this sorts it
into nothing matches, an obligation will not discharge, or the algebra does
not close, and says what to try. A suggestion is only ever shown after
`trial` (the kernel itself, run from the same node without recording
anything) accepted every sentence of it, so an explanation can be unhelpful
but never wrong about the algebra. Numbers are floats marked ≈: navigation,
like the probe (§8.6).
"""

import math
from fractions import Fraction

from assist import palette as PL
from assist import probe
from assist import recognizer as R
from assist.shapes import subterms
import field as FD
from entries import ENTRIES
from terms import (App, Mul, NegInf, Num, PosInf, fv, lit, parse_term, show,
                   subst)

NO_MATCH = ("rewrite-target-not-found", "rewrite-lhs-mismatch",
            "ftc-no-integral", "int-subst-no-integral",
            "int-parts-no-integral", "int-flip-no-integral",
            "int-improper-no-integral", "int-subst-wrong-variable",
            "int-parts-wrong-variable", "int-subst-ambiguous",
            "int-parts-ambiguous", "int-flip-ambiguous",
            "int-improper-finite", "ftc-infinite-endpoint",
            "int-subst-infinite-endpoint", "int-parts-infinite-endpoint",
            "close-no-mvar")
OBLIGATION = ("obligation-decided-false", "obligation-refuted",
              "orientation-undecided")
ALGEBRA = ("ftc-check-failed", "int-improper-check-failed",
           "int-subst-check-failed", "int-parts-check-failed",
           "close-check-failed", "int-subst-endpoint-mismatch",
           "divisor-normalises-to-zero")
# a line for the codes whose fix is a different move
_OTHER_MOVE = {
    "ftc-infinite-endpoint": "An end is infinite: int_improper takes it.",
    "int-subst-infinite-endpoint": "An end is infinite: int_improper "
                                   "first, then substitute.",
    "int-parts-infinite-endpoint": "An end is infinite: int_improper "
                                   "first, then by parts.",
    "int-improper-finite": "Both ends are finite: ftc takes it.",
    "close-no-mvar": "The goal has no ?A to name.",
}
MAX_REWRITES = 5


def _stuck(kind, headline, lines=(), suggest=None):
    return {"kind": kind, "headline": headline, "lines": list(lines),
            "suggest": suggest}


def _num(v):
    return f"≈ {v:.6g}"


def _first_int(goal, args=None):
    ints = PL.integrals(goal)
    if not ints:
        return None
    k = (args or {}).get("occurrence", 0)
    return ints[k] if isinstance(k, int) and 0 <= k < len(ints) else ints[0]


def _accepted(trial, sentences):
    try:
        return bool(trial(sentences))
    except Exception:
        return False


# ---------------------------------------------------------------- no-match

def _canon(text, sig):
    try:
        return show(parse_term(text, sig))
    except Exception:
        return text


def no_match(code, message, goal, move, args, sig, trial):
    rws = PL.rewrites(goal) if goal else []
    lines, suggest = [], None
    if code in _OTHER_MOVE:
        lines.append(_OTHER_MOVE[code])
    target = None
    if move == "rewrite" and isinstance(args.get("at"), str):
        target = _canon(args["at"], sig)
    here = [w for w in rws if w["at"] == target]
    if here:
        lines.append(f"At {target}, what matches: "
                     + "; ".join(w["entry"] for w in here) + ".")
        if len(here) == 1 and _accepted(trial, [here[0]["sentence"]]):
            suggest = [here[0]["sentence"]]
    elif rws:
        lines.append("Rewrites that match here: " + "; ".join(
            f"{w['entry']} at {w['at']}" for w in rws[:MAX_REWRITES])
            + (" …" if len(rws) > MAX_REWRITES else "") + ".")
    else:
        lines.append("No rewrite matches this goal.")
    ms = [m["move"] for m in PL.moves(goal)] if goal else []
    if ms:
        lines.append("Moves whose shape fits: " + ", ".join(ms) + ".")
    i = _first_int(goal)
    if i is not None:
        try:
            step = R.ladder(i.body, i.var)
        except Exception:
            step = None
        lines.append(f"For {show(i)}: {step[1].rstrip('.')}." if step else
                     "The recognizer has no row for the integral.")
    lines.append("? for a nudge.")
    return _stuck("no-match", "No rule matches here", lines, suggest)


# ---------------------------------------------------------------- obligation

_ADVICE = {
    "rewrite": "The entry holds only where its hypothesis does; over this "
               "range it does not. This rewrite is wrong here, or the range "
               "needs splitting.",
    "ftc": "F or the integrand is undefined somewhere on the range: the "
           "integral may be improper there, or F is the wrong "
           "antiderivative.",
}
_ADVICE["int_improper"] = _ADVICE["ftc"]
_SIDE = "The step's side condition fails on this range."


_ORIENT = ("The order of the limits cannot be decided: state it in the "
           "goal's domain (a < b), or give the limits as numbers.")


def obligation(code, message, move):
    advice = _ORIENT if code == "orientation-undecided" else \
        _ADVICE.get(move, _SIDE)
    return _stuck("obligation",
                  "The move applies, but a condition it needs fails",
                  [message, advice])


def admitted(obligations):
    """A node's stuck, from its rendered obligations: the ones this step
    admitted (new and admitted), or None."""
    new = [o for o in obligations if o["new"] and o["status"] == "admitted"]
    if not new:
        return None
    n = len(new)
    word = "admission" if n == 1 else "admissions"
    return _stuck("obligation", f"Accepted, with {n} {word}",
                  [f"{o['key']}: {o['reason']}" for o in new]
                  + ["A fact the kernel can use, or a narrower range, would "
                     "discharge it; the proof will read Proved modulo "
                     f"{n} {word} until then."])


# ---------------------------------------------------------------- algebra

def _fact_pairs(r):
    """Candidate identity facts for residual r, as (entry, inst term,
    (lhs, rhs)) with the entry's statement instantiated."""
    out, seen = [], set()
    for t in subterms(r):
        if not isinstance(t, App):
            continue
        if t.fn == "sqrt":
            name, var, arg = "sqrt_sq_val", "a", t.arg
        elif t.fn in ("sin", "cos"):
            name, var, arg = "pyth_cos", "u", t.arg
        else:
            continue
        if (name, arg) in seen:
            continue
        seen.add((name, arg))
        st = ENTRIES[name].statement
        out.append((name, var, arg,
                    (subst(st.lhs, {var: arg}), subst(st.rhs, {var: arg}))))
    return out


def _closes(r, facts):
    try:
        FD.field(r, Num(0), [f[3] for f in facts])
        return True
    except Exception:
        return False


def _fresh(handles):
    for k in range(100):
        h = "h" if k == 0 else f"h{k}"
        if h not in handles:
            return h
    return None


def _identity(r, move, args, handles, trial, show_move):
    cands = _fact_pairs(r)
    sets = [[c] for c in cands]
    if len(cands) > 1:
        sets.append(cands)
    for fs in sets:
        if not _closes(r, fs):
            continue
        names, facts, sentences, taken = [], [], [], set(handles)
        for name, var, arg, _ in fs:
            h = _fresh(taken)
            taken.add(h)
            names.append(h)
            sentences.append(f"fact {h} := {name} with {var} := {show(arg)}.")
        again = dict(args, check="field",
                     facts=list(args.get("facts") or [])
                     + [["handle", h] for h in names])
        sentences.append(show_move(move, again))
        if _accepted(trial, sentences):
            ids = ", ".join(sorted({f[0] for f in fs}))
            return ([f"The difference is zero by the identity {ids}: the "
                     "answer is right, written another way (§8.7).",
                     "Bind it as a fact and check by field using it."],
                    sentences)
    return None


def _spell(c, F):
    """c·F for a rational c, in the simplest spelling."""
    if c.denominator == 1:
        return f"{c.numerator}*({F})"
    if c.numerator == 1:
        return f"({F})/{c.denominator}"
    return f"{c.numerator}*({F})/{c.denominator}"


def _samples(i):
    """Three points at a quarter, a half and three quarters of i's range,
    as floats, or None."""
    if isinstance(i.lo, (NegInf, PosInf)) or isinstance(i.hi,
                                                        (NegInf, PosInf)):
        return None
    try:
        a = probe._ev(i.lo, {}, probe._Budget())
        b = probe._ev(i.hi, {}, probe._Budget())
    except Exception:
        return None
    return [a + (b - a) * k / 4 for k in (1, 2, 3)]


def _at(t, x, v):
    try:
        out = probe._ev(t, {x: v}, probe._Budget())
    except Exception:
        return None
    return out if math.isfinite(out) else None


def _factor(r, f, x, pts):
    """λ with r = λ·f exactly (field), found by sampling r/f, or None."""
    ratios = []
    for v in pts:
        a, b = _at(r, x, v), _at(f, x, v)
        if a is None or b is None or b == 0:
            return None
        ratios.append(a / b)
    if max(ratios) - min(ratios) > 1e-9 * max(1.0, abs(ratios[0])):
        return None
    lam = Fraction(ratios[0]).limit_denominator(1000)
    try:
        FD.field(r, Mul(lit(lam), f))
    except Exception:
        return None
    return lam


def algebra(code, message, residual, goal, move, args, handles, trial,
            show_move):
    r = residual
    if code == "divisor-normalises-to-zero":
        return _stuck("algebra", "A divisor in the step is zero",
                      [message, "Something is divided by an expression that "
                       "simplifies to 0: rewrite that quotient."])
    if r is None:
        return _stuck("algebra", "The algebra does not close", [message])
    rs = show(r)
    i = _first_int(goal, args) if move in ("ftc", "int_improper") else None
    if move in ("ftc", "int_improper"):
        head = f"D[{i.var}] F − integrand = {rs}" if i else \
            f"F′ − integrand = {rs}"
    elif move == "close":
        head = f"The goal's side − your value = {rs}"
    elif code == "int-subst-endpoint-mismatch":
        head = f"A new limit does not map to the old one: they differ by {rs}"
    else:
        head = f"The two sides differ by {rs}"
    found = _identity(r, move, args, handles, trial, show_move)
    if found:
        return _stuck("algebra", head, found[0], found[1])
    if i is not None:
        x, f = i.var, i.body
        pts = _samples(i)
        lam = _factor(r, f, x, pts) if pts else None
        if lam is not None and lam != -1:
            c = 1 / (1 + lam)
            new = _spell(c, args["F"])
            sentence = show_move(move, dict(args, F=new))
            ok = _accepted(trial, [sentence])
            return _stuck("algebra", head,
                          [f"Your F′ is {1 + lam} times the integrand."
                           + (f" Scale F by {c}." if ok else "")],
                          [sentence] if ok else None)
        if x not in fv(r) and not _is_zero(r):
            return _stuck("algebra", head,
                          [f"F′ − integrand is the constant {rs}: F has an "
                           f"extra {_times(rs, x)}."])
        if pts:
            vals = [(v, _at(r, x, v)) for v in pts]
            vals = [(v, w) for v, w in vals if w is not None]
            if vals:
                return _stuck("algebra", head, [
                    "Where they diverge: " + "; ".join(
                        f"at {x} {_num(v)}, F′ − integrand {_num(w)}"
                        for v, w in vals) + "."])
        return _stuck("algebra", head, [])
    if move == "close" and not fv(r):
        try:
            side = probe.value(goal)
            val = probe._ev(parse_term(args["value"], {}), {},
                            probe._Budget())
            return _stuck("algebra", head, [
                f"The goal's side is {_num(side)}; your value is "
                f"{_num(val)}."])
        except Exception:
            pass
    if not fv(r):
        v = _at(r, "_", 0.0)
        if v is not None:
            return _stuck("algebra", head, [f"The difference is {_num(v)}."])
    return _stuck("algebra", head, [])


def _times(c, x):
    return f"{c}*{x}" if c.replace("/", "").isdigit() else f"({c})*{x}"


def _is_zero(r):
    try:
        FD.field(r, Num(0))
        return True
    except Exception:
        return False


# ---------------------------------------------------------------- dispatch

def explain(code, message, residual, goal, move, args, sig=None,
            handles=(), trial=None, show_move=None):
    """The stuck object for one refusal. `goal` is the goal the move was
    tried on (a tuple) or None; `move` and `args` the script-shaped move,
    or None when the sentence did not parse; `trial(sentences)` runs the
    kernel from the same node and says whether it accepts them all;
    `show_move(move, args)` prints a sentence (script.show)."""
    trial = trial or (lambda s: False)
    args = args or {}
    if code in NO_MATCH:
        return no_match(code, message, goal, move, args, sig or {}, trial)
    if code in OBLIGATION:
        return obligation(code, message, move)
    if code in ALGEBRA and move is not None:
        return algebra(code, message, residual, goal, move, args,
                       set(handles), trial, show_move)
    return _stuck("other", f"Refused: {code}")

