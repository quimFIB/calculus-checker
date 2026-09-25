"""The palette and the antiderivative card (DESIGN.md §8.5; app/UI.md §2).

Untrusted (tier 2). The palette says what is even legal-looking here: the
moves whose shape fits the goal, and each ENTRIES equation whose left side
matches a subterm syntactically, with a ready tactic sentence. It never
runs a move; side conditions are the kernel's. The card is the
inside-cover table, with the forms the recognizer sees in the integrand
marked.
"""

from assist import recognizer as R
from assist.shapes import subterms, summands
from entries import ENTRIES
import field as FD
from assist import factor as FA
from assist import probe
from terms import (App, Deriv, Integral, MVar, NegInf, PosInf, Rel, Term,
                   Var, show, subst)
from dataclasses import fields


def sides(goal):
    """The sides of the goal's first equation that moves act on: never ?A."""
    if not goal:
        return ()
    g = goal[0]
    if not hasattr(g, "lhs"):
        return ()
    return (g.lhs,) if isinstance(g.rhs, MVar) else (g.lhs, g.rhs)


def integrals(goal):
    return [t for s in sides(goal) for t in subterms(s)
            if isinstance(t, Integral)]


# ---------------------------------------------------------------- matching

def match(pat, t, schema, inst):
    """First-order syntactic match of pat against t, binding schema
    variables in inst (a dict, extended in place). True or False."""
    if isinstance(pat, Var) and pat.name in schema:
        if pat.name in inst:
            return inst[pat.name] == t
        inst[pat.name] = t
        return True
    if type(pat) is not type(t):
        return False
    if not isinstance(pat, Term):
        return pat == t
    for f in fields(pat):
        a, b = getattr(pat, f.name), getattr(t, f.name)
        if isinstance(a, Term):
            if not match(a, b, schema, inst):
                return False
        elif isinstance(a, tuple):
            if len(a) != len(b) or not all(
                    match(x, y, schema, inst) for x, y in zip(a, b)):
                return False
        elif a != b:
            return False
    return True


def _ring_equal(a, b):
    try:
        return FD.ring_equal(a, b)
    except Exception:
        return False


def entry_matches(e, t):
    """The instantiation under which entry e's left side is t, or None.

    Syntactic first. An App left side then matches as the kernel's rewrite
    reads it, by function name and its argument up to ring: with no schema
    variable that is ring_equal alone (sin(2*(pi/2)) is sin pi); with one,
    each subterm of t's argument is tried as its value (sqrt(1 - (1 - t^2))
    is sqrt(u^2) with u := t). Entries with two schema variables match
    syntactically only, so the palette under-approximates."""
    lhs = e.statement.lhs
    inst = {}
    if match(lhs, t, set(e.schema), inst) and set(inst) == set(e.schema):
        return inst
    if not (isinstance(lhs, App) and isinstance(t, App) and lhs.fn == t.fn):
        return None
    if not e.schema:
        return {} if _ring_equal(lhs.arg, t.arg) else None
    if len(e.schema) == 1:
        (v,) = e.schema
        seen = set()
        for c in subterms(t.arg):
            if c in seen:
                continue
            seen.add(c)
            if _ring_equal(subst(lhs.arg, {v: c}), t.arg):
                return {v: c}
    return None


def rewrites(goal):
    out, seen = [], set()
    for s in sides(goal):
        for t in subterms(s):
            for name, e in ENTRIES.items():
                if e.statement.op != "==":
                    continue
                inst = entry_matches(e, t)
                if inst is None or (name, t) in seen:
                    continue
                seen.add((name, t))
                w = ("" if not inst else " with " + "; ".join(
                    f"{k} := {show(v)}" for k, v in inst.items()))
                out.append({"entry": name, "at": show(t),
                            "sentence": f"rewrite {name}{w} at {show(t)}."})
    return out


# ---------------------------------------------------------------- moves

def _finite(i):
    return not any(isinstance(e, (PosInf, NegInf)) for e in (i.lo, i.hi))


def _float(t):
    try:
        return probe.value(((Rel("==", t, MVar("A"))),))
    except Exception:
        return None


def moves(goal):
    """The moves whose shape fits. ftc, int_subst and int_parts refuse an
    infinite end, so they are offered for a finite-ended Int only."""
    ints = integrals(goal)
    finite = [i for i in ints if _finite(i)]
    out = []
    if finite:
        x = finite[0].var
        out += [
            {"move": "ftc", "sentence": "ftc _.",
             "why": "an integral: give an antiderivative F"},
            {"move": "int_subst",
             "sentence": f"int_subst {x} := _ as _ from _ to _.",
             "why": "an integral: change its variable"},
            {"move": "int_parts",
             "sentence": f"int_parts in {x} with u := _; v := _.",
             "why": "an integral of a product"}]
    if ints:
        if any(not _finite(i) for i in ints):
            out.append({"move": "int_improper", "sentence": "int_improper _.",
                        "why": "an integral with an infinite end"})
        for i in finite:
            lo, hi = _float(i.lo), _float(i.hi)
            if lo is not None and hi is not None and lo > hi:
                out.append({"move": "int_flip", "sentence": "int_flip.",
                            "why": "an integral whose limits are reversed"})
                break
    g = goal[0] if goal else None
    if (g is not None and isinstance(getattr(g, "rhs", None), MVar)
            and not any(isinstance(t, (Integral, Deriv))
                        for t in subterms(g.lhs))):
        out.append({"move": "close", "sentence": "close _.",
                    "why": "no integral or derivative left: name the value"})
    if g is not None and getattr(g, "op", "==") != "==":  # p1_expected E96
        out += [
            {"move": "taylor_lagrange",
             "sentence": "taylor_lagrange _ := lower of _ in u from _ to _ "
                         "at _ derivs _; _ increasing by field.",
             "why": "an inequality: bound a Taylor remainder by its "
                    "monotone last derivative"},
            {"move": "bound", "sentence": "bound by field using _.",
             "why": "an inequality: close it from a bound you hold"}]
    out.append({"move": "fact", "sentence": "fact _ := _.",
                "why": "bind an entry as a fact for by field"})
    return out


# ---------------------------------------------------------------- the card

CARD = [
    ("constant", r"k", r"k\,x", ("constant",)),
    ("power", r"x^{n},\ n \neq -1", r"\frac{x^{n+1}}{n+1}",
     ("polynomial: the power rule", "x^p: the power rule",
      "c/(linear)^k: the power rule")),
    ("reciprocal", r"\frac{1}{x}", r"\ln\left|x\right|", ()),
    ("exp", r"\mathrm{e}^{a x}", r"\frac{\mathrm{e}^{a x}}{a}",
     ("exp of a linear argument",)),
    ("sin", r"\sin a x", r"-\frac{\cos a x}{a}",
     ("sin of a linear argument",)),
    ("cos", r"\cos a x", r"\frac{\sin a x}{a}", ("cos of a linear argument",)),
    ("sinh", r"\sinh a x", r"\frac{\cosh a x}{a}",
     ("sinh of a linear argument",)),
    ("cosh", r"\cosh a x", r"\frac{\sinh a x}{a}",
     ("cosh of a linear argument",)),
    ("tan", r"\tan x", r"-\ln\left|\cos x\right|", ()),
    ("tanh", r"\tanh x", r"\ln \cosh x", ()),
    ("sec2", r"\frac{1}{\cos^{2} x}", r"\tan x", ()),
    ("ln", r"\ln x", r"x \ln x - x", ()),
    ("arctan", r"\frac{1}{x^{2} + a^{2}}",
     r"\frac{1}{a}\arctan\frac{x}{a}", ("1/(x² + a²): arctan",)),
    ("artanh", r"\frac{1}{a^{2} - x^{2}}",
     r"\frac{1}{a}\operatorname{artanh}\frac{x}{a}",
     ("1/(a² − x²): artanh",)),
    ("arcsin", r"\frac{1}{\sqrt{a^{2} - x^{2}}}", r"\arcsin\frac{x}{a}",
     ("1/√(a² − x²): arcsin",)),
    ("arsinh", r"\frac{1}{\sqrt{x^{2} + a^{2}}}",
     r"\operatorname{arsinh}\frac{x}{a}", ()),
    ("arcosh", r"\frac{1}{\sqrt{x^{2} - a^{2}}}",
     r"\operatorname{arcosh}\frac{x}{a}", ()),
    ("logderiv", r"\frac{f'(x)}{f(x)}", r"\ln\left|f(x)\right|", ()),
    ("apow", r"a^{x}", r"\frac{a^{x}}{\ln a}", ()),
]


def card(goal):
    """The card rows, each marked when the first integral's integrand has
    a summand of that form (recognizer.card_form)."""
    ints = integrals(goal)
    found = set()
    if ints:
        i = ints[0]
        for u in summands(i.body):
            try:
                f = R.card_form(u, i.var)
            except Exception:
                f = None
            if f:
                found.add(f)
    return [{"id": cid, "form": form, "antiderivative": anti,
             "matches": bool(found & set(keys))}
            for cid, form, anti, keys in CARD]


def rational(goal):
    """FACTOR.md: the first Int's integrand and variable when it is a
    rational function of that variable, for the factor tools; else None."""
    ints = integrals(goal)
    if not ints:
        return None
    i = ints[0]
    try:
        _, q = FA.read(i.body, i.var)
    except Exception:
        return None
    if FA.deg(q) < 1:  # a polynomial: nothing to split
        return None
    return {"term": show(i.body), "var": i.var}


def palette(goal):
    return {"moves": moves(goal), "rewrites": rewrites(goal),
            "card": card(goal), "rational": rational(goal)}
