"""The proposer (app/EVAL.md): SymPy, shelled out to, run by a Python that
has it. One JSON object on stdin, one on stdout.

    in:  {"integral": "Int[x = a .. b] f", "functions": {...},
          "positive": ["a", ...]}
    out: {"status": "ok" | "outside-grammar" | "not-found" |
                    "has-parameters" | "error",
          "shapes": [F, ...], "value": V | null, "value_note": str | null,
          "function": name | null, "message": str}

Untrusted: whatever it prints is parsed by the kernel like typed text and
checked by the kernel before anything is shown as a value. The integral is
read by the kernel's own parser (review 9), never by sympify.
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "kernel"))

import sympy as sp  # noqa: E402
import terms as T  # noqa: E402

FUNCS = {"sin": sp.sin, "cos": sp.cos, "tan": sp.tan, "asin": sp.asin,
         "acos": sp.acos, "atan": sp.atan, "exp": sp.exp, "ln": sp.log,
         "sqrt": sp.sqrt, "abs": sp.Abs, "sinh": sp.sinh, "cosh": sp.cosh,
         "tanh": sp.tanh, "asinh": sp.asinh, "acosh": sp.acosh,
         "atanh": sp.atanh}
NAMES = {sp.sin: "sin", sp.cos: "cos", sp.tan: "tan", sp.asin: "asin",
         sp.acos: "acos", sp.atan: "atan", sp.exp: "exp", sp.log: "ln",
         sp.Abs: "abs", sp.sinh: "sinh", sp.cosh: "cosh", sp.tanh: "tanh",
         sp.asinh: "asinh", sp.acosh: "acosh", sp.atanh: "atanh"}


class Outside(Exception):
    """A SymPy node the grammar has no word for; args[0] names it."""


class Params(Exception):
    pass


# ---------------------------------------------------------------- in

def to_sympy(t, syms):
    if isinstance(t, T.Num):
        return sp.Integer(t.n)
    if isinstance(t, T.Const):
        return sp.pi if t.name == "pi" else sp.E
    if isinstance(t, T.Var):
        if t.name not in syms:
            raise Params(t.name)
        return syms[t.name]
    if isinstance(t, T.Neg):
        return -to_sympy(t.a, syms)
    if isinstance(t, T.Add):
        return to_sympy(t.a, syms) + to_sympy(t.b, syms)
    if isinstance(t, T.Mul):
        return to_sympy(t.a, syms) * to_sympy(t.b, syms)
    if isinstance(t, T.Div):
        return to_sympy(t.a, syms) / to_sympy(t.b, syms)
    if isinstance(t, T.Pow):
        return to_sympy(t.base, syms) ** t.n
    if isinstance(t, T.RPow):
        return to_sympy(t.base, syms) ** to_sympy(t.exp, syms)
    if isinstance(t, T.App):
        return FUNCS[t.fn](to_sympy(t.arg, syms))
    if isinstance(t, T.Call):
        raise Outside(t.fn)  # a declared function: unknown to SymPy
    raise Outside(type(t).__name__)


def end(e, syms):
    if isinstance(e, T.PosInf):
        return sp.oo
    if isinstance(e, T.NegInf):
        return -sp.oo
    return to_sympy(e, syms)


# ---------------------------------------------------------------- out

def show(e, rad=False):
    """GRAMMAR text, over-parenthesised; the caller re-shows it through
    the kernel's printer, which drops what is not needed. With rad, c*sqrt n
    for rational c prints as (c*n)/sqrt n: sqrt(3)/3 -> 1/sqrt 3, the form
    the §6.8 table (atan_one_sqrt3) is written in (review 3)."""
    s = lambda u: show(u, rad)  # noqa: E731
    if e.has(sp.I) or e.has(sp.nan) or e.has(sp.zoo):
        raise Outside("complex")
    if isinstance(e, sp.Piecewise):
        raise Outside("Piecewise")
    if isinstance(e, sp.Integer):
        return str(e) if e >= 0 else f"(-{-e})"
    if isinstance(e, sp.Rational):
        p, q = e.p, e.q
        return f"({p}/{q})" if p >= 0 else f"(-({-p}/{q}))"
    if e is sp.pi:
        return "pi"
    if e is sp.E:
        return "e_const"
    if e in (sp.oo, -sp.oo):
        raise Outside("oo")
    if isinstance(e, sp.Symbol):
        return e.name
    if isinstance(e, sp.Add):
        terms = list(e.as_ordered_terms())
        out = s(terms[0])
        for t in terms[1:]:
            c, _ = t.as_coeff_Mul()
            out += (" - " + s(-t)) if c < 0 else (" + " + s(t))
        return f"({out})"
    if isinstance(e, sp.Mul):
        c, rest = e.as_coeff_Mul()
        if c < 0:
            return f"(-{s(-e)})"
        if rad and c.is_Rational:
            for f in sp.Mul.make_args(rest):
                if (isinstance(f, sp.Pow) and f.exp == sp.Rational(1, 2)
                        and f.base.is_Integer):
                    others = sp.Mul(*[g for g in sp.Mul.make_args(rest)
                                      if g is not f])
                    return f"(({s(c * f.base * others)})/sqrt({f.base}))"
        n, d = sp.fraction(e)
        if d != 1:
            return f"({s(n)})/({s(d)})"
        return "(" + "*".join(s(f) for f in e.as_ordered_factors()) + ")"
    if isinstance(e, sp.Pow):
        b, x = e.args
        if x == sp.Rational(1, 2):
            return f"sqrt({s(b)})"
        if x == -sp.Rational(1, 2):
            return f"(1/sqrt({s(b)}))"
        if x.is_Integer:
            if x < 0:
                return f"(1/({s(b)})^{-x})" if x != -1 else f"(1/{s(b)})"
            return f"({s(b)})^{x}"
        return f"({s(b)})^({s(x)})"
    if isinstance(e, sp.exp):
        return f"exp({s(e.args[0])})"
    if e.func in NAMES:
        return f"{NAMES[e.func]}({s(e.args[0])})"
    raise Outside(e.func.__name__)


# ---------------------------------------------------------------- shapes

def pull_args(e, x):
    """Each atan, ln or atanh of a linear argument gets it factored:
    (2*sqrt 3*x - sqrt 3)/3 -> sqrt 3*(2*x - 1)/3, printed (2*x - 1)/sqrt 3."""
    def fix(f):
        a = f.args[0]
        if a.is_polynomial(x) and sp.degree(a, x) == 1:
            return f.func(sp.factor(a), evaluate=False)
        return f
    return e.replace(lambda f: isinstance(f, (sp.atan, sp.log, sp.atanh)),
                     fix)


def combine_logs(e):
    """c*ln A - c*ln B -> c*ln(A/B): one log, so an improper limit meets
    one quotient, not oo - oo (review 3)."""
    groups, rest = {}, []
    for t in sp.Add.make_args(e):
        c, f = t.as_independent(sp.log, as_Add=False)
        if isinstance(f, sp.log):
            k = sp.Abs(c)
            groups.setdefault(k, [[], []])[0 if c > 0 else 1].append(f.args[0])
        else:
            rest.append(t)
    out = list(rest)
    for k, (pos, neg) in groups.items():
        out.append(k * sp.log(sp.Mul(*pos) / sp.Mul(*neg), evaluate=False))
    return sp.Add(*out, evaluate=False)


def negate_logs(e):
    return e.replace(lambda f: isinstance(f, sp.log),
                     lambda f: sp.log(sp.expand(-f.args[0])))


def shapes(F, x):
    g = pull_args(F, x)
    cands = [(F, False), (g, True), (combine_logs(g), True),
             (negate_logs(F), False)]
    out, seen = [], set()
    for c, rad in cands:
        try:
            s = show(c, rad)
        except Exception:
            continue
        if s not in seen:
            seen.add(s)
            out.append(s)
    return out


# ---------------------------------------------------------------- main

def propose(req):
    sig = req.get("functions") or {}
    t = T.parse_term(req["integral"], sig)
    if not isinstance(t, T.Integral):
        return {"status": "error", "message": "not an integral"}
    x = sp.Symbol(t.var, real=True)
    syms = {t.var: x}
    for p in req.get("positive") or []:
        syms[p] = sp.Symbol(p, positive=True)
    try:
        f = to_sympy(t.body, syms)
        lo, hi = end(t.lo, syms), end(t.hi, syms)
    except Params as e:
        return {"status": "has-parameters", "function": None,
                "message": f"{e.args[0]} is a parameter with no domain fact "
                           "saying it is positive"}
    except Outside as e:
        return {"status": "not-found", "function": e.args[0],
                "message": f"{e.args[0]} is a declared function: nothing is "
                           "known about it"}
    F = sp.integrate(f, x)
    V = sp.integrate(f, (x, lo, hi))
    out = {"status": "ok", "shapes": [], "value": None, "value_note": None,
           "function": None, "message": ""}
    if not isinstance(V, sp.Integral):
        V = sp.simplify(V)
        if V.has(sp.oo, -sp.oo, sp.zoo, sp.nan):
            out["value_note"] = "SymPy says it diverges"
        elif V.has(sp.I):
            out["value_note"] = "SymPy's value is complex"
        else:
            try:
                out["value"] = show(V)
            except Outside as e:
                out["function"] = e.args[0]
    if F.has(sp.Integral) or isinstance(F, sp.Integral):
        out["status"] = "not-found" if out["value"] is None else "ok"
        out["message"] = "not found; one may well exist"
        return out
    out["shapes"] = shapes(F, x)
    if lo.is_finite and hi.is_finite:  # F(b) - F(a), each side simplified:
        try:                          # ln(1 + a) - ln a, not ln((a + 1)/a)
            out["values"] = [show(sp.Add(sp.simplify(F.subs(x, hi)),
                                         -sp.simplify(F.subs(x, lo)),
                                         evaluate=False))]
        except Outside:
            pass
    if not out["shapes"]:
        try:
            show(F)
        except Outside as e:
            out["function"] = e.args[0]
        out["status"] = "outside-grammar"
        name = out["function"]
        if name == "Piecewise":
            out["message"] = "SymPy gives no single antiderivative on this range"
        elif name == "RootSum":
            out["message"] = ("SymPy writes this with the roots of a "
                              "polynomial, which have no closed form here")
        else:
            out["message"] = (f"SymPy writes this with {name}, which this "
                              "grammar does not have")
    return out


def main():
    req = json.loads(sys.stdin.read())
    try:
        out = propose(req)
    except Exception as e:  # report, never crash the caller
        out = {"status": "error", "message": f"{type(e).__name__}: {e}"}
    sys.stdout.write(json.dumps(out))


if __name__ == "__main__":
    main()
