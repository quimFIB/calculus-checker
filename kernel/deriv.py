"""`deriv`: §6.3's entries applied to a term, collecting side conditions.

Trusted in this milestone (DESIGN.md §15.2 item 2). §6.3 makes deriv an
untrusted tactic that emits one kernel step per entry. Here `ftc` takes its
output as the derivative, so the output forms and side conditions below are
the rule table itself. A missing side condition is a false theorem. The
planted bug `d_ln_emits_nothing` is that case, and it is patched in through
`APP_RULES` (kernel/ARCHITECTURE.md §7).

The walk is top-down and applies each entry's output form literally, with
no tidying of 0*u or u*1 (p1_expected E12). At each subterm t, in order:

  d_const     x is not free in t (terms.fv, so a Deriv on x counts as free):
              output Num 0, whatever t's former is (rev 7). Except that a t
              holding an Integral or Deriv node anywhere is refused
              'Int-or-D-not-normalisable' (p1_expected E12, E26 (b)): 0
              would read it as a constant whose existence nothing can state
              (Int[t = 0 .. oo] 1 - Int[t = 0 .. oo] 1 is undefined, not
              constant). The test is inside this branch, so a Deriv or
              Integral with x free still falls through to 'deriv-no-rule'.
  d_var       t is Var x: output Num 1
  d_add       Add(u, v): Add(D u, D v)
  route_neg   Neg(u): walk Mul(lit(-1), u) instead (-u ≐ (-1)*u by ring)
  d_mul       Mul(u, v): Add(Mul(D u, v), Mul(u, D v))
  d_inv       Div(Num 1, v): Div(Neg(D v), Pow(v, 2)), side v # 0
  route_div   Div(u, v), u not Num 1: walk Mul(u, Div(Num 1, v)) instead.
              It emits v # 0 (u/v ≐ u*(1/v) by field)
  d_pow_int   Pow(u, n), n != 0: Mul(Mul(lit(n), Pow(u, n - 1)), D u),
              with n - 1 folded to a literal; side u # 0 when n < 0
  APP_RULES   App(fn, u) with fn in APP_RULES: the rule's output and sides
  otherwise   Refused 'deriv-no-rule'. That covers a Deriv or Integral
              with x free (D10), a Call (d_chain waits for declared
              symbols), an RPow (d_pow_real is not in this milestone), Pow
              with n == 0, and an App whose builtin has no rule yet.

Every `v # 0` a firing owes is a divisor of one of F's own '/' or
negative-power formers, which ftc has already charged and E25-tested
(kernel._charge_formers). kernel._emit tests each emitted NonZero again, so
deriv does no E25 test of its own.

The routes are recorded in the trace under their own names, and so are the
rules they reach. So `-(2*t*cos t)` gives ("route_neg", that term) and then
("d_mul", `-1*(2*t*cos t)`), as p1_expected's DERIV lists them.
"""

from dataclasses import dataclass
from types import MappingProxyType

from terms import (Add, App, Div, Mul, Neg, NonZero, Num, Pow, Refused, Rel,
                   Var, fv, lit, show, trees, with_domain)


@dataclass(frozen=True, slots=True)
class TraceEntry:
    rule: str  # "d_mul", "route_div", ...
    subterm: object  # the Term the rule fired on
    emits: tuple  # the keys this firing emitted, already on the domain


@dataclass(frozen=True, slots=True)
class Derived:
    output: object  # deriv(F), exactly as the output forms build it
    trace: tuple  # TraceEntry, in walk order
    emissions: tuple  # ((key, source), ...), deduplicated, first-seen order.
    # The source is the rule name: "d_ln", "d_sqrt", "route_div", "d_inv", ...


# §6.3's App entries, each (u, du) -> (output form, side props with dom ()).
def _d_sin(u, du):
    return Mul(App("cos", u), du), ()


def _d_cos(u, du):
    return Mul(Neg(App("sin", u)), du), ()


def _d_exp(u, du):
    return Mul(App("exp", u), du), ()


def _d_sqrt(u, du):
    return Div(du, Mul(Num(2), App("sqrt", u))), (Rel(">", u, Num(0)),)


def _d_ln(u, du):
    return Div(du, u), (Rel(">", u, Num(0)),)


def _d_atan(u, du):
    # No side condition in §6.3: field charges the denominator 1 + u^2.
    return Div(du, Add(Num(1), Pow(u, 2))), ()


# fn -> rule(u, du) -> (output Term, side-condition props with dom == ()).
# The rule for fn is named "d_" + fn in the trace and as the emission source.
# A seam: the walk must look rules up here at call time, never through a
# copy taken at import (kernel/ARCHITECTURE.md §7). Other §6.3 entries are
# added here, one line each, when a problem needs them. It is read-only, as
# ENTRIES is: a write from outside would extend the trusted rule table
# (§15.2 item 2), and a wrong rule is a false theorem whose admissions are
# all true. The d_ln_emits_nothing child swaps the whole mapping with
# patch.object instead.
APP_RULES = MappingProxyType({
    "sin": _d_sin,
    "cos": _d_cos,
    "exp": _d_exp,
    "sqrt": _d_sqrt,
    "ln": _d_ln,
    "atan": _d_atan,
})


def const_guard(t):
    """E12's d_const guard (E26 (b)): refuse an x-free t that holds an
    Integral or Deriv node, rather than give it derivative 0. Returns
    nothing when t holds none.

    A seam (kernel/ARCHITECTURE.md §7): the walk calls it by this global
    name, and the mutation deriv_d_const_on_Int_or_D replaces it in a child
    process. Keep the name and signature."""
    for node in trees(t):
        raise Refused("Int-or-D-not-normalisable",
                      f"d_const would read {show(node)} as a constant, and "
                      "nothing can state that it exists (E26 (b))")


def deriv(F, x, dom):
    """D[x] F by the walk above. Every side condition is placed on `dom`
    with terms.with_domain, so E5 applies, and the kernel emits them as they
    come back.

    `dom` is the domain tuple the derivative premise holds on: G + (a, b) in
    ftc. Returns Derived. Raises Refused 'deriv-no-rule', or
    'Int-or-D-not-normalisable' from const_guard.
    """
    trace = []

    def fire(rule, t, props=(), slot=None):
        # Record one firing, its sides already on dom. `slot` is the trace
        # position an App reserved before walking its argument, so the trace
        # stays in top-down order though the rule runs after D u is known.
        entry = TraceEntry(rule, t, tuple(with_domain(p, dom) for p in props))
        if slot is None:
            trace.append(entry)
        else:
            trace[slot] = entry

    def walk(t):
        if x not in fv(t):
            const_guard(t)
            fire("d_const", t)
            return Num(0)
        if t == Var(x):
            fire("d_var", t)
            return Num(1)
        if isinstance(t, Add):
            fire("d_add", t)
            return Add(walk(t.a), walk(t.b))
        if isinstance(t, Neg):
            fire("route_neg", t)
            return walk(Mul(lit(-1), t.a))
        if isinstance(t, Mul):
            fire("d_mul", t)
            du = walk(t.a)
            return Add(Mul(du, t.b), Mul(t.a, walk(t.b)))
        if isinstance(t, Div) and t.a == Num(1):
            fire("d_inv", t, (NonZero(t.b),))
            return Div(Neg(walk(t.b)), Pow(t.b, 2))
        if isinstance(t, Div):
            fire("route_div", t, (NonZero(t.b),))
            return walk(Mul(t.a, Div(Num(1), t.b)))
        if isinstance(t, Pow) and t.n != 0:
            fire("d_pow_int", t, (NonZero(t.base),) if t.n < 0 else ())
            return Mul(Mul(lit(t.n), Pow(t.base, t.n - 1)), walk(t.base))
        rule = APP_RULES.get(t.fn) if isinstance(t, App) else None
        if rule is not None:
            slot = len(trace)
            trace.append(None)
            out, props = rule(t.arg, walk(t.arg))
            fire("d_" + t.fn, t, props, slot)
            return out
        raise Refused("deriv-no-rule",
                      f"no §6.3 rule differentiates {show(t)} in {x}")

    output = walk(F)
    seen = {}
    for e in trace:
        for key in e.emits:
            seen.setdefault((key, e.rule), None)
    return Derived(output, tuple(trace), tuple(seen))
