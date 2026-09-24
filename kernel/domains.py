"""The natural-domain table: one datum for definedness and regularity.

Trusted (DESIGN.md §15.2 items 2 and 5; p1_expected E26 (a), E61). Each
partial builtin's natural domain, the set on which §6.9 makes it C^0, as
the propositions its former owes: fn -> u -> props. The kernel's formers
(`kernel._owed`) read it, and so does the regularity checker
(`discharge._reg_sides`), whose C^0 sides for a builtin ARE its row, and
whose C^1 sides are the same row's interior (`interior`) plus C1_EXTRA. The
search and the tagger read it as untrusted code reads trusted data. §6.9:
'the C^0 sets above are exactly the domains §5.1's partial formers owe'.

One linear item per bound, written `u REL c` (the orientation of §6.3's
d_ln and d_sqrt, GRAMMAR.md D12), so a two-sided domain is two keys and
Fourier–Motzkin reads each bound directly (TAG_RULES range, linear). Not
abs u <= 1: abs u is an opaque atom to every §5.3 method. Closed where the
builtin is defined at the end (sqrt at 0, asin and acos at ±1, acosh at 1),
open where it is not (ln at 0, atanh at ±1, tan where cos u = 0), which is
also REWRITE_RULE 9(a)'s split into open and closed domains. sin, cos,
atan, exp, abs, sinh, cosh, tanh and asinh are total: no row.

**A seam** (kernel/ARCHITECTURE.md §7): every reader looks NATURAL_DOMAINS
(and C1_EXTRA) up by this module's global name at call time, so the
definedness mutations, which swap the whole mapping in a child process,
reach the formers and the checker alike (REG_SWITCH: 'both see one
object'). Both are read-only, like deriv.APP_RULES, because a missing or
wrong row is a false 'Proved.'.
"""

from types import MappingProxyType

from terms import App, NonZero, Num, Rel, lit

NATURAL_DOMAINS = MappingProxyType({
    "ln": lambda u: (Rel(">", u, Num(0)),),
    "sqrt": lambda u: (Rel(">=", u, Num(0)),),
    "tan": lambda u: (NonZero(App("cos", u)),),
    "asin": lambda u: (Rel(">=", u, lit(-1)), Rel("<=", u, Num(1))),
    "acos": lambda u: (Rel(">=", u, lit(-1)), Rel("<=", u, Num(1))),
    "acosh": lambda u: (Rel(">=", u, Num(1)),),
    "atanh": lambda u: (Rel(">", u, lit(-1)), Rel("<", u, Num(1))),
})

# E61's REG_C1_EXTRA: the one datum regularity adds to the table. abs is C^0
# everywhere and C^1 where its argument is nonzero.
C1_EXTRA = MappingProxyType({
    "abs": lambda u: (NonZero(u),),
})

_STRICT = {">=": ">", "<=": "<"}


def interior(props):
    """A natural-domain row made open: every >= made > and every <= made <
    (E61); a strict item or a # 0 item is its own interior."""
    return tuple(Rel(_STRICT[p.op], p.lhs, p.rhs, p.dom)
                 if isinstance(p, Rel) and p.op in _STRICT else p for p in props)
