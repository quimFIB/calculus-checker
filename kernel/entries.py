"""The §6.8 entries this milestone uses, pinned by exact statement.

Trusted (DESIGN.md §15.2 item 7, the cite library). Each statement is a
judgement in GRAMMAR.md syntax, as GRAMMAR.md §9 pins it. `schema` lists the
ordinary variables an instantiation must bind, exactly. A sequent entry is
written with `@` (GRAMMAR.md D14), so an entry's hypotheses are its
statement's domain items. The statements are the kernel's own, parsed from
the strings below at import. p1_expected.py's NAMED_ENTRIES is the check on
them, never their source.

The last four are stage 0's (kernel/problems/stage0/, WHAT.md "Start
here"): S3 needs `ln_e` and the sign fact `e_gt_one`, and S2, whose answer
is stated with e_const, needs `exp_zero` and `exp_one`. §6.8 states only
e_gt_one. ln_e is as GRAMMAR.md §9 pins it, and exp_zero and exp_one are
the only statements §6.8's row "exp 0, 1" can mean. P1 uses none of them.
`e_gt_one` is not an equation, so rewrite refuses it; it is here as the
cite that tagger.SIGN_FACTS names for e_const, as pi_pos is for pi.

Two more are the owner's (p1_expected E35 (3), DISCHARGE_NEW_ENTRIES):
`sqrt_zero : sqrt 0 == 0`, placed immediately before sqrt_sq so that E27
(a), which names the first entry that counts at a subterm, names the direct
move at sqrt 0, and `cos_zero : cos 0 == 1`, appended last. Neither has a
schema variable or a hypothesis, so each is an exact value (E31) that
discharge.exact_values applies, and a rewrite by either owes nothing.

`sqrt_nonneg : sqrt a >= 0 @ a >= 0` is the owner's sign fact for sqrt atoms
(p1_expected E49, SQRT_NONNEG_ENTRY), appended last. The linear method reads
it for each sqrt atom of a key, as it reads pi_pos for pi (discharge.py's
('fact', 'sqrt_nonneg', u) label); it is also an ordinary cite entry.

The last six are the consolidation's (p1_expected E54, E55), for
Int_0^1 sqrt(1 - x^2) by x := cos theta. `pyth` is the identity as the owner
states it. Its left side is a sum, so field cannot use it (a fact must be
a^k == r); rewrite can, at a subterm tree-equal to (sin b)^2 + (cos b)^2 (a
non-App left side is matched as a tree), turning it into 1, soundly for
every real b, and E57 refuses a b holding an Int or D node, which that
rewrite would erase. E27 (a) counts it. `pyth_cos` is pyth solved for (cos u)^2,
differing from it by a ring identity: a rewrite at (cos b)^2 and a field
fact in §6.2's a^k == r shape. `sin_nonneg_on` and `cos_nonneg_on` are
sign facts whose hypotheses are real conditions on the argument, so they
are read by cite only. `cos_le_one` and `cos_ge_neg_one` are total bounds,
read by the linear method for each cos atom as sqrt_nonneg is for each sqrt
atom (ATOM_FACT_RULE, discharge.ATOM_FACTS), and by cite. None is an exact
value: each has a schema variable.

ENTRIES is read-only: writing to it would extend the trusted cite library
(§15.2 item 7) for the whole process, and it is not one of
kernel/ARCHITECTURE.md §7's seams, so nothing needs it mutable.

FAMILIES (p1_expected E163) holds the one entry no single statement can
state: `rpow_int : rpow(u, n) == u^n @ u > 0` for each integer literal n.
`u^n` with n a schema variable would parse as a real power (GRAMMAR.md
D8), so the family is a template, instantiated for the n an inst gives and
parsed by the trusted parser like every other statement. `resolve` is the
one way the kernel reads an entry by name: an ENTRIES entry unchanged, or a
family's member for the literal its inst carries. Sound for every integer
n: where u > 0, u^n as a real power, exp(n*ln u), is the n-fold product
(its inverse for n < 0, and 1 for n = 0).
"""

from dataclasses import dataclass
from types import MappingProxyType

from terms import (App, Div, Neg, Num, NonZero, Refused, Rel, Term, fv,
                   parse_judgement, show, sort_of, trees)

STATEMENTS = {
    # name: (statement, schema)
    "sqrt_zero": ("sqrt 0 == 0", ()),
    "sqrt_sq": ("sqrt(u^2) == u @ u >= 0", ("u",)),
    "pi_pos": ("pi > 0", ()),
    "sin_pi_half": ("sin(pi/2) == 1", ()),
    "cos_pi_half": ("cos(pi/2) == 0", ()),
    "sin_zero": ("sin 0 == 0", ()),
    "ln_one": ("ln 1 == 0", ()),
    "atan_one_sqrt3": ("atan(1/sqrt 3) == pi/6", ()),
    "atan_odd": ("atan(-u) == -atan u", ("u",)),
    "sqrt_sq_val": ("(sqrt a)^2 == a @ a >= 0", ("a",)),
    "sqrt_pos": ("sqrt a > 0 @ a > 0", ("a",)),
    "e_gt_one": ("e_const > 1", ()),
    "ln_e": ("ln e_const == 1", ()),
    "exp_zero": ("exp 0 == 1", ()),
    "exp_one": ("exp 1 == e_const", ()),
    "cos_zero": ("cos 0 == 1", ()),
    "sqrt_nonneg": ("sqrt a >= 0 @ a >= 0", ("a",)),
    # the consolidation's six (p1_expected E54, CONSOLIDATION_ENTRIES)
    "pyth": ("(sin u)^2 + (cos u)^2 == 1", ("u",)),
    "pyth_cos": ("(cos u)^2 == 1 - (sin u)^2", ("u",)),
    "sin_nonneg_on": ("sin u >= 0 @ u >= 0, u <= pi", ("u",)),
    "cos_nonneg_on": ("cos u >= 0 @ u >= 0, u <= pi/2", ("u",)),
    "cos_le_one": ("cos u <= 1", ("u",)),
    "cos_ge_neg_one": ("cos u >= -1", ("u",)),
    "atan_zero": ("atan 0 == 0", ()),  # p1_expected E80
    # trig_norm's (p1_expected E87): the addition formulas, parity, tan_def
    # (DESIGN.md §6.8, §8.9), and the two values at pi its closes need
    "sin_add": ("sin(u + v) == sin u * cos v + cos u * sin v", ("u", "v")),
    "cos_add": ("cos(u + v) == cos u * cos v - sin u * sin v", ("u", "v")),
    "sin_odd": ("sin(-u) == -sin u", ("u",)),
    "cos_even": ("cos(-u) == cos u", ("u",)),
    "tan_def": ("tan u == sin u / cos u @ cos u # 0", ("u",)),
    "sin_pi": ("sin pi == 0", ()),
    "cos_pi": ("cos pi == -1", ()),
    # p1_expected E103: exp is positive, for a monotone Taylor premise
    "exp_pos": ("exp u > 0", ("u",)),
    # unit 00's (p1_expected E117, UNIT00_ENTRIES): the hyperbolic facts P4
    # uses
    "sinh_zero": ("sinh 0 == 0", ()),
    "cosh_zero": ("cosh 0 == 1", ()),
    "tanh_zero": ("tanh 0 == 0", ()),
    "atanh_zero": ("atanh 0 == 0", ()),
    "tanh_def": ("tanh u == sinh u / cosh u", ("u",)),
    "cosh_sq": ("(cosh u)^2 == 1 + (sinh u)^2", ("u",)),
    "cosh_pos": ("cosh u > 0", ("u",)),
    # G8's (p1_expected E133): t_up substituted into v(t), as the course
    # does, and the height's orientation
    "exp_neg": ("exp(-u) == 1/exp u", ("u",)),
    "exp_ln": ("exp(ln u) == u @ u > 0", ("u",)),
    "ln1p_pos": ("ln(1 + u) > 0 @ u > 0", ("u",)),
    # K1's (p1_expected E172): the principal argument's values. Each order
    # hypothesis forces its variables Real (GRAMMAR.md §11, D20)
    "arg_pos": ("Arg u == 0 @ u > 0", ("u",)),
    "arg_neg": ("Arg u == pi @ u < 0", ("u",)),
    "arg_i_pos": ("Arg(i*u) == pi/2 @ u > 0", ("u",)),
    "arg_i_neg": ("Arg(i*u) == -pi/2 @ u < 0", ("u",)),
    "arg_right": ("Arg(u + i*v) == atan(v/u) @ u > 0", ("u", "v")),
    # K4c-ii's (p1_expected E239): two exact atan values and the left
    # half-plane's argument
    "atan_one": ("atan 1 == pi/4", ()),
    "atan_sqrt3": ("atan(sqrt 3) == pi/3", ()),
    "arg_left_up": ("Arg(u + i*v) == atan(v/u) + pi @ u < 0, v >= 0",
                    ("u", "v")),
    "arg_left_down": ("Arg(u + i*v) == atan(v/u) - pi @ u < 0, v < 0",
                      ("u", "v")),
}


@dataclass(frozen=True, slots=True)
class Entry:
    name: str
    statement: object  # a Judgement
    schema: tuple

    @property
    def hyps(self):
        """The statement's domain items: a tuple of judgements with
        dom == ()."""
        return self.statement.dom


def _load():
    """Parse STATEMENTS into Entry objects, keyed by name. It also checks
    each schema against the statement's free variables, so that a typo in a
    pin fails at import and not in a proof."""
    entries = {}
    for name, (text, schema) in STATEMENTS.items():
        st = parse_judgement(text)
        # A relation, schema exactly its free variables, and hypotheses that
        # are propositions (the kernel emits each one at the use's domain).
        if (not isinstance(st, Rel) or fv(st) != frozenset(schema)
                or not all(isinstance(h, (Rel, NonZero)) for h in st.dom)):
            raise ValueError(f"entry {name}: bad statement or schema {schema}")
        entries[name] = Entry(name, st, schema)
    return entries

ENTRIES = MappingProxyType(_load())


# A family's literal is printed into its template, so it is bounded: a
# literal with thousands of digits would crash the printer, not refuse.
MAX_FAMILY_LITERAL = 10 ** 6

# name: (template, schema, {parameter: kind}). A parameter's value is
# printed into the template: "int" an integer literal ({n}, and {p} the
# same as a power's exponent), "angle" a closed real constant (D19).
FAMILIES = MappingProxyType({
    "rpow_int": ("rpow(u, {n}) == u^{p} @ u > 0", ("u",), {"n": "int"}),
    # E181: periodicity, so sin and cos of any multiple of pi evaluate
    "sin_period": ("sin(u + 2*pi*{k}) == sin u", ("u",), {"k": "int"}),
    "cos_period": ("cos(u + 2*pi*{k}) == cos u", ("u",), {"k": "int"}),
    # E172: one branch's argument from the principal one, 2*pi*k apart
    "arg_branch": ("arg[{theta}] w == Arg w + 2*pi*{k} @ "
                   "{theta} - 2*pi < Arg w + 2*pi*{k}, "
                   "Arg w + 2*pi*{k} <= {theta}", ("w",),
                   {"theta": "angle", "k": "int"}),
    # E239: sin and cos at a multiple of pi/6 or pi/4, from the table
    "sin_table": ("sin({q}*pi) == {v}", (), {"q": "table"}),
    "cos_table": ("cos({q}*pi) == {v}", (), {"q": "table"}),
})


_HALF = Div(Num(1), Num(2))
_COS_SIN_DEG = {  # the first quadrant's exact values (E211, E239)
    0: (Num(1), Num(0)), 30: (Div(App("sqrt", Num(3)), Num(2)), _HALF),
    45: (Div(App("sqrt", Num(2)), Num(2)), Div(App("sqrt", Num(2)), Num(2))),
    60: (_HALF, Div(App("sqrt", Num(3)), Num(2))), 90: (Num(0), Num(1))}


def cos_sin_table(q):
    """(cos, sin) of q*pi exactly, q a Fraction, when q*pi is a multiple of
    pi/6 or pi/4, by reflecting the first quadrant; else None. The one
    trigonometric table the kernel holds (E211, E239)."""
    deg = q * 180
    if deg.denominator != 1 or int(deg) % 15:
        return None
    d = int(deg) % 360
    neg = lambda t: t if t == Num(0) else Neg(t)
    for lo, sc, ss, base in ((0, 1, 1, lambda d: d),
                             (90, -1, 1, lambda d: 180 - d),
                             (180, -1, -1, lambda d: d - 180),
                             (270, 1, -1, lambda d: 360 - d)):
        if lo <= d <= lo + 90 and base(d) in _COS_SIN_DEG:
            c, s = _COS_SIN_DEG[base(d)]
            return (c if sc > 0 else neg(c)), (s if ss > 0 else neg(s))
    return None


def resolve(name, inst):
    """(Entry, inst) for the entry `name` under `inst`, or None when no
    entry has that name. An ENTRIES entry comes back as it is, with inst
    unchanged. A FAMILIES member is built for the values inst gives its
    parameters, each checked for its kind and printed into the template,
    and the parameters are dropped from the inst returned, so the caller
    sees an ordinary entry whose schema is the family's. A missing or
    ill-kinded parameter raises Refused 'bad-args'."""
    if name in ENTRIES:
        return ENTRIES[name], inst
    if name not in FAMILIES:
        return None
    text, schema, params = FAMILIES[name]
    fill = {}
    for param, kind in params.items():
        v = inst.get(param)
        if kind == "int":
            if type(v) is Num:
                k = v.n
            elif type(v) is Neg and type(v.a) is Num:
                k = -v.a.n
            else:
                raise Refused("bad-args", f"{name} takes {param} := an "
                              "integer literal, such as 2 or -1")
            if abs(k) > MAX_FAMILY_LITERAL:  # field would refuse it anyway
                raise Refused("power-too-large", f"{name}: {param} is too "
                              "large")
            fill[param] = str(k)
            fill["p"] = str(k) if k >= 0 else f"({k})"
        elif kind == "table":  # E239: a rational q in the table
            from field import rational_value
            q = rational_value(v) if isinstance(v, Term) else None
            cs = None if q is None else cos_sin_table(q)
            if cs is None:
                raise Refused("bad-args", f"{name} takes {param} := a "
                              "rational q with q*pi a multiple of pi/6 or "
                              "pi/4")
            fill[param] = f"({show(v)})"
            fill["v"] = f"({show(cs[0] if name == 'cos_table' else cs[1])})"
        else:  # "angle": a closed real constant, as a branch's (D19)
            if not isinstance(v, Term) or fv(v) or sort_of(v) != "R" or \
                    next(trees(v), None) is not None:
                raise Refused("bad-args", f"{name} takes {param} := a closed "
                              "real constant, such as pi or 2*pi")
            fill[param] = f"({show(v)})"
    st = parse_judgement(text.format(**fill))
    return (Entry(name, st, schema),
            {v: t for v, t in inst.items() if v not in params})
