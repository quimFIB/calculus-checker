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
"""

from dataclasses import dataclass
from types import MappingProxyType

from terms import NonZero, Rel, fv, parse_judgement

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
