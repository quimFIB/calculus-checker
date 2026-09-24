"""The §6.8 entries this milestone uses, pinned by exact statement.

Trusted (DESIGN.md §15.2 item 7, the cite library). Each statement is a
judgement in GRAMMAR.md syntax, as GRAMMAR.md §9 pins it. `schema` lists the
ordinary variables an instantiation must bind, exactly. A sequent entry is
written with `@` (GRAMMAR.md D14), so an entry's hypotheses are its
statement's domain items. The statements are the kernel's own, parsed from
the strings below at import. p1_expected.py's NAMED_ENTRIES is the check on
them, never their source.

`e_gt_one` and `ln_e` join when stage 0's S3 is run (WHAT.md). P1 uses
neither.

ENTRIES is read-only: writing to it would extend the trusted cite library
(§15.2 item 7) for the whole process, and it is not one of
kernel/ARCHITECTURE.md §7's seams, so nothing needs it mutable.
"""

from dataclasses import dataclass
from types import MappingProxyType

from terms import NonZero, Rel, fv, parse_judgement

STATEMENTS = {
    # name: (statement, schema)
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
