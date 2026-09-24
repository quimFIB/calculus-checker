"""Stage 0's S1-S3 as problem files, with their behaviour written out first.

This is WHAT.md's "Start here" item 3 for the files S1.json, S2.json and
S3.json beside it: for every step of each reference proof, the obligation
list the kernel is expected to emit, the tracker at the end, the admission
count and the verdict. Like kernel/p1_expected.py, it was derived by hand
from DESIGN.md revision 10, kernel/GRAMMAR.md, kernel/ARCHITECTURE.md and
p1_expected.py's stated rules (E1-E26, TAG_RULES, KEYING, REWRITE_RULE,
DOMAIN_RULES). It was written before any code ran against these files, and
without reading the kernel's implementation (kernel.py, field.py, deriv.py,
tagger.py). A mismatch when they run is a finding: either the encoding or
the kernel is wrong.

Nothing here imports anything. Terms and judgements are strings in
GRAMMAR.md's concrete syntax, to be parsed with the kernel's parser and
compared as trees, never as strings. Each obligation is the tuple
p1_expected.OB_FIELDS names: (prop, dom, sources, status, tag, new).

The mathematics was checked at build time with SymPy 1.14 in the session's
scratch directory. That check is not part of this file and nothing here
depends on it (VERIFIED, at the end).

Decisions are marked PF1, PF2, ... (for problem file) and collected in
DECISIONS. Each cites the § or E-number it reads. Places where DESIGN.md,
WHAT.md or ARCHITECTURE.md are wrong or ambiguous are in FINDINGS.
"""

# ---------------------------------------------------------------------------
# 0. Conventions, restated from p1_expected.py so this file stands alone.
#    The values are p1_expected's, verbatim.

SIG = {}  # S1-S3 declare no function symbols (each file's declarations)

VERDICT = "Proved modulo {n} admissions"
DISCHARGED = "discharged"
ADMITTED = "admitted"

# Source codes, as the kernel reports them (p1_expected.SOURCES).
S_FORMER = "former"        # E6, E26: '/' owes d # 0, ln u owes u > 0, ...
S_ORIENT = "orient"        # E4: lo <= hi
S_FTC_C0F = "ftc_F_C0"     # §6.4: F in C^0([a, b])
S_FTC_C1F = "ftc_F_C1"     # §6.4: F in C^1((a, b))
S_FTC_D = "ftc_D"          # §6.4: D[x] F == f @ (a, b), decided in-step
S_FTC_C0f = "ftc_f_C0"     # §6.4: f in C^0([a, b])
S_D_LN = "d_ln"            # §6.3: d_ln's u > 0
S_ROUTE_DIV = "route_div"  # §6.3 rev 7, E12: u/v routed as u*(1/v), v # 0
S_FIELD = "field_div"      # §6.2: every divisor in field's input

# Tags, (method, cites) (E15, E24). T_LINEAR_E is new here: the
# linear-arithmetic tag citing S3's sign fact, as T_LINEAR_PI cites pi_pos
# in P1.1.
T_REG = ("reg", ())
T_RANGE = ("range", ())
T_LINEAR_E = ("linear", ("e_gt_one",))
T_NORM_NUM = ("norm_num", ())
T_DERIV_RING = ("deriv+ring", ())
T_DERIV_FIELD = ("deriv+field", ())


def judgement_string(prop, dom):
    """The parse_judgement input for an obligation, as p1_expected's: a
    regularity judgement carries its domain inside C^k(...)."""
    if " in C^" in prop or dom == "true":
        return prop
    return prop + " @ " + dom


# ---------------------------------------------------------------------------
# 1. The §6.8 entries S1-S3 need that kernel/entries.py does not have yet,
#    pinned by exact statement, in p1_expected.NAMED_ENTRIES' shape.
#    Step 2 adds them to entries.py. This file does not touch it.
#
# PF13. Only e_gt_one has its statement in §6.8 ("e_gt_one : e_const > 1").
# §6.8 names ln_e, exp_zero and exp_one, in the prose list and in the table
# rows "exp 0, 1" and "ln 1, e", but gives no statement for them. ln_e is
# pinned by GRAMMAR.md §9 as (== (ln e_const) 1). exp_zero and exp_one are
# pinned here as the only statements those rows can mean. Each entry below
# has no schema variable and no hypothesis, so using it owes nothing (E1
# steps 8 and 10: R is a literal or a constant, with no former).
#
# S1 needs none. S2 needs exp_one and exp_zero, because its answer is stated
# with e_const (PF7). S3 needs ln_e and e_gt_one (WHAT.md item 4), and
# ln_one, which entries.py already has.

NEW_ENTRIES = {
    "ln_e": {
        "statement": "ln e_const == 1",
        "schema": (),
        "lhs": "ln e_const",
        "rhs": "1",
        "hyps": (),
        "use": "rewrite",
        "cite": "§6.8 (ln_e, named with no statement); statement as "
                "GRAMMAR.md §9 pins it",
        "used_in": ("S3 s2", "S3-ring s2"),
    },
    "e_gt_one": {
        "statement": "e_const > 1",
        "schema": (),
        "hyps": (),
        "use": "sign fact: joins §5.3's constraint set whenever e_const "
               "occurs (rev 9), as pi_pos does for pi; appears here only as "
               "a cite in tags",
        "cite": "§6.8 rev 9 (e_gt_one : e_const > 1)",
        "used_in": ("tags of 1 <= e_const and e_const > 0 (S3, S3-ring)",),
    },
    "exp_zero": {
        "statement": "exp 0 == 1",
        "schema": (),
        "lhs": "exp 0",
        "rhs": "1",
        "hyps": (),
        "use": "rewrite",
        "cite": "§6.8 (exp_zero, named with no statement; table row "
                "'exp 0, 1'); STAGE0.md gap 4",
        "used_in": ("S2 s3",),
    },
    "exp_one": {
        "statement": "exp 1 == e_const",
        "schema": (),
        "lhs": "exp 1",
        "rhs": "e_const",
        "hyps": (),
        "use": "rewrite",
        "cite": "§6.8 (exp_one, named with no statement; table row "
                "'exp 0, 1'); STAGE0.md gap 4",
        "used_in": ("S2 s2",),
    },
}

# Every entry each proof names, new or existing, rewrites and cites alike.
USED_ENTRIES = {
    "S1": (),
    "S2": ("exp_one", "exp_zero"),
    "S3": ("ln_e", "ln_one", "e_gt_one"),
    "S3-ring": ("ln_e", "ln_one", "e_gt_one"),
}

# ---------------------------------------------------------------------------
# 2. The proofs: which file holds each, and what each step is expected to
#    do to the goal.
#
# PF1. The reference proof lives in the problem file, under
# "reference_proof", and an alternative under "alternative_proofs". The
# proofs' (move, args) steps are in the JSON files, in p1_expected.PROOFS'
# step shape ({"id", "move", "args"}), and nowhere else. This file holds only
# what the kernel is expected to do with them, keyed by step id. "move" is
# repeated below so a reordered file fails loudly.

PROOF_FILES = {
    "S1": ("S1.json", "reference_proof"),
    "S2": ("S2.json", "reference_proof"),
    "S3": ("S3.json", "reference_proof"),
    "S3-ring": ("S3.json", "alternative_proofs", "S3-ring"),
}

GOALS = {
    "S1": "Int[x = 0 .. 1] 3*x^2 + 2*x == ?A",
    "S2": "Int[x = 0 .. 1] x*exp(x^2) == ?A",
    "S3": "Int[x = 1 .. e_const] (ln x)/x == ?A",
}
GOALS["S3-ring"] = GOALS["S3"]

# The installed goal as the printer should echo it (GRAMMAR.md §8). S3's is
# the form GRAMMAR.md §9 gives: (ln x)/x prints as ln x / x (R3).
ECHO = {
    "S1": "Int[x = 0 .. 1] 3*x^2 + 2*x == ?A",
    "S2": "Int[x = 0 .. 1] x*exp(x^2) == ?A",
    "S3": "Int[x = 1 .. e_const] ln x / x == ?A",
}

# PF3, PF10. Each ftc goal_after is Add(F[x := b], Neg(F[x := a])), which
# the left-associative strings below parse to (p1_expected P1_1_AFTER_FTC's
# convention). A rewrite target is written as it appears in the goal:
# exp(1^2), not exp 1. REWRITE_RULE step 3 matches it because
# ring_nf(1^2) = 1 = ring_nf(1), the Q21 case P1.2's ln(1 + 0) exercises.
S1_AFTER_FTC = "1^3 + 1^2 - (0^3 + 0^2) == ?A"
S2_AFTER_FTC = "exp(1^2)/2 - exp(0^2)/2 == ?A"
S3_AFTER_FTC = "(ln e_const)^2/2 - (ln 1)^2/2 == ?A"

STEPS = {
    "S1": [
        {"id": "s1", "move": "ftc", "goal_after": S1_AFTER_FTC},
        # ring: 1 + 1 - (0 + 0) = 2
        {"id": "s2", "move": "close", "goal_after": None},
    ],
    "S2": [
        {"id": "s1", "move": "ftc", "goal_after": S2_AFTER_FTC},
        {"id": "s2", "move": "rewrite", "occurrences": 1,
         "goal_after": "e_const/2 - exp(0^2)/2 == ?A"},
        {"id": "s3", "move": "rewrite", "occurrences": 1,
         "goal_after": "e_const/2 - 1/2 == ?A"},
        # ring: (1/2)*e_const - 1/2 on both sides; e_const is an atom, and
        # division by the literal 2 is a coefficient (§6.2)
        {"id": "s4", "move": "close", "goal_after": None},
    ],
    "S3": [
        {"id": "s1", "move": "ftc", "goal_after": S3_AFTER_FTC},
        {"id": "s2", "move": "rewrite", "occurrences": 1,
         "goal_after": "1^2/2 - (ln 1)^2/2 == ?A"},
        {"id": "s3", "move": "rewrite", "occurrences": 1,
         "goal_after": "1^2/2 - 0^2/2 == ?A"},
        # ring over literals: 1/2 - 0 = 1/2 (PF4)
        {"id": "s4", "move": "close", "goal_after": None},
    ],
}
STEPS["S3-ring"] = STEPS["S3"]

THEOREMS = {
    "S1": "Int[x = 0 .. 1] 3*x^2 + 2*x == 2",
    "S2": "Int[x = 0 .. 1] x*exp(x^2) == (e_const - 1)/2",
    "S3": "Int[x = 1 .. e_const] (ln x)/x == 1/2",
}
THEOREMS["S3-ring"] = THEOREMS["S3"]

# ---------------------------------------------------------------------------
# 3. deriv, rule by rule (§6.3, E12), in p1_expected.DERIV's shape: the
#    trace as (rule, subterm, emissions), asserted as a multiset of
#    (rule, subterm) trees; `output` exactly as §6.3's forms build it,
#    which is the lhs the check sees; `emits`, deriv's side conditions at
#    G + (a, b).
#
# E12 applied literally, with no tidying of 0*u or u*1:
#   * d_pow_int builds n * u^(n-1) * D[x]u with n - 1 folded to a literal,
#     so D[x](x^2) is 2*x^1*1 (P1.2's own output has 2*x^1*1).
#   * PF8. u/v with x free and u not the literal 1 is routed as u*(1/v),
#     owing v # 0 (route_div). E12 does not except a literal v, so S2's and
#     S3's F, each over the literal 2, are routed, and owe 2 # 0. It merges
#     with F's own former 2 # 0 (one key, E8) and is discharged by norm_num,
#     so only the sources and the trace depend on this reading.
#   * d_const fires on the x-free 1/2 the routing builds.

DERIV = {
    "S1": {
        "var": "x",
        "F": "x^3 + x^2",
        "trace": [
            ("d_add", "x^3 + x^2", ()),
            ("d_pow_int", "x^3", ()),
            ("d_var", "x", ()),
            ("d_pow_int", "x^2", ()),
            ("d_var", "x", ()),
        ],
        "output": "3*x^2*1 + 2*x^1*1",
        "emits": (),  # d_pow_int with n > 0 owes nothing
    },
    "S2": {
        "var": "x",
        "F": "exp(x^2)/2",
        "trace": [
            ("route_div", "exp(x^2)/2", ("2 # 0",)),
            ("d_mul", "exp(x^2)*(1/2)", ()),
            ("d_exp", "exp(x^2)", ()),   # d_exp has no side condition
            ("d_pow_int", "x^2", ()),
            ("d_var", "x", ()),
            ("d_const", "1/2", ()),
        ],
        "output": "exp(x^2)*(2*x^1*1)*(1/2) + exp(x^2)*0",
        "emits": ("2 # 0",),
    },
    "S3": {
        "var": "x",
        "F": "(ln x)^2 / 2",
        "trace": [
            ("route_div", "(ln x)^2 / 2", ("2 # 0",)),
            ("d_mul", "(ln x)^2*(1/2)", ()),
            ("d_pow_int", "(ln x)^2", ()),
            ("d_ln", "ln x", ("x > 0 @ (1, e_const)",)),
            ("d_var", "x", ()),
            ("d_const", "1/2", ()),
        ],
        # d_ln's D[x]u / u with D[x]x = 1 is 1/x. d_pow_int carries it as
        # its chain factor: 2*(ln x)^1*(1/x).
        "output": "2*(ln x)^1*(1/x)*(1/2) + (ln x)^2*0",
        "emits": ("2 # 0", "x > 0 @ (1, e_const)"),
    },
}
DERIV["S3-ring"] = DERIV["S3"]

# ---------------------------------------------------------------------------
# 4. Expected obligations, step by step.
#
# "goal" is installation: both sides' formers at their position domains
# (E6, E26 (a)), and the orientation of each Int range some emitted key uses
# (E4, ARCHITECTURE.md §4 rewrite: "only when the interval is used").
#
# How the tags were reached (TAG_RULES, E24; every Γ below is empty, since no
# goal has a domain, so hyp never fires):
#   * x > 0 @ [1, e_const] and @ (1, e_const). Fourier-Motzkin over the
#     negated goal x <= 0, the interval's items (1 <= x or 1 < x, and
#     x <= e_const or x < e_const) and e_const's sign fact e_const > 1. The
#     only irreducible infeasible subset is {x <= 0, 1 <= x} (or 1 < x): a
#     dom item is used, so 'range', and e_gt_one's multiplier is zero, so it
#     is not cited. {x <= 0, x <= e_const, e_const > 1} is feasible
#     (x = -1, e_const = 2). PF11.
#   * x # 0 on either interval is tried as x > 0 first, which closes as
#     above: ('range', ()).
#   * 1 <= e_const is closed, so domain true (E5). Its negation
#     e_const < 1 against e_gt_one is infeasible with no dom item: 'linear',
#     citing e_gt_one. It is not literal, so norm_num does not decide it
#     (E7: e_const is a constant, not a rational literal).
#   * e_const > 0, from ln e_const in ftc's new goal (E26 on the goal ftc
#     produces), is closed and not literal. Its negation e_const <= 0
#     against e_const > 1 is infeasible: ('linear', ('e_gt_one',)). PF12.
#   * 2 # 0 and 1 > 0 are literal, so norm_num discharges them (E7).
#   * Regularity is ('reg', ()) by shape. ftc's derivative premise is
#     discharged in-step with the check's name (E9).

EXPECTED_OBLIGATIONS = {
    "S1": {
        # 3*x^2 + 2*x: no divisor, no negative or real power, no partial
        # builtin, so no former, and no key uses the literal range [0, 1],
        # which norm_num orders anyway (E4)
        "goal": [],
        "s1": [
            # literal range: no orientation (E4). F = x^3 + x^2 has no
            # former. deriv emits nothing, and ring emits nothing (§6.2).
            ("x^3 + x^2 in C^0([0, 1])", "[0, 1]", (S_FTC_C0F,), ADMITTED,
             T_REG, True),
            ("x^3 + x^2 in C^1((0, 1))", "(0, 1)", (S_FTC_C1F,), ADMITTED,
             T_REG, True),
            ("D[x](x^3 + x^2) == 3*x^2 + 2*x", "(0, 1)", (S_FTC_D,),
             DISCHARGED, T_DERIV_RING, True),
            ("3*x^2 + 2*x in C^0([0, 1])", "[0, 1]", (S_FTC_C0f,), ADMITTED,
             T_REG, True),
            # the new goal 1^3 + 1^2 - (0^3 + 0^2) has no former
        ],
        "s2": [],  # the value 2 has no former, and ring emits nothing
    },

    "S2": {
        # x*exp(x^2): exp is total (E26 (a) lists it among the builtins that
        # owe nothing), and there is no divisor
        "goal": [],
        "s1": [
            # F's /2 at [0, 1], closed so domain true (E5); deriv's
            # route_div of the same /2 (PF8); the new goal's two /2. One
            # key. ring's check emits nothing (§6.2, PF6).
            ("2 # 0", "true", (S_FORMER, S_ROUTE_DIV), DISCHARGED,
             T_NORM_NUM, True),
            ("exp(x^2)/2 in C^0([0, 1])", "[0, 1]", (S_FTC_C0F,), ADMITTED,
             T_REG, True),
            ("exp(x^2)/2 in C^1((0, 1))", "(0, 1)", (S_FTC_C1F,), ADMITTED,
             T_REG, True),
            ("D[x](exp(x^2)/2) == x*exp(x^2)", "(0, 1)", (S_FTC_D,),
             DISCHARGED, T_DERIV_RING, True),
            ("x*exp(x^2) in C^0([0, 1])", "[0, 1]", (S_FTC_C0f,), ADMITTED,
             T_REG, True),
            # the new goal exp(1^2)/2 - exp(0^2)/2: exp is total, and its /2
            # is the key above
        ],
        "s2": [],  # exp_one: no hypothesis; R = e_const has no former
        "s3": [],  # exp_zero: no hypothesis; R = 1 has no former
        # close: the value (e_const - 1)/2 owes its /2; ring emits nothing
        "s4": [
            ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False),
        ],
    },

    "S3": {
        "goal": [
            # The integrand ln x / x at its position domain, the range
            # [1, e_const] (E4 builds it closed, lo first). The divisor x
            # (E6) and ln's own domain (E26 (a), §5.1's partial-builtin
            # table: ln u owes u > 0). WHAT.md's revision-10 note names the
            # second and not the first.
            ("x # 0", "[1, e_const]", (S_FORMER,), ADMITTED, T_RANGE, True),
            ("x > 0", "[1, e_const]", (S_FORMER,), ADMITTED, T_RANGE, True),
            # Both keys use the range, and 1 .. e_const is not two
            # literals, so installation owes the orientation (E4; §6.4 rev
            # 10). Only e_gt_one closes it.
            ("1 <= e_const", "true", (S_ORIENT,), ADMITTED, T_LINEAR_E,
             True),
        ],
        "s1": [
            # (i) the orientation again (E4, E9), not new
            ("1 <= e_const", "true", (S_ORIENT,), ADMITTED, T_LINEAR_E,
             False),
            # (ii) F's formers on [1, e_const]: its /2, closed so domain
            # true (E5), and its ln x, installation's key again (E8). The
            # 2 # 0 key also comes from deriv's route_div (PF8), from
            # field's divisors (deriv's output holds 1/2), and from the new
            # goal's two /2.
            ("2 # 0", "true", (S_FORMER, S_ROUTE_DIV, S_FIELD), DISCHARGED,
             T_NORM_NUM, True),
            ("x > 0", "[1, e_const]", (S_FORMER,), ADMITTED, T_RANGE, False),
            # (iii) the three regularity premises, split across the closed
            # and open interval (§6.4)
            ("(ln x)^2/2 in C^0([1, e_const])", "[1, e_const]",
             (S_FTC_C0F,), ADMITTED, T_REG, True),
            ("(ln x)^2/2 in C^1((1, e_const))", "(1, e_const)",
             (S_FTC_C1F,), ADMITTED, T_REG, True),
            ("ln x / x in C^0([1, e_const])", "[1, e_const]", (S_FTC_C0f,),
             ADMITTED, T_REG, True),
            # (iv) deriv's side conditions on (1, e_const): d_ln's u > 0. A
            # different key from ln's former on [1, e_const] (E8).
            ("x > 0", "(1, e_const)", (S_D_LN,), ADMITTED, T_RANGE, True),
            # (v) field's divisors on (1, e_const): x from d_ln's output 1/x
            # and from the integrand ln x / x, one key; 2 from 1/2 (above).
            # A different key from installation's x # 0 @ [1, e_const].
            ("x # 0", "(1, e_const)", (S_FIELD,), ADMITTED, T_RANGE, True),
            # (vi) the derivative premise, discharged in the step (E9)
            ("D[x]((ln x)^2/2) == ln x / x", "(1, e_const)", (S_FTC_D,),
             DISCHARGED, T_DERIV_FIELD, True),
            # the new goal (ln e_const)^2/2 - (ln 1)^2/2 at the goal's
            # domain, true (E6, E26): each ln owes its argument > 0 as a
            # tree. ln e_const's is not literal, so it is admitted (PF12);
            # ln 1's is, so norm_num discharges it (E7). Its /2s are the
            # 2 # 0 key above.
            ("e_const > 0", "true", (S_FORMER,), ADMITTED, T_LINEAR_E, True),
            ("1 > 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
        ],
        "s2": [],  # ln_e: no hypothesis, R = 1; the goal has no Int now
        "s3": [],  # ln_one: no hypothesis, R = 0
        # close: the value 1/2 owes its /2; ring emits nothing (PF4)
        "s4": [
            ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False),
        ],
    },
}

# PF5. S3-ring differs only at s1: ring's check owes no divisor (§6.2), so
# field's x # 0 @ (1, e_const) is not emitted, 2 # 0 loses field_div, and
# the premise is tagged deriv+ring. Nothing else in the proof owes that key.
_s3_ring = dict(EXPECTED_OBLIGATIONS["S3"])
_s3_ring["s1"] = [
    ob for ob in EXPECTED_OBLIGATIONS["S3"]["s1"]
    if (ob[0], ob[1]) not in (("x # 0", "(1, e_const)"),
                              ("2 # 0", "true"),
                              ("D[x]((ln x)^2/2) == ln x / x",
                               "(1, e_const)"))
] + [
    ("2 # 0", "true", (S_FORMER, S_ROUTE_DIV), DISCHARGED, T_NORM_NUM, True),
    ("D[x]((ln x)^2/2) == ln x / x", "(1, e_const)", (S_FTC_D,), DISCHARGED,
     T_DERIV_RING, True),
]
EXPECTED_OBLIGATIONS["S3-ring"] = _s3_ring
del _s3_ring

# The tracker at the end of each proof: every key once, with its final
# status and tag. Written out by hand, not computed from the per-step lists,
# so the two cross-check each other. The order follows ARCHITECTURE.md §4's
# emission order but is informative only; compare as a set, as the per-step
# lists are (KEYING).
FINAL_TRACKER = {
    "S1": [
        ("x^3 + x^2 in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
        ("x^3 + x^2 in C^1((0, 1))", "(0, 1)", ADMITTED, T_REG),
        ("D[x](x^3 + x^2) == 3*x^2 + 2*x", "(0, 1)", DISCHARGED,
         T_DERIV_RING),
        ("3*x^2 + 2*x in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
    ],
    "S2": [
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("exp(x^2)/2 in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
        ("exp(x^2)/2 in C^1((0, 1))", "(0, 1)", ADMITTED, T_REG),
        ("D[x](exp(x^2)/2) == x*exp(x^2)", "(0, 1)", DISCHARGED,
         T_DERIV_RING),
        ("x*exp(x^2) in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
    ],
    "S3": [
        ("x # 0", "[1, e_const]", ADMITTED, T_RANGE),
        ("x > 0", "[1, e_const]", ADMITTED, T_RANGE),
        ("1 <= e_const", "true", ADMITTED, T_LINEAR_E),
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("(ln x)^2/2 in C^0([1, e_const])", "[1, e_const]", ADMITTED, T_REG),
        ("(ln x)^2/2 in C^1((1, e_const))", "(1, e_const)", ADMITTED, T_REG),
        ("ln x / x in C^0([1, e_const])", "[1, e_const]", ADMITTED, T_REG),
        ("x > 0", "(1, e_const)", ADMITTED, T_RANGE),
        ("x # 0", "(1, e_const)", ADMITTED, T_RANGE),
        ("D[x]((ln x)^2/2) == ln x / x", "(1, e_const)", DISCHARGED,
         T_DERIV_FIELD),
        ("e_const > 0", "true", ADMITTED, T_LINEAR_E),
        ("1 > 0", "true", DISCHARGED, T_NORM_NUM),
    ],
    "S3-ring": [
        ("x # 0", "[1, e_const]", ADMITTED, T_RANGE),
        ("x > 0", "[1, e_const]", ADMITTED, T_RANGE),
        ("1 <= e_const", "true", ADMITTED, T_LINEAR_E),
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("(ln x)^2/2 in C^0([1, e_const])", "[1, e_const]", ADMITTED, T_REG),
        ("(ln x)^2/2 in C^1((1, e_const))", "(1, e_const)", ADMITTED, T_REG),
        ("ln x / x in C^0([1, e_const])", "[1, e_const]", ADMITTED, T_REG),
        ("x > 0", "(1, e_const)", ADMITTED, T_RANGE),
        ("D[x]((ln x)^2/2) == ln x / x", "(1, e_const)", DISCHARGED,
         T_DERIV_RING),
        ("e_const > 0", "true", ADMITTED, T_LINEAR_E),
        ("1 > 0", "true", DISCHARGED, T_NORM_NUM),
    ],
}

# N in "Proved modulo N admissions". No admission is tagged none, so each
# proof passes the no-none check p1_expected applies to PROOFS runs.
ADMISSIONS = {
    "S1": 3,       # three regularity
    "S2": 3,       # three regularity
    "S3": 9,       # x # 0 and x > 0 on [1, e_const], 1 <= e_const,
                   # x > 0 and x # 0 on (1, e_const), e_const > 0,
                   # three regularity
    "S3-ring": 8,  # no x # 0 @ (1, e_const)
}
VERDICTS = {name: VERDICT.format(n=n) for name, n in ADMISSIONS.items()}

# ---------------------------------------------------------------------------
# 5. Answers

ANSWERS = {
    "S1": "2",
    "S2": "(e_const - 1)/2",
    "S3": "1/2",
    "S3-ring": "1/2",
}
# For a math-module sanity check only. Not terms (GRAMMAR.md D1).
NUMERIC = {
    "S1": 2.0,
    "S2": 0.8591409142295225,  # (e - 1)/2
    "S3": 0.5,
}

# ---------------------------------------------------------------------------
# 6. Refusals
#
# No step of any proof above is expected to refuse. EXPECTED_REFUSALS maps
# (proof, step id) to a refusal code for any that would, and is empty.
EXPECTED_REFUSALS = {}

# PF16. Wrong answers, in p1_expected.WRONG_ANSWERS' shape. WHAT.md does
# not ask for them. They are added because two of them show the new entries
# are needed for the answer as stated: without exp_one and exp_zero, or
# ln_e and ln_one, the close with (e_const - 1)/2 or 1/2 does not go through
# (S2-W2, S3-W2). Before the user's decision of 2026-09-24 on evaluated
# answers, an unevaluated answer needed none of them (PF7). Since then
# (p1_expected E27) it is refused 'close-not-evaluated' (S2-W3, S3-W3), so
# the entries are needed to close the goal at all. Each of the first six is
# refused with the residual lhs - rhs, compared by equality in `compare`,
# never as a string (E14). S2-W3 and S3-W3 are right values in a refused
# form: their residual is E27's offending subterm, compared as a tree
# ("tree"), with 'entry' and 'message' asserted as p1_expected's E27 cases
# are (E27_MESSAGES filled with show(residual) and the entry). Every case
# emits nothing (E13). "goal" starts from the freshly installed goal;
# "state" from the state after that step of that proof.
WRONG_ANSWERS = [
    {"id": "S1-W1",
     "what": "S1 with F := 3*x^3 + 2*x^2 (each term's new power not "
             "divided out)",
     "goal": GOALS["S1"],
     "move": ("ftc", {"F": "3*x^3 + 2*x^2", "check": "ring", "facts": []}),
     "refusal": "ftc-check-failed",
     "residual": "6*x^2 + 2*x",
     "compare": ("ring", ())},
    {"id": "S1-W2",
     "what": "S1 closed with ?A := 1",
     "state": ("S1", "s1"),
     "move": ("close", {"value": "1", "check": "ring", "facts": []}),
     "refusal": "close-check-failed",
     "residual": "1",
     "compare": ("ring", ())},
    {"id": "S2-W1",
     "what": "S2 with F := exp(x^2) (the factor 1/2 missing)",
     "goal": GOALS["S2"],
     "move": ("ftc", {"F": "exp(x^2)", "check": "ring", "facts": []}),
     "refusal": "ftc-check-failed",
     "residual": "x*exp(x^2)",
     "compare": ("ring", ())},
    {"id": "S2-W2",
     "what": "S2 closed with the right value before exp_one and exp_zero: "
             "exp(1^2) and e_const are unrelated atoms to ring (§6.2)",
     "state": ("S2", "s1"),
     "move": ("close", {"value": "(e_const - 1)/2", "check": "ring",
                        "facts": []}),
     "refusal": "close-check-failed",
     "residual": "exp(1^2)/2 - exp(0^2)/2 - (e_const - 1)/2",
     "compare": ("ring", ())},
    {"id": "S3-W1",
     "what": "S3 with F := (ln x)^2 (the factor 1/2 missing)",
     "goal": GOALS["S3"],
     "move": ("ftc", {"F": "(ln x)^2", "check": "field", "facts": []}),
     "refusal": "ftc-check-failed",
     "residual": "ln x / x",
     "compare": ("field", ())},
    {"id": "S3-W2",
     "what": "S3 closed with the right value before ln_e and ln_one",
     "state": ("S3", "s1"),
     "move": ("close", {"value": "1/2", "check": "ring", "facts": []}),
     "refusal": "close-check-failed",
     "residual": "(ln e_const)^2/2 - (ln 1)^2/2 - 1/2",
     "compare": ("ring", ())},
    # Added by user decision 2026-09-24 (evaluated answers), p1_expected
    # E27. Each value is right (SymPy, VERIFIED) and ring proves it equal to
    # the goal after s1, which is what closed before E27. E19, E23, the
    # value's formers (2 # 0, and S3's e_const > 0 and 1 > 0, all keys s1
    # already minted) and check_goal pass, so E27, which runs last, is the
    # refusal. Its first (a) offender in pre-order is the leftmost
    # application, which (a1) matches through E1 step 3.
    {"id": "S2-W3",
     "added": True,
     "what": "S2 closed with its right value unevaluated, (exp 1 - exp 0)/2, "
             "after s1: ring proves it (exp 1 and exp(1^2) are one atom, "
             "§6.2) but exp_one still applies (E27 (a))",
     "state": ("S2", "s1"),
     "move": ("close", {"value": "(exp 1 - exp 0)/2", "check": "ring",
                        "facts": []}),
     "refusal": "close-not-evaluated",
     "residual": "exp 1",
     "compare": ("tree", ()),
     "entry": "exp_one",
     "message": "exp 1 can still be evaluated (exp_one)"},
    {"id": "S3-W3",
     "added": True,
     "what": "S3 closed with its right value unevaluated, (ln e_const)^2/2 "
             "- (ln 1)^2/2, the goal's own left side after s1: ln_e still "
             "applies (E27 (a))",
     "state": ("S3", "s1"),
     "move": ("close", {"value": "(ln e_const)^2/2 - (ln 1)^2/2",
                        "check": "ring", "facts": []}),
     "refusal": "close-not-evaluated",
     "residual": "ln e_const",
     "compare": ("tree", ()),
     "entry": "ln_e",
     "message": "ln e_const can still be evaluated (ln_e)"},
]

# ---------------------------------------------------------------------------
# 7. The decisions, collected

DECISIONS = {
    "PF1": "The reference proof goes in the problem file, under "
           "'reference_proof', with any alternatives under "
           "'alternative_proofs'. §16.4 lists four things a problem file "
           "holds (statement, formal goal, answer schema, declarations), and "
           "puts scripts under persistence, a file per problem in the "
           "working directory. That separates the learner's attempts from "
           "the problem. It does not argue for separating the author's "
           "proof: the author's proof is evidence that the goal is provable "
           "as stated, which §9 says is authored with the problem and §17 "
           "says the kernel is the reviewer of. Kept in one file, it cannot "
           "drift from the goal it proves. It is also what WHAT.md's "
           "'problem ... proof ... qed' shape describes, and §1's "
           "replaceability test puts both in the course-specific package. "
           "The constraint it brings: the client must never show "
           "'reference_proof' to the learner. §2's hint ladder comes from "
           "the recognizer's layers, not from a stored solution, so nothing "
           "in the tool needs to read it except the regression suite. "
           "§16.4 should name the fifth field.",
    "PF2": "The file's keys are a closed set: format ('calc-problem/0'), "
           "id, title, source, statement (prose, not parsed), goal "
           "(GRAMMAR.md syntax, for terms.parse_goal with sig = "
           "declarations.functions), answer_schema ('closed', the E23 "
           "whitelist; §9's 'closed + erf' extensions are not needed here), "
           "declarations ({'functions': {name: arity}}, the parser's sig), "
           "reference_proof, alternative_proofs (optional; id -> {why, "
           "steps}) and notes (prose). A step is {id, move, args}, and args "
           "is p1_expected.PROOFS' args with terms as GRAMMAR.md strings "
           "and a handle as ['handle', name] (JSON has no tuples). S1-S3 "
           "need no handle",
    "PF3": "WHAT.md's 'step rewrite [ln_e, ln_one]' is two rewrite steps. "
           "The kernel's rewrite takes one entry and one target "
           "(REWRITE_RULE's arguments, ARCHITECTURE.md §4), and P1.2 "
           "writes its three ln_one rewrites as three steps for the same "
           "reason",
    "PF4": "WHAT.md's 'close ?A := 1/2 by norm_num' is close with check "
           "ring. close takes ring or field (ARCHITECTURE.md §4), and "
           "norm_num runs only on obligations at emission (E7). "
           "1^2/2 - 0^2/2 == 1/2 is over rational literals, which ring "
           "decides exactly. The same holds for S1's and S2's closes",
    "PF5": "S3's ftc checks with field, as WHAT.md's block does, so its "
           "field divisor x # 0 @ (1, e_const) is expected. ring would close "
           "the check too: deriv's output 2*(ln x)^1*(1/x)*(1/2) and the "
           "integrand ln x / x both ring-normalise to ln x * inv(x) under "
           "E3, since 2 and 1/2 are rational coefficients. That route is "
           "kept as S3-ring, with one admission fewer. It pins §6.2's 'ring "
           "emits no obligations' against ARCHITECTURE.md §4's ftc text, "
           "which says the check's divisors are emitted as field_div "
           "without saying whether that holds for ring. Soundness does not "
           "need the missing key: the integrand's x # 0 was charged at "
           "installation on [1, e_const], which contains (1, e_const), and "
           "d_ln's x > 0 covers deriv's 1/x",
    "PF6": "S2's ftc checks with ring. Its only divisor is the literal 2, "
           "which ring reads as a coefficient (§6.2). field would add the "
           "field_div source to 2 # 0 and change nothing else",
    "PF7": "S2's answer is (e_const - 1)/2, STAGE0.md's (e - 1)/2, reached "
           "by rewriting exp(1^2) with exp_one and exp(0^2) with exp_zero, "
           "then closing by ring. An answer written (exp 1 - 1)/2 would "
           "pass ring's check without exp_one, because exp(1^2) and exp 1 "
           "are one atom (§6.2, atoms up to their arguments' normal "
           "forms), but not without exp_zero, and it is not how the answer "
           "is usually stated. So S2, with its answer as stated, needs two "
           "§6.8 entries WHAT.md does not list. Before the user's decision "
           "of 2026-09-24 on evaluated answers they were not needed to "
           "close S2 at all: §9's closed whitelist accepted the unevaluated "
           "(exp 1 - exp 0)/2, which ring closes after s1, modulo 3, using "
           "no entry, and likewise S3 closed with (ln e_const)^2/2 - "
           "(ln 1)^2/2, modulo 9, without ln_e or ln_one (FINDINGS 12). "
           "Since that decision a closed answer must be fully evaluated "
           "(p1_expected E27), so both are refused 'close-not-evaluated', "
           "naming exp_one and ln_e (S2-W3, S3-W3), and so is (exp 1 - 1)/2 "
           "(exp 1 is exp_one's left side). Now the entries are needed to "
           "close the goal, not only for the answer as stated: any value "
           "ring proves equal to S2's post-ftc side keeps an exp atom whose "
           "argument normalises to 1 or to 0 unless the rewrites are made, "
           "and E27 (a) matches through that normal form (E1 step 3); "
           "likewise S3's ln atoms",
    "PF8": "deriv routes F's u/2 through u*(1/2), owing 2 # 0 with source "
           "route_div (E12: every u/v with x free and u not the literal 1). "
           "E12 makes no exception for a literal v. If the kernel reads "
           "division by a literal as a coefficient instead, as ring does, "
           "S2's and S3's traces lose route_div and 2 # 0 loses that "
           "source. Nothing else changes, because 2 # 0 is F's own former "
           "anyway and is discharged",
    "PF9": "S1's F is x^3 + x^2. It is the antiderivative in lowest terms, "
           "and it has no divisor, so S1 stays the control case with "
           "nothing owed but regularity",
    "PF10": "Rewrite targets are the subterms as they stand in the goal "
            "(exp(1^2), exp(0^2), ln e_const, ln 1). REWRITE_RULE step 3 "
            "matches exp(1^2) against exp_one's exp 1 through ring_nf of "
            "the argument, as P1.2 matches ln(1 + 0) against ln 1 (§18 "
            "Q21). No rewrite is under an Int, since ftc has consumed it, "
            "so none owes an orientation (E1 step 7)",
    "PF11": "The x > 0 and x # 0 keys on [1, e_const] and (1, e_const) are "
            "tagged ('range', ()) with no cite. TAG_RULES cites a sign fact "
            "only when its multiplier is nonzero, and 1 <= x (or 1 < x) "
            "alone refutes x <= 0. e_gt_one is cited by 1 <= e_const and "
            "e_const > 0 instead. That is where it does its work: the item "
            "1 <= x is the range only once 1 <= e_const holds. WHAT.md's "
            "block annotates each x > 0 'by range, e_gt_one; linear', which "
            "joins the two, as §11.1's '0 <= t by range, pi_pos' did for "
            "P1.1, and p1_expected split it the same way",
    "PF12": "The goal ftc produces holds ln e_const, which owes "
            "e_const > 0 (E26 (a), charged on ftc's new goal). It is closed, "
            "so its domain is true (E5). It is not literal, because e_const "
            "is a constant and not a rational (E7), so it is admitted, "
            "tagged ('linear', ('e_gt_one',)). Neither WHAT.md's block nor "
            "its revision-10 note lists it. ln 1 in the same goal owes "
            "1 > 0, which is literal and discharged",
    "PF13": "NEW_ENTRIES: e_gt_one as §6.8 states it; ln_e as GRAMMAR.md "
            "§9 pins it; exp_zero as exp 0 == 1 and exp_one as "
            "exp 1 == e_const, which §6.8 names but does not state. None "
            "has a schema variable or a hypothesis",
    "PF14": "The domain strings follow p1_expected: a bare interval names "
            "the judgement's one free variable (GRAMMAR.md D13, R4), a "
            "closed obligation's domain is 'true' (E5), and a regularity "
            "judgement's dom column repeats the domain inside C^k(...)",
    "PF15": "declarations.functions is empty for all three: no goal calls a "
            "declared symbol, and none has a free variable or a hypothesis "
            "(every goal's domain is true). §5.2's variable declarations "
            "have no file form yet. S5 in STAGE0.md is the first goal that "
            "will need one",
    "PF16": "No reference step is expected to refuse (EXPECTED_REFUSALS is "
            "empty). WRONG_ANSWERS adds eight refusals. Six are one wrong F "
            "and one wrong or premature close per problem. S2-W2 and S3-W2 "
            "show the new entries are needed for the answer as stated. The "
            "other two, S2-W3 and S3-W3, added by the user's decision of "
            "2026-09-24 on evaluated answers (p1_expected E27), close with "
            "the right value unevaluated and are refused "
            "'close-not-evaluated', which shows the entries are now needed "
            "to close the goal at all (PF7). Their residual is E27's "
            "offending subterm, not lhs - rhs, so it is compared as a tree "
            "('tree'), and each names its entry and message. None of the "
            "eight was asked for, and each is labelled",
    # discharge spec 2026-09-24
    "PF17": "Discharge for the problem files follows p1_expected's "
            "section 11 (DISCHARGE_RULE, E28-E34) unchanged. S3's six "
            "non-Reg admissions become DISCHARGED with the tags PF11 and "
            "PF12 gave: the four x > 0 and x # 0 keys by a Farkas "
            "certificate on the lower end 1 (range, no cite), 1 <= e_const "
            "and e_const > 0 by one with e_gt_one (linear). S1 and S2 "
            "admitted only regularity. So every stage-0 proof reads 'Proved "
            "modulo 3 admissions', S3 from 9 and S3-ring from 8, and "
            "e_gt_one does its work exactly where PF11 placed it. No "
            "WRONG_ANSWERS outcome changes: each refused step emits only "
            "true obligations before its refusal, so no decided-false "
            "refusal comes first. The owner's answers of 2026-09-24 "
            "(p1_expected E35) change nothing here: no S1-S3 goal, step, "
            "obligation or value holds cos 0 or sqrt 0, so the two new "
            "exact values (cos_zero, sqrt_zero, pinned in p1_expected's "
            "DISCHARGE_NEW_ENTRIES, not here) touch no stage-0 key and no "
            "E27 case; and no stage-0 obligation is refuted, so the new "
            "message form has no instance",
}

# ---------------------------------------------------------------------------
# 8. What deriving this found in the design documents. For folding in, in
#    the way PROOF_OF_LIFE.md collects p1_expected's DESIGN_DEFECTS.

FINDINGS = [
    "WHAT.md, S3 block: 'rewrite [ln_e, ln_one]' names two entries in one "
    "step, and the kernel's rewrite takes one (PF3). 'close ?A := 1/2 by "
    "norm_num' names a check close does not take (PF4).",
    "WHAT.md, S3 block and its revision-10 note: the installation also owes "
    "the integrand's divisor x # 0 @ [1, e_const] (E6), which neither "
    "lists. The goal ftc produces owes e_const > 0 from ln e_const, "
    "admitted and needing e_gt_one (PF12), and 1 > 0 from ln 1, "
    "discharged. F's literal 2 owes 2 # 0, discharged. The note names only "
    "ln's x > 0 on [1, e_const] and the orientation 1 <= e_const.",
    "WHAT.md, S3 block: the x > 0 lines are annotated 'by range, e_gt_one; "
    "linear'. Under TAG_RULES they are range with no cite. e_gt_one belongs "
    "to the orientation and to e_const > 0 (PF11). §6.8's e_gt_one "
    "paragraph says d_ln's x > 0 is out of reach without the sign fact. "
    "That is correct under §5.3 method 2's own text, which adds the "
    "range's a <= t <= b only once the order of a and b follows from the "
    "constraint set, so without e_const > 1 it adds nothing and x > 0 does "
    "not follow. The departure is TAG_RULES and E4: the tagger always adds "
    "an interval's [lo, hi] items, and the order they presuppose is split "
    "out as the separate obligation 1 <= e_const (E4, charged where the "
    "range is used), which is where e_gt_one is then cited. Under that "
    "reading x > 0 is range with no cite. So the §5.3 method 2 sentence "
    "('adds nothing rather than a min/max') needs folding as well as "
    "§6.8's, to say the orientation is owed instead of presupposed.",
    "WHAT.md, S3 block: '(ln x)/x ∈ C⁰([1,e_const]) by reg' lists only "
    "x > 0 under it. §6.9's quotient rule needs x # 0 as well, which is "
    "the installation key above. And 'F ∈ C¹((1,e_const))' is listed "
    "against x > 0 @ [1, e_const], where §6.9 would ask for x > 0 on the "
    "open (1, e_const) (as p1_expected.REGULARITY_LISTING does for P1.2).",
    "WHAT.md says 'field closes the derivative owing x # 0'. ring closes it "
    "too, owing nothing, by E3 (PF5). That is not an error, but a reader "
    "could take it to mean field is required.",
    "WHAT.md item 4 names ln_e and e_gt_one as the §6.8 entries to add. S2, "
    "with its answer stated as (e_const - 1)/2, needs exp_one and exp_zero "
    "too (PF7). STAGE0.md gap 4 found both, alongside ln_e.",
    "§6.8 names ln_e, exp_zero and exp_one without statements. Only "
    "e_gt_one, among the entries S1-S3 need, is stated there, and ln_e's "
    "statement lives only in GRAMMAR.md §9 (PF13). §6.8 says the table is "
    "'the most traffic in the document on the least specification', and "
    "these three are examples.",
    "§16.4 lists four things in a problem file and no reference proof. "
    "WHAT.md's 'problem ... proof ... qed' shape includes one. Decided in "
    "PF1; §16.4 should name the field and say the client does not show it. "
    "§16.4 also does not give 'declarations' a shape (PF2, PF15).",
    "E12 (p1_expected) routes u/v whenever x is free and u is not the "
    "literal 1, with no exception for a literal v, while §6.2 treats "
    "division by a literal as a coefficient. No P1 F divides by a literal "
    "at top level with x free in the numerator, so P1 never tested which "
    "reading deriv takes. S2 and S3 do (PF8).",
    "kernel/ARCHITECTURE.md §4, ftc: 'the check deriv(F).output == f, whose "
    "divisors are emitted at G+J (field_div)' does not say whether that "
    "holds when check is ring. §6.2 says ring emits nothing. P1.1's check "
    "was ring but its deriv output had no divisor, so P1 never tested "
    "this. S3-ring does (PF5).",
    "For step 2: the tags above need e_gt_one in the tagger's sign-fact "
    "table beside pi_pos (TAG_RULES: 'e_gt_one : e_const > 1'), not only "
    "in entries.py.",
    "§9's closed schema did not require an evaluated form. After ftc, S3 "
    "closed by ring with ?A := (ln e_const)^2/2 - (ln 1)^2/2 (modulo 9) "
    "and S2 with ?A := (exp 1 - exp 0)/2 (modulo 3), using none of ln_e, "
    "ln_one, exp_one or exp_zero, because the whitelist accepts an "
    "unevaluated F(b) - F(a). So §6.8's 'every authored goal terminates "
    "in this table' was not enforced by anything the kernel checks. "
    "DECIDED by the user on 2026-09-24: answers under `closed` must be "
    "fully evaluated. p1_expected E27 states it as a checkable property, "
    "not a canonical form: (a) no subterm matches the left side of an "
    "equation entry in force, matched as rewrite matches (E1, "
    "ring-normalised arguments), and (b) no unreduced literal arithmetic. "
    "It is checked untrusted, beside the whitelist, and last in close, so "
    "'close-not-evaluated' means right value, unevaluated form. S2-W3 and "
    "S3-W3 pin it here, and the entries are now needed to close the goal "
    "(PF7, PF16). Still for DESIGN.md: §9 should state the requirement and "
    "where it runs, and §6.8 should say that its claim now holds of every "
    "accepted close, relative to the entries in force (p1_expected "
    "DESIGN_DEFECTS).",
]

# ---------------------------------------------------------------------------
# 9. What was checked at build time, in scratch, with SymPy 1.14. None of it
#    is imported here.

VERIFIED = (
    "each F' equals its integrand: d/dx(x^3 + x^2) = 3x^2 + 2x, "
    "d/dx(exp(x^2)/2) = x*exp(x^2), d/dx((ln x)^2/2) = ln(x)/x",
    "each DERIV output, read as a function, equals the true derivative, "
    "and each is the literal application of §6.3's forms under E12",
    "each endpoint value: F(1) - F(0) = 2 for S1; exp(1)/2 - exp(0)/2 = "
    "(e - 1)/2 for S2; ln(e)^2/2 - ln(1)^2/2 = 1/2 for S3",
    "each answer equals its integral, symbolically and numerically, and "
    "NUMERIC matches",
    "each goal_after follows from the one before: F[b] - F[a] for ftc, and "
    "one occurrence of the target replaced by the entry's rhs for each "
    "rewrite, with ring_nf of the argument agreeing (1^2 = 1, 0^2 = 0)",
    "each close: lhs - value is 0 by expansion over Q with ln e_const, "
    "exp(1^2), exp(0^2) and e_const kept as free symbols where the entry "
    "is not yet applied",
    "each obligation is true on its domain: x # 0 and x > 0 on [1, e] and "
    "(1, e) (minimum of x is 1), 1 <= e, e > 0, 1 > 0 and 2 # 0; the "
    "regularity premises by hand (polynomials and exp everywhere; ln and "
    "1/x on x > 0, which [1, e] is inside)",
    "each field divisor list equals the set of divisors in deriv(F) and f",
    "the Fourier-Motzkin sets behind each tag: {x <= 0, 1 <= x} and "
    "{x <= 0, 1 < x} infeasible; {x <= 0, x <= e, e > 1} feasible at "
    "x = -1, e = 2, so e_gt_one gets zero multiplier; {e < 1, e > 1} and "
    "{e <= 0, e > 1} infeasible; {e < 1} and {e <= 0} feasible without "
    "the sign fact, so it is needed",
    "each new entry is true: ln(E) = 1, E > 1, exp(0) = 1, exp(1) = E",
    "each wrong answer's residual equals lhs - rhs and is nonzero",
    "per-step lists and FINAL_TRACKER agree, and the admission counts match",
    "every JSON file loads, and its step ids and moves match STEPS",
    # Added by user decision 2026-09-24 (evaluated answers).
    "S2-W3 and S3-W3 refuse right values: (exp(1) - exp(0))/2 = (e - 1)/2 "
    "and ln(e)^2/2 - ln(1)^2/2 = 1/2, each equal to its integral, so each "
    "refusal is about form, not truth; each residual (exp 1, ln e_const) is "
    "the first node in pre-order that E27 (a) matches, and each message is "
    "E27_MESSAGES' (a) template filled with it, checked with a throwaway "
    "scratch reading of E27 over terms.py's parser and printer, not kernel "
    "code; both strings parse and round-trip",
    # Added by the discharge spec 2026-09-24.
    "discharge spec 2026-09-24: p1_expected's scratch SymPy reading of "
    "DISCHARGE_RULE accepts each S3 certificate with its tag ((0 - x) + "
    "(x - 1) = -1 on both ranges, (1 - e) + (e - 1) = 0 strict, (0 - e) + "
    "(e - 1) = -1), each key is true on its domain with e real, and each "
    "Farkas key's set without the goal is satisfiable (x = 3/2, e = 2)",
)

# ---------------------------------------------------------------------------
# 10. Changes made after the kernel first ran against this file, each as
#     (location, old, new, why, evidence). The first run (2026-09-24,
#     kernel/proof_of_life.py item 7) matched every assertion above, so no
#     expected value has changed. The first two entries below are text-only
#     fixes from the review of that run. The rest carry out the user's
#     decision of 2026-09-24 on evaluated answers (p1_expected E27): they
#     add two cases and reword text, and change no existing expected value.
#     A change here needs a reason in the rules, never only that the kernel
#     disagrees.

CHANGES = (
    ("PF7, PF16 (the WRONG_ANSWERS comment and DECISIONS)",
     "the new entries are said to be needed",
     "needed for the answer as stated, not needed to close the goal",
     "text-only review fix, no expected value changed: §9's closed "
     "whitelist accepts an unevaluated F(b) - F(a), so the goals close "
     "without the entries",
     "run 2026-09-24: after s1, close ?A := (ln e_const)^2/2 - (ln 1)^2/2 "
     "by ring gives S3 'Proved modulo 9 admissions', and ?A := "
     "(exp 1 - exp 0)/2 gives S2 'Proved modulo 3 admissions', citing no "
     "entry; a FINDINGS entry records it for DESIGN.md"),
    ("FINDINGS item 3 (e_gt_one and d_ln's x > 0)",
     "§6.8's 'd_ln's x > 0 is out of reach' called a conflation",
     "§6.8 is correct under §5.3 method 2's text; the departure is "
     "TAG_RULES and E4 adding the [lo, hi] items with the orientation "
     "split out, so method 2's sentence needs folding too",
     "text-only review fix, no expected value changed: the tags PF11 gives "
     "follow TAG_RULES, not §5.3 method 2 as written",
     "DESIGN.md §5.3 method 2: 'method 2 can write its constraint as a "
     "linear a <= t <= b only once the order of a and b follows from the "
     "constraint set. Where it does not, method 2 adds nothing'"),
    ("WRONG_ANSWERS S2-W3 and S3-W3 (new)",
     "no case closed S2 or S3 with the unevaluated F(b) - F(a)",
     "S2-W3 closes S2 after s1 with (exp 1 - exp 0)/2 and S3-W3 closes S3 "
     "after s1 with (ln e_const)^2/2 - (ln 1)^2/2, each by ring, each "
     "expected refused 'close-not-evaluated' with residual exp 1 (entry "
     "exp_one) or ln e_const (entry ln_e), compared as a tree, and its "
     "message",
     "user decision 2026-09-24 (evaluated answers): answers under `closed` "
     "must be fully evaluated (p1_expected E27). These are FINDINGS 12's "
     "two closes, which were accepted before",
     "derived by hand from E27 before any code: E27 runs last in close, "
     "after ring's check, which passes, and its (a) search meets exp 1 and "
     "ln e_const first in pre-order; SymPy: (e - 1)/2 and 1/2, so the "
     "values are right. The suite needs a 'tree' comparison and the "
     "entry/message assertions, and fails on both cases until schema.py "
     "implements E27"),
    ("PF7, PF16, the WRONG_ANSWERS comment (PF16)",
     "the entries needed for the answer as stated, not to close the goal; "
     "the whitelist accepts the unevaluated forms; six wrong answers",
     "before the decision the whitelist accepted the unevaluated forms; "
     "since it (E27) they are refused, so the entries are needed to close "
     "the goal at all; eight refusals, the two new ones right values in a "
     "refused form, with a tree-compared residual",
     "user decision 2026-09-24 (evaluated answers)",
     "p1_expected EVALUATED_RULE (a1): a value ring proves equal to S2's or "
     "S3's post-ftc side keeps an atom whose argument normalises to an "
     "entry's, and (a) matches through that normal form"),
    ("FINDINGS item 12",
     "an open question for DESIGN.md: should the closed schema require an "
     "evaluated form",
     "decided (E27), with what DESIGN.md §9 and §6.8 still need to say",
     "user decision 2026-09-24 (evaluated answers)",
     "p1_expected DECISIONS E27, DESIGN_DEFECTS' §9/§6.8 entry"),
    ("VERIFIED, one entry appended",
     "none",
     "the SymPy and scratch checks behind S2-W3 and S3-W3",
     "user decision 2026-09-24 (evaluated answers)",
     "scratch run 2026-09-24, SymPy 1.14"),
    # discharge spec 2026-09-24: additions only, no existing value changed.
    ("section 11 (new): DISCHARGE_EXPECTED, DISCHARGE_OBLIGATIONS, "
     "DISCHARGE_FINAL_TRACKER, DISCHARGE_ADMISSIONS, DISCHARGE_VERDICTS, "
     "DISCHARGE_S0_SEAMS",
     "every admission reason 'discharge not built', and S3's six non-Reg "
     "keys admitted",
     "S3's six keys DISCHARGED with their certificates and unchanged tags; "
     "N = 3 for S1, S2, S3 and S3-ring; the two stage-0 seams move no N",
     "WHAT.md 'Start here' item 1: the expected results written before the "
     "discharge code, under p1_expected's DISCHARGE_RULE",
     "derived by hand from DISCHARGE_RULE and PF11/PF12's traces; the "
     "import-time cross-check against FINAL_TRACKER passes; scratch SymPy "
     "check (VERIFIED)"),
    ("DECISIONS PF17 (new), VERIFIED (one entry appended)",
     "none",
     "PF17 records how discharge reads the problem files; VERIFIED the "
     "checks behind it",
     "discharge spec 2026-09-24",
     "scratch run 2026-09-24, SymPy 1.14"),
    ("DECISIONS PF17, one sentence appended",
     "silent on the owner's answers",
     "records that p1_expected E35 changes no stage-0 value: no S1-S3 "
     "goal, step, obligation or value holds cos 0 or sqrt 0, and the new "
     "entries are pinned in p1_expected's DISCHARGE_NEW_ENTRIES",
     "discharge spec 2026-09-24, owner answers",
     "grep of S1.json-S3.json and this file for cos 0 and sqrt 0: none; "
     "the verifier re-run passes with the entries in force"),
)

# ---------------------------------------------------------------------------
# 11. Real discharge, specified before any code (discharge spec 2026-09-24)
#
# p1_expected's section 11 states the rule (DISCHARGE_RULE, E28-E34); this
# is S1-S3's data under it, derived by hand the same way and without reading
# kernel.py, tagger.py or field.py. The pre-discharge tables above are kept
# as the record and asserted until the suite switches (p1_expected
# DISCHARGE_SWITCH). Nothing here changes a goal, a step, a source, a `new`
# flag or a tag: statuses change, and each obligation gains a reason and a
# certificate. WRONG_ANSWERS are unchanged: every obligation they emit
# before their refusal is true, so discharge refuses nothing earlier.
#
# Restated from p1_expected so this file stands alone (the values are
# p1_expected's, verbatim).
REASON_REG = "regularity not built"
REASON_NONE = "no method decides it"

GOAL = ("goal",)


def LO(i):
    return ("dom", i, "lo")


def FACT(name):
    return ("fact", name)


def _farkas(mults, sense=None):
    return {"method": "farkas", "sense": sense, "multipliers": dict(mults)}


# The certificates. For x > 0 and x # 0 on a range whose lower end is 1:
# (0 - x, non-strict) + (x - 1, the lower end) = -1, whatever the end's
# openness, and e_gt_one's multiplier is zero, so it is not cited (PF11).
# For 1 <= e_const: (1 - e_const, strict) + (e_const - 1, strict) = 0 with a
# strict constraint. For e_const > 0: (0 - e_const, non-strict) +
# (e_const - 1, strict) = -1. Each Farkas key passes the pre-check:
# [1, e_const] and (1, e_const) with e_const > 1 hold at x = 3/2,
# e_const = 2.
_RANGE_LO = _farkas({GOAL: "1", LO(0): "1"})
_RANGE_LO_NZ = _farkas({GOAL: "1", LO(0): "1"}, ">")
_E_FACT = _farkas({GOAL: "1", FACT("e_gt_one"): "1"})

DISCHARGE_EXPECTED = {
    "S1": {},   # nothing but regularity was ever admitted
    "S2": {},
    "S3": {
        ("x # 0", "[1, e_const]"): (T_RANGE, _RANGE_LO_NZ),
        ("x > 0", "[1, e_const]"): (T_RANGE, _RANGE_LO),
        ("1 <= e_const", "true"): (T_LINEAR_E, _E_FACT),
        ("x > 0", "(1, e_const)"): (T_RANGE, _RANGE_LO),
        ("x # 0", "(1, e_const)"): (T_RANGE, _RANGE_LO_NZ),
        ("e_const > 0", "true"): (T_LINEAR_E, _E_FACT),
    },
}
DISCHARGE_EXPECTED["S3-ring"] = {
    k: v for k, v in DISCHARGE_EXPECTED["S3"].items()
    if k != ("x # 0", "(1, e_const)")}


def _after_discharge(ob, table):
    """p1_expected's rule: an admission DISCHARGE_EXPECTED lists becomes
    DISCHARGED with its tag unchanged; everything else is unchanged."""
    prop, dom, sources, status, tag, new = ob
    if status == ADMITTED and (prop, dom) in table:
        assert table[(prop, dom)][0] == tag, (prop, dom)
        return (prop, dom, sources, DISCHARGED, tag, new)
    return ob


DISCHARGE_OBLIGATIONS = {
    proof: {sid: [_after_discharge(ob, DISCHARGE_EXPECTED[proof])
                  for ob in obs]
            for sid, obs in steps.items()}
    for proof, steps in EXPECTED_OBLIGATIONS.items()}

# Written out by hand.
DISCHARGE_FINAL_TRACKER = {
    "S1": [
        ("x^3 + x^2 in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
        ("x^3 + x^2 in C^1((0, 1))", "(0, 1)", ADMITTED, T_REG),
        ("D[x](x^3 + x^2) == 3*x^2 + 2*x", "(0, 1)", DISCHARGED,
         T_DERIV_RING),
        ("3*x^2 + 2*x in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
    ],
    "S2": [
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("exp(x^2)/2 in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
        ("exp(x^2)/2 in C^1((0, 1))", "(0, 1)", ADMITTED, T_REG),
        ("D[x](exp(x^2)/2) == x*exp(x^2)", "(0, 1)", DISCHARGED,
         T_DERIV_RING),
        ("x*exp(x^2) in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
    ],
    "S3": [
        ("x # 0", "[1, e_const]", DISCHARGED, T_RANGE),
        ("x > 0", "[1, e_const]", DISCHARGED, T_RANGE),
        ("1 <= e_const", "true", DISCHARGED, T_LINEAR_E),
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("(ln x)^2/2 in C^0([1, e_const])", "[1, e_const]", ADMITTED, T_REG),
        ("(ln x)^2/2 in C^1((1, e_const))", "(1, e_const)", ADMITTED, T_REG),
        ("ln x / x in C^0([1, e_const])", "[1, e_const]", ADMITTED, T_REG),
        ("x > 0", "(1, e_const)", DISCHARGED, T_RANGE),
        ("x # 0", "(1, e_const)", DISCHARGED, T_RANGE),
        ("D[x]((ln x)^2/2) == ln x / x", "(1, e_const)", DISCHARGED,
         T_DERIV_FIELD),
        ("e_const > 0", "true", DISCHARGED, T_LINEAR_E),
        ("1 > 0", "true", DISCHARGED, T_NORM_NUM),
    ],
    "S3-ring": [
        ("x # 0", "[1, e_const]", DISCHARGED, T_RANGE),
        ("x > 0", "[1, e_const]", DISCHARGED, T_RANGE),
        ("1 <= e_const", "true", DISCHARGED, T_LINEAR_E),
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("(ln x)^2/2 in C^0([1, e_const])", "[1, e_const]", ADMITTED, T_REG),
        ("(ln x)^2/2 in C^1((1, e_const))", "(1, e_const)", ADMITTED, T_REG),
        ("ln x / x in C^0([1, e_const])", "[1, e_const]", ADMITTED, T_REG),
        ("x > 0", "(1, e_const)", DISCHARGED, T_RANGE),
        ("D[x]((ln x)^2/2) == ln x / x", "(1, e_const)", DISCHARGED,
         T_DERIV_RING),
        ("e_const > 0", "true", DISCHARGED, T_LINEAR_E),
        ("1 > 0", "true", DISCHARGED, T_NORM_NUM),
    ],
}

# N after discharge: ftc's three Reg premises, in every proof. Each
# remaining admission's reason is REASON_REG, and none is tagged none.
DISCHARGE_ADMISSIONS = {
    "S1": 3,       # three regularity (unchanged)
    "S2": 3,       # three regularity (unchanged)
    "S3": 3,       # three regularity (was 9)
    "S3-ring": 3,  # three regularity (was 8)
}
DISCHARGE_VERDICTS = {name: VERDICT.format(n=n)
                      for name, n in DISCHARGE_ADMISSIONS.items()}

# The data cross-checks itself when imported, as p1_expected's does.
for _p, _rows in DISCHARGE_FINAL_TRACKER.items():
    _pre = {(r[0], r[1]): r for r in FINAL_TRACKER[_p]}
    assert set(_pre) == {(r[0], r[1]) for r in _rows}, _p
    for _r in _rows:
        _old = _pre[(_r[0], _r[1])]
        assert _r[3] == _old[3], (_p, _r)
        if _old[2] == ADMITTED and _old[3] != T_REG:
            assert _r[2] == DISCHARGED and (_r[0], _r[1]) in \
                DISCHARGE_EXPECTED[_p], (_p, _r)
        else:
            assert _r[2] == _old[2], (_p, _r)
    assert sum(r[2] == ADMITTED for r in _rows) == \
        DISCHARGE_ADMISSIONS[_p], _p
    assert all(r[3] == T_REG for r in _rows if r[2] == ADMITTED), _p
    for _sid, _obs in DISCHARGE_OBLIGATIONS[_p].items():
        for _ob in _obs:
            _fin = [r for r in _rows if (r[0], r[1]) == (_ob[0], _ob[1])]
            assert _fin and _fin[0][2] == _ob[3], (_p, _sid, _ob)
del _p, _rows, _pre, _r, _old, _sid, _obs, _ob, _fin

# The two stage-0 seams (ARCHITECTURE.md §9, S0_SEAMS) after discharge:
# no_ln_former removes S3's x > 0 @ [1, e_const] and e_const > 0 and 1 > 0,
# all discharged, so S3's N stays 3 and only the lists catch it;
# d_ln_emits_nothing removes x > 0 @ (1, e_const), discharged, the same.
# S1 and S2 are untouched by both, as before.
DISCHARGE_S0_SEAMS = {
    "no_ln_former": {"admissions": {"S1": 3, "S2": 3, "S3": 3,
                                    "S3-ring": 3},
                     "caught_by": "the obligation lists only; N no longer "
                                  "moves"},
    "d_ln_emits_nothing": {"admissions": {"S1": 3, "S2": 3, "S3": 3,
                                          "S3-ring": 3},
                           "caught_by": "the obligation lists only; N no "
                                        "longer moves"},
}
