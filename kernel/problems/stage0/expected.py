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
    # int_subst spec 2026-09-24
    "PF18": "The first problem file whose reference proof uses int_subst "
            "is kernel/problems/stage1/SUB1.json, id stage1.SUB1, in "
            "PF1-PF2's format with one more move shape (p1_expected "
            "INT_SUBST_ARGS: var, sub, new_var, lo, hi as strings, check, "
            "facts). It is not in stage0/, because item 7's floor requires "
            "every *.json there to be one PROOF_FILES names, and adding one "
            "before the move exists would turn the suite red. Its expected "
            "data is this file's section 12, keyed separately "
            "(INT_SUBST_*), so no stage-0 table gains a key. STAGE0.md gap "
            "5 is why it exists: an authored proof would otherwise hand F "
            "straight to ftc and never exercise the move",
    "PF19": "SUB1 is Int_0^1 x*sqrt(1 - x) = 4/15 by x := 1 - t^2 over t "
            "from 1 to 0: §8.5's 'sqrt(u) inside f(.) -> u = t^2' row with "
            "u = 1 - x, so substitution is the natural route. phi is "
            "decreasing with literal ends, so the new integral is reversed "
            "and E4 owes no orientation (p1_expected E40); the answer's "
            "sign rests on keeping the limits as given (SUB1-W2, and the "
            "planted bug int_subst_sorts_new_limits). sqrt_sq then fires "
            "through a ring-normalised argument, 1 - (1 - t^2) = t^2 (§18 "
            "Q21). F is written (2/5)*t^5 - (2/3)*t^3 so that its "
            "coefficients are x-free literals, d_const fires on them and "
            "nothing is routed (PF8 would otherwise add route_div's 5 # 0 "
            "and 3 # 0 sources). Rejected candidates: S2 by u := x^2 "
            "(reverse substitution is out, p1_expected E37); S2 by x := "
            "sqrt u (refused, PF20); and Int_0^4 1/(1 + sqrt x) = "
            "4 - 2 ln 3 by x := t^2, the more familiar example, whose "
            "installation owes 1 + sqrt x # 0 @ [0, 4], which no §5.3 "
            "method closes and F3 cannot refute (FINDINGS), so it would be "
            "admitted tagged none and fail the no-none check. (Owner "
            "answers 2026-09-24: the first and last are now problem files, "
            "S2R by PF21 and SUB2 by PF22; SUB1 is kept, as the decreasing "
            "literal-ended case)",
    "PF20": "S2 keeps its reference proof (ftc with F := exp(x^2)/2) and "
            "gains no substitution route. Reverse substitution is out "
            "(E37), and the forward x := sqrt u over [0, 1] is refused "
            "(INT_SUBST_S0_REFUSALS S2-SUB-W1): phi = sqrt u is not C^1 at "
            "0, and d_sqrt's u > 0 on the closed range is decided false at "
            "u = 0. The refusal is correct under §6.4 as stated (phi in "
            "C^1([a, b])), though the transformed integrand, after "
            "cancelling sqrt u, is continuous; that cancellation is what "
            "reverse substitution would do. (Owner answers 2026-09-24: S2 "
            "keeps S2.json unchanged, and gains the reverse route in "
            "stage1/S2R.json, PF21; S2-SUB-W1 is unchanged)",
    # int_subst spec 2026-09-24, owner answers
    "PF21": "S2R is S2 by reverse substitution (p1_expected E45): u := x^2 "
            "with f := exp(u)/2 and new limits 0 and 1. The learner supplies "
            "f as a term in u; the kernel substitutes x^2 for u, "
            "multiplies by deriv's 2*x^1*1, and ring checks x*exp(x^2) == "
            "(exp(x^2)/2)*(2*x^1*1) on [0, 1]. It is a separate file "
            "because S2.json, in stage0/, is asserted by item 7 as it "
            "stands, and its loader does not know the move. The proof then "
            "is S2's own tail on u: ftc with F := exp(u)/2, exp_one, "
            "exp_zero and the same close. Its N is 4, not 5: F is the "
            "integrand, so ftc's F in C^0 and f in C^0 are one key (E8). "
            "S2R-W1 is the missing 1/2, refused by the integrand check with "
            "its residual",
    "PF22": "SUB2 is Int_0^4 1/(1 + sqrt x) = 4 - 2 ln 3 by x := t^2 over "
            "[0, 2], the example PF19 had to reject. The owner's sqrt_nonneg "
            "(p1_expected E49) closes 1 + sqrt x # 0 @ [0, 4] and, after "
            "the substitution, 1 + sqrt(t^2) # 0 @ [0, 2], each ('linear', "
            "('sqrt_nonneg',)). ftc checks by field, owing 1 + t # 0 on "
            "(0, 2); the answer is stated with ln 3, which ln(1 + 2) is as "
            "an atom. SUB2-W1 keeps the old upper limit, the classic "
            "unchanged-limits error, refused at 4^2 == 4",
    # consolidation spec 2026-09-24
    "PF23": "QC1 is Int_0^1 sqrt(1 - x^2) = pi/4 by x := cos theta over "
            "theta from pi/2 to 0 (p1_expected E55), §5.1's canonical "
            "reversed case, finished. It lives in kernel/problems/"
            "consolidation/, because stage1/'s floor names its files "
            "exactly. Its route: int_subst (flipped, E46), pyth_cos at "
            "(cos theta)^2, sqrt_sq with u := sin theta (owing sin theta >= "
            "0, cite sin_nonneg_on), fact pyth_cos, ftc with F := (theta - "
            "sin theta * cos theta)/2 checked by field with that fact, three "
            "exact-value rewrites, and close pi/4. Its sign products are "
            "1 - x^2 >= 0 at installation and 1 - (cos theta)^2 >= 0 after "
            "the substitution (E53). QC1-W1 drops the fact; QC1-W2 applies "
            "sqrt_sq before pyth_cos",
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
    # int_subst spec 2026-09-24
    "§8.5's recognizer row 'sqrt(u) inside f(.) -> u = t^2' has an "
    "obstacle before any substitution: a sqrt inside a divisor. "
    "Int_0^4 1/(1 + sqrt x) owes 1 + sqrt x # 0 @ [0, 4] at installation, "
    "and nothing decides it: Fourier-Motzkin sees sqrt x as an opaque atom "
    "with no sign fact (only pi and e_const bring one), sign and sign "
    "product see a degree-1 sum, sqrt_pos concludes sqrt a > 0 and not "
    "1 + sqrt a > 0, and F3 cannot evaluate sqrt 4 or sqrt 2. It is true, "
    "and admitted tagged none. A fact sqrt a >= 0 @ a >= 0 read by the "
    "linear method (a schema entry, which E29's Farkas labels exclude), or "
    "a sign rule for sqrt atoms, is what §5.3 would need (PF19). (Owner "
    "answers 2026-09-24: resolved by sqrt_nonneg, p1_expected E49; SUB2 "
    "is that integral, PF22.)",
    "S2's natural substitution has no kernel move: reverse substitution "
    "(u := x^2) is out of int_subst (p1_expected E37), and the forward "
    "x := sqrt u is refused because sqrt is not C^1 at 0 (PF20). ftc "
    "remains S2's only route, which STAGE0.md gap 5 already said of its "
    "reference proof. (Owner answers 2026-09-24: resolved, reverse "
    "substitution is in, p1_expected E45; S2R, PF21.)",
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
    # int_subst spec 2026-09-24
    "int_subst spec 2026-09-24, SymPy 1.14 in scratch: Int_0^1 x sqrt(1 - x) "
    "= 4/15, and so is the transformed Int_1^0 (1 - t^2) sqrt(1 - (1 - "
    "t^2)) (-2t) dt, before and after sqrt_sq; 1 - (1 - t^2) = t^2; the "
    "ends map (1 - 1^2 = 0, 1 - 0^2 = 1); both DERIV outputs are the true "
    "derivatives; F(0) - F(1) = 4/15, and -4/15 with the limits sorted; "
    "SUB1-W1's residual is 1 and SUB1-W2's 8/15; 1 - x >= 0 and t >= 0 on "
    "[0, 1]; S2's x := sqrt u has phi' = 1/(2 sqrt u), unbounded at 0, "
    "though its transformed integrand integrates to (e - 1)/2; Int_0^4 "
    "1/(1 + sqrt x) = 4 - 2 ln 3. SUB1.json loads, and its goal, step ids "
    "and moves match INT_SUBST_STEPS; every string in section 12 parses "
    "with terms.py's parser and round-trips, the echo is the printer's, "
    "and both goal_after trees equal the ones built with terms.subst",
    # int_subst spec 2026-09-24, owner answers
    "int_subst spec 2026-09-24, owner answers, SymPy 1.14 in scratch: S2R's identity x e^(x^2) = "
    "(e^(x^2)/2)(2x), Int_0^1 e^u/2 = (e - 1)/2, (e^u/2)' = e^u/2, its "
    "deriv output and F(1) - F(0); S2R-W1's residual -x e^(x^2); SUB2's "
    "4 - 2 ln 3 before and after x := t^2, 2^2 = 4, F' = 2t/(1 + t), the "
    "deriv output, F(2) - F(0); SUB2-W1's 4^2 - 4 = 12. All three JSON "
    "files load and match INT_SUBST_STEPS; every string parses and "
    "round-trips; each echo is the printer's; each int_subst and ftc "
    "goal_after equals its rebuilt tree, and S2R's identity key "
    "body == f[u := x^2]*g'",
    # consolidation spec 2026-09-24
    "consolidation spec 2026-09-24, SymPy 1.14 in scratch: QC1's value, ends, flipped integral, "
    "factorisations, sqrt(sin^2) = sin on [0, pi/2], F' = sin^2 with "
    "pyth_cos and not without it (QC1-W1's residual), F(pi/2) - F(0) = "
    "pi/4. QC1.json loads and matches CONSOLIDATION_STEPS; every string "
    "parses and round-trips; every goal_after equals its rebuilt tree",
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
    # int_subst spec 2026-09-24: additions only, no existing value changed,
    # nothing new asserted until the build (p1_expected INT_SUBST_SWITCH).
    ("section 12 (new): INT_SUBST_PROOF_FILES, INT_SUBST_GOALS, "
     "INT_SUBST_ECHO, INT_SUBST_STEPS, INT_SUBST_THEOREMS, INT_SUBST_DERIV, "
     "INT_SUBST_OBLIGATIONS, INT_SUBST_EXPECTED, INT_SUBST_FINAL_TRACKER, "
     "INT_SUBST_ADMISSIONS, INT_SUBST_VERDICTS, INT_SUBST_ANSWERS, "
     "INT_SUBST_NUMERIC, INT_SUBST_WRONG_ANSWERS, INT_SUBST_S0_REFUSALS; "
     "kernel/problems/stage1/SUB1.json (new)",
     "no problem file used int_subst",
     "SUB1, Int_0^1 x*sqrt(1 - x) = 4/15 by x := 1 - t^2 over t from 1 to "
     "0, 'Proved modulo 5 admissions', with two wrong answers (limits in "
     "increasing order; the lost sign) and S2's forward substitution "
     "x := sqrt u refused at d_sqrt's u > 0 @ [0, 1]",
     "WHAT.md 'Start here' item 1 and the task's item 4: a problem where "
     "substitution is the natural route, derived by hand before any code "
     "under p1_expected's INT_SUBST_RULE",
     "hand derivation; import-time cross-check; scratch SymPy and parser "
     "checks (VERIFIED, last entry)"),
    ("DECISIONS PF18-PF20 (new), FINDINGS (two appended), VERIFIED (one "
     "appended)",
     "none",
     "PF18 where the file lives and why; PF19 why SUB1 and not S2 or "
     "Int_0^4 1/(1 + sqrt x); PF20 S2 unchanged; the findings: a sqrt in "
     "a divisor has no deciding method, and S2's substitution has no "
     "kernel move",
     "int_subst spec 2026-09-24",
     "scratch run 2026-09-24, SymPy 1.14"),
    # int_subst spec 2026-09-24, owner answers: additions and text notes only; SUB1, S2-SUB-W1 and every
    # stage-0 value are unchanged.
    ("section 12: S2R and SUB2 added to every INT_SUBST_* table, "
     "S2R-W1 and SUB2-W1 appended to INT_SUBST_WRONG_ANSWERS, a second "
     "cross-check over all three files; kernel/problems/stage1/S2R.json "
     "and SUB2.json (new)",
     "SUB1 was the only int_subst problem file",
     "S2R: S2 by reverse u := x^2, 'Proved modulo 4 admissions' (ftc's F "
     "in C^0 is its f in C^0); SUB2: Int_0^4 1/(1 + sqrt x) = 4 - 2 ln 3 "
     "by x := t^2, 'Proved modulo 5 admissions', its divisors closed by "
     "sqrt_nonneg",
     "the owner's answers 1 and 5 (p1_expected E45, E49)",
     "hand derivation under the amended INT_SUBST_RULE and SQRT_FACT_RULE; "
     "import-time cross-check; scratch SymPy and parser checks (VERIFIED)"),
    ("DECISIONS PF19 and PF20 (a closing note each), PF21 and PF22 (new); "
     "FINDINGS, the two int_subst entries (a resolution note each); "
     "VERIFIED, one entry appended",
     "PF19 rejected S2 by u := x^2 and Int_0^4 1/(1 + sqrt x); PF20 left S2 "
     "with ftc only; the findings named a sqrt divisor no method decides "
     "and S2's missing move",
     "both rejected candidates are now problem files; both findings "
     "resolved by the owner's answers",
     "int_subst spec 2026-09-24, owner answers",
     "p1_expected E45 and E49"),
    # int_subst review 2026-09-24: re-traced, nothing changed
    ("section 12 and every stage-0 table (no change)",
     "none",
     "none: no stage-0 or stage-1 key is a false key without a refuting "
     "point among the old candidates, so p1_expected E50's roots, walked "
     "after every existing candidate, change no status, tag, message or "
     "N; S2-SUB-W1's u > 0 @ [0, 1] is still refused at u = 0, the first "
     "candidate",
     "int_subst review 2026-09-24: p1_expected E50 and F3_ROOTS_CHANGES",
     "hand re-trace of every key in section 12 and sections 4-11"),
    # consolidation spec 2026-09-24: additions only
    ("section 13 (new): the CONSOLIDATION_* tables for QC1; "
     "kernel/problems/consolidation/QC1.json (new); DECISIONS PF23 (new); "
     "VERIFIED (one appended)",
     "none",
     "QC1: 14 keys, 5 admitted (regularity), 'Proved modulo 5 admissions'; "
     "two wrong answers",
     "consolidation spec 2026-09-24: p1_expected E53-E55",
     "hand derivation; import-time cross-check; scratch SymPy and parser "
     "checks; QC1's s1 on today's kernel"),
    ("sections 4-12 (no change)",
     "none",
     "none: no stage-0 or stage-1 key is non-strict and first closed by the "
     "new sign product, and none holds a cos or sin atom outside a Reg "
     "judgement",
     "consolidation spec 2026-09-24: p1_expected E53 and E54, CONSOLIDATION_CHANGES",
     "hand re-trace of every key"),
    # consolidation spec 2026-09-24, owner answers: re-traced, nothing changed
    ("every table (no change)",
     "none",
     "none: no stage-0, stage-1 or consolidation file has a symbolic "
     "reversed range; S3's 1 <= e_const is the same key under E56, "
     "discharged the same way; SUB1's and S2R's literal ranges are ordered "
     "by norm_num as before; QC1's int_subst keeps E46's flip",
     "consolidation spec 2026-09-24, owner answers: p1_expected E56",
     "hand re-trace of every range in sections 4-13"),
    ("QC1 s3, CONSOLIDATION_EXPECTED and CONSOLIDATION_FINAL_TRACKER: sin theta >= 0 @ [0, pi/2]",
     "tag ('cite', ('sin_nonneg_on', 'pi_pos')) -> ('cite', ('sin_nonneg_on',)); the child theta <= pi's certificate -> _farkas({GOAL: 1, LO(0): 1, HI(0): 2})",
     "the consolidation build showed the child is closed by the range alone: (theta - pi, strict) + (theta - 0) + 2*(pi/2 - theta) = 0, strict, so pi_pos is unneeded and TAG_RULES' deletion filter drops sign facts first. Checked by the main session",
     "adjudicated during implementation"),
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

# ---------------------------------------------------------------------------
# 12. int_subst in a problem file (int_subst spec 2026-09-24)
#
# p1_expected's section 12 states the move (INT_SUBST_RULE, E36-E44); this is
# a problem file's data under it, derived by hand the same way, without
# reading kernel.py, and written after discharge was wired, so only the
# post-discharge values exist. PF18-PF20 give the choices. The file is
# kernel/problems/stage1/SUB1.json, not in stage0/, because item 7's floor
# requires every *.json in stage0/ to be one PROOF_FILES names (PF18).
# Nothing here is asserted until the build (p1_expected INT_SUBST_SWITCH).
#
# Restated from p1_expected so this file stands alone (values verbatim).
T_SIGN = ("sign", ())
T_RING = ("ring", ())
S_SQRT_SQ = "rewrite_hyp"
S_SUBST_LO, S_SUBST_HI = "int_subst_lo", "int_subst_hi"
S_SUBST_C1, S_SUBST_C0 = "int_subst_phi_C1", "int_subst_f_C0"
OBLIGATION_DECIDED_FALSE = "obligation-decided-false"


def HI(i):
    return ("dom", i, "hi")


def _sos(const, squares, sense=None):
    return {"method": "sign", "sense": sense, "const": const,
            "squares": tuple(squares)}


def _point(key, reading, **values):
    """p1_expected's F3 message parts, without exact values."""
    return ("point", {"key": key, "point": dict(sorted(values.items())),
                      "reading": reading})


# Paths relative to kernel/problems/.
INT_SUBST_PROOF_FILES = {"SUB1": ("stage1/SUB1.json", "reference_proof")}
INT_SUBST_GOALS = {"SUB1": "Int[x = 0 .. 1] x*sqrt(1 - x) == ?A"}
INT_SUBST_ECHO = {"SUB1": "Int[x = 0 .. 1] x*sqrt(1 - x) == ?A"}

SUB1_S1 = ("Int[t = 1 .. 0] (1 - t^2)*sqrt(1 - (1 - t^2))"
           "*(0 + (0*t^2 + (-1)*(2*t^1*1))) == ?A")
SUB1_S2 = "Int[t = 1 .. 0] (1 - t^2)*t*(0 + (0*t^2 + (-1)*(2*t^1*1))) == ?A"
# F[t := b] - F[t := a] with b = hi = 0 and a = lo = 1 (E4 orders the literal
# ends for the premises, and ftc keeps the limits as written)
SUB1_AFTER_FTC = "(2/5)*0^5 - (2/3)*0^3 - ((2/5)*1^5 - (2/3)*1^3) == ?A"
SUB1_F = "(2/5)*t^5 - (2/3)*t^3"
SUB1_F_INTEGRAND = "(1 - t^2)*t*(0 + (0*t^2 + (-1)*(2*t^1*1)))"

INT_SUBST_STEPS = {
    "SUB1": [
        {"id": "s1", "move": "int_subst", "goal_after": SUB1_S1},
        # sqrt_sq with u := t at sqrt(1 - (1 - t^2)): ring_nf of the
        # argument is t^2 (REWRITE_RULE step 3), and t is bound by the
        # enclosing Int (step 6)
        {"id": "s2", "move": "rewrite", "occurrences": 1,
         "goal_after": SUB1_S2},
        {"id": "s3", "move": "ftc", "goal_after": SUB1_AFTER_FTC},
        # ring over literals: 0 - (2/5 - 2/3) = 4/15
        {"id": "s4", "move": "close", "goal_after": None},
    ],
}
INT_SUBST_THEOREMS = {"SUB1": "Int[x = 0 .. 1] x*sqrt(1 - x) == 4/15"}

# deriv (E12) at int_subst's step 10, on the closed [0, 1], and in ftc
INT_SUBST_DERIV = {
    ("SUB1", "s1"): {
        "var": "t", "F": "1 - t^2",
        "trace": [("d_add", "1 - t^2", ()), ("d_const", "1", ()),
                  ("route_neg", "-t^2", ()), ("d_mul", "-1*t^2", ()),
                  ("d_const", "-1", ()), ("d_pow_int", "t^2", ()),
                  ("d_var", "t", ())],
        "output": "0 + (0*t^2 + (-1)*(2*t^1*1))",
        "emits": (),
    },
    # PF19: F's coefficients are literal fractions, x-free, so d_const
    # fires on them and nothing is routed (no route_div, unlike S2 and S3)
    ("SUB1", "s3"): {
        "var": "t", "F": SUB1_F,
        "trace": [("d_add", SUB1_F, ()), ("d_mul", "(2/5)*t^5", ()),
                  ("d_const", "2/5", ()), ("d_pow_int", "t^5", ()),
                  ("d_var", "t", ()), ("route_neg", "-((2/3)*t^3)", ()),
                  ("d_mul", "-1*((2/3)*t^3)", ()), ("d_const", "-1", ()),
                  ("d_mul", "(2/3)*t^3", ()), ("d_const", "2/3", ()),
                  ("d_pow_int", "t^3", ()), ("d_var", "t", ())],
        "output": ("0*t^5 + (2/5)*(5*t^4*1) + (0*((2/3)*t^3)"
                   " + (-1)*(0*t^3 + (2/3)*(3*t^2*1)))"),
        "emits": (),
    },
}

# Per step, after discharge. Hand-derived (p1_expected INT_SUBST_RULE):
#   goal: sqrt(1 - x) owes 1 - x >= 0 on the literal range [0, 1], by range
#     on the upper end: (x - 1, strict) + (1 - x) = 0 with a strict
#     constraint. No orientation (literal ends).
#   s1: step 8, the limits 1 and 0 owe nothing and are literal, so I' is
#     [0, 1] and no orientation is owed (E40). Step 9, 1 - t^2 owes
#     nothing. Step 10, deriv emits nothing. Step 11, 1 - 1^2 == 0 and
#     1 - 0^2 == 1 by ring. Step 12, the two Reg, the C^0 one on the
#     composed integrand. Step 13, the new integrand's sqrt owes
#     1 - (1 - t^2) >= 0 on [0, 1]: FM sees t^2 as opaque and fails, and
#     sign closes its ring normal form t^2 (E20).
#   s2: sqrt_sq's t >= 0 on [0, 1], by range on the lower end; R = t has no
#     former; no orientation (literal).
#   s3: F's 2/5 and 2/3 owe 5 # 0 and 3 # 0 (literal); the premises on
#     [0, 1] and (0, 1); ring's check emits nothing; the new goal's
#     fractions are the same two keys.
#   s4: the value 4/15 owes 15 # 0.
INT_SUBST_OBLIGATIONS = {
    "SUB1": {
        "goal": [
            ("1 - x >= 0", "[0, 1]", (S_FORMER,), DISCHARGED, T_RANGE, True),
        ],
        "s1": [
            ("1 - 1^2 == 0", "true", (S_SUBST_LO,), DISCHARGED, T_RING, True),
            ("1 - 0^2 == 1", "true", (S_SUBST_HI,), DISCHARGED, T_RING, True),
            ("1 - t^2 in C^1([0, 1])", "[0, 1]", (S_SUBST_C1,), ADMITTED,
             T_REG, True),
            ("(1 - t^2)*sqrt(1 - (1 - t^2)) in C^0([0, 1])", "[0, 1]",
             (S_SUBST_C0,), ADMITTED, T_REG, True),
            ("1 - (1 - t^2) >= 0", "[0, 1]", (S_FORMER,), DISCHARGED, T_SIGN,
             True),
        ],
        "s2": [
            ("t >= 0", "[0, 1]", (S_SQRT_SQ,), DISCHARGED, T_RANGE, True),
        ],
        "s3": [
            ("5 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
            ("3 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
            (SUB1_F + " in C^0([0, 1])", "[0, 1]", (S_FTC_C0F,), ADMITTED,
             T_REG, True),
            (SUB1_F + " in C^1((0, 1))", "(0, 1)", (S_FTC_C1F,), ADMITTED,
             T_REG, True),
            ("D[t](" + SUB1_F + ") == " + SUB1_F_INTEGRAND, "(0, 1)",
             (S_FTC_D,), DISCHARGED, T_DERIV_RING, True),
            (SUB1_F_INTEGRAND + " in C^0([0, 1])", "[0, 1]", (S_FTC_C0f,),
             ADMITTED, T_REG, True),
        ],
        "s4": [
            ("15 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
        ],
    },
}

INT_SUBST_EXPECTED = {
    "SUB1": {
        ("1 - x >= 0", "[0, 1]"): (T_RANGE, _farkas({GOAL: "1", HI(0): "1"})),
        ("1 - (1 - t^2) >= 0", "[0, 1]"): (T_SIGN,
                                          _sos("0", [("1", "t", 2)])),
        ("t >= 0", "[0, 1]"): (T_RANGE, _RANGE_LO),
    },
}

INT_SUBST_FINAL_TRACKER = {
    "SUB1": [
        ("1 - x >= 0", "[0, 1]", DISCHARGED, T_RANGE),
        ("1 - 1^2 == 0", "true", DISCHARGED, T_RING),
        ("1 - 0^2 == 1", "true", DISCHARGED, T_RING),
        ("1 - t^2 in C^1([0, 1])", "[0, 1]", ADMITTED, T_REG),
        ("(1 - t^2)*sqrt(1 - (1 - t^2)) in C^0([0, 1])", "[0, 1]", ADMITTED,
         T_REG),
        ("1 - (1 - t^2) >= 0", "[0, 1]", DISCHARGED, T_SIGN),
        ("t >= 0", "[0, 1]", DISCHARGED, T_RANGE),
        ("5 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("3 # 0", "true", DISCHARGED, T_NORM_NUM),
        (SUB1_F + " in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
        (SUB1_F + " in C^1((0, 1))", "(0, 1)", ADMITTED, T_REG),
        ("D[t](" + SUB1_F + ") == " + SUB1_F_INTEGRAND, "(0, 1)", DISCHARGED,
         T_DERIV_RING),
        (SUB1_F_INTEGRAND + " in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
        ("15 # 0", "true", DISCHARGED, T_NORM_NUM),
    ],
}

# N: int_subst's two regularity premises and ftc's three (p1_expected E43:
# 3 + 2k). None is tagged none.
INT_SUBST_ADMISSIONS = {"SUB1": 5}
INT_SUBST_VERDICTS = {name: VERDICT.format(n=n)
                      for name, n in INT_SUBST_ADMISSIONS.items()}
INT_SUBST_ANSWERS = {"SUB1": "4/15"}
INT_SUBST_NUMERIC = {"SUB1": 0.26666666666666666}  # 4/15

# Refusals, in WRONG_ANSWERS' shape. Each emits nothing (E13).
INT_SUBST_WRONG_ANSWERS = [
    {"id": "SUB1-W1",
     "what": "SUB1's substitution with the new limits in increasing order, "
             "lo 0 and hi 1: phi(0) = 1 is not the lower limit 0",
     "goal": INT_SUBST_GOALS["SUB1"],
     "move": ("int_subst", {"var": "x", "sub": "1 - t^2", "new_var": "t",
                            "lo": "0", "hi": "1", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-endpoint-mismatch",
     "message": ("int-subst-endpoint-mismatch",
                 {"image": "1 - 0^2", "limit": "0", "end": "lower"}),
     "residual": "1 - 0^2 - 0",
     "compare": ("ring", ())},
    {"id": "SUB1-W2",
     "what": "SUB1 closed with -4/15, the sign a learner loses by reading "
             "the reversed limits [1, 0] as [0, 1]",
     "state": ("SUB1", "s3"),
     "move": ("close", {"value": "-4/15", "check": "ring", "facts": []}),
     "refusal": "close-check-failed",
     "residual": SUB1_AFTER_FTC.split(" == ")[0] + " - (-4/15)",
     "compare": ("ring", ())},
]

# PF20. S2's substitution, as a learner would try it forward: refused, and
# correctly, because sqrt is not C^1 at 0. Before the refusal: sqrt u owes
# u >= 0 on [0, 1] (range, discharged); then deriv's d_sqrt owes u > 0 on
# the CLOSED [0, 1] (p1_expected E38), which F3 decides false at u = 0.
# (Were it not, the upper endpoint sqrt 1 == 1 would still fail: sqrt 1
# has no exact value and ring reads it as an atom.)
INT_SUBST_S0_REFUSALS = [
    {"id": "S2-SUB-W1",
     "what": "S2 by x := sqrt u over u in [0, 1], the forward form of the "
             "learner's u = x^2",
     "goal": GOALS["S2"],
     "move": ("int_subst", {"var": "x", "sub": "sqrt u", "new_var": "u",
                            "lo": "0", "hi": "1", "check": "ring",
                            "facts": []}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("u > 0 @ [0, 1]", "0 > 0", u="0"),
     "deriv_trace": [("d_sqrt", "sqrt u", ("u > 0 @ [0, 1]",)),
                     ("d_var", "u", ())]},
]

# The data cross-checks itself when imported, as section 11 does.
for _p, _rows in INT_SUBST_FINAL_TRACKER.items():
    _keys = [(r[0], r[1]) for r in _rows]
    assert len(set(_keys)) == len(_keys), _p
    _seen = set()
    for _sid, _obs in INT_SUBST_OBLIGATIONS[_p].items():
        for _ob in _obs:
            _fin = [r for r in _rows if (r[0], r[1]) == (_ob[0], _ob[1])]
            assert _fin and _fin[0][2:] == (_ob[3], _ob[4]), (_p, _sid, _ob)
            assert _ob[5] == ((_ob[0], _ob[1]) not in _seen), (_p, _sid, _ob)
        _seen |= {(o[0], o[1]) for o in _obs}
    assert _seen == set(_keys), _p
    assert [s["id"] for s in INT_SUBST_STEPS[_p]] == \
        [k for k in INT_SUBST_OBLIGATIONS[_p] if k != "goal"], _p
    assert sum(r[2] == ADMITTED for r in _rows) == INT_SUBST_ADMISSIONS[_p]
    assert all(r[3] == T_REG for r in _rows if r[2] == ADMITTED), _p
    for _k, (_tag, _c) in INT_SUBST_EXPECTED[_p].items():
        assert [r for r in _rows if (r[0], r[1]) == _k][0][2:] == \
            (DISCHARGED, _tag), (_p, _k)
del _p, _rows, _keys, _seen, _sid, _obs, _ob, _fin, _k, _tag, _c

# --- Owner answers 2026-09-24 (int_subst spec 2026-09-24, owner answers) ---
#
# Two more problem files in stage1/: S2R, S2 by the reverse substitution
# u := x^2 (p1_expected E45, PF21), and SUB2, Int_0^4 1/(1 + sqrt x) by
# x := t^2, which installs only because sqrt_nonneg now closes its divisor
# (E49, PF22). SUB1 and S2-SUB-W1 are unchanged: SUB1's ends are literal,
# so E46 keeps them, and no key of either holds a sqrt atom.
S_SUBST_INT = "int_subst_integrand"
T_LINEAR_SQRT = ("linear", ("sqrt_nonneg",))


def SQRT(u):
    return ("fact", "sqrt_nonneg", u)


INT_SUBST_PROOF_FILES.update({
    "S2R": ("stage1/S2R.json", "reference_proof"),
    "SUB2": ("stage1/SUB2.json", "reference_proof"),
})
INT_SUBST_GOALS.update({
    "S2R": GOALS["S2"],
    "SUB2": "Int[x = 0 .. 4] 1/(1 + sqrt x) == ?A",
})
INT_SUBST_ECHO.update({
    "S2R": ECHO["S2"],
    "SUB2": "Int[x = 0 .. 4] 1/(1 + sqrt x) == ?A",
})

S2R_S1 = "Int[u = 0 .. 1] exp(u)/2 == ?A"
S2R_AFTER_FTC = "exp(1)/2 - exp(0)/2 == ?A"
S2R_IDENTITY = "x*exp(x^2) == (exp(x^2)/2)*(2*x^1*1)"
SUB2_S1 = "Int[t = 0 .. 2] (1/(1 + sqrt(t^2)))*(2*t^1*1) == ?A"
SUB2_S2 = "Int[t = 0 .. 2] (1/(1 + t))*(2*t^1*1) == ?A"
SUB2_F = "2*t - 2*ln(1 + t)"
SUB2_F_INTEGRAND = "(1/(1 + t))*(2*t^1*1)"
SUB2_AFTER_FTC = "2*2 - 2*ln(1 + 2) - (2*0 - 2*ln(1 + 0)) == ?A"

INT_SUBST_STEPS.update({
    "S2R": [
        # reverse mode (E45): the new integral is f over the new limits
        {"id": "s1", "move": "int_subst", "goal_after": S2R_S1},
        {"id": "s2", "move": "ftc", "goal_after": S2R_AFTER_FTC},
        {"id": "s3", "move": "rewrite", "occurrences": 1,
         "goal_after": "e_const/2 - exp(0)/2 == ?A"},
        {"id": "s4", "move": "rewrite", "occurrences": 1,
         "goal_after": "e_const/2 - 1/2 == ?A"},
        {"id": "s5", "move": "close", "goal_after": None},
    ],
    "SUB2": [
        {"id": "s1", "move": "int_subst", "goal_after": SUB2_S1},
        {"id": "s2", "move": "rewrite", "occurrences": 1,
         "goal_after": SUB2_S2},
        {"id": "s3", "move": "ftc", "goal_after": SUB2_AFTER_FTC},
        {"id": "s4", "move": "rewrite", "occurrences": 1,
         "goal_after": "2*2 - 2*ln(1 + 2) - (2*0 - 2*0) == ?A"},
        # ring: ln(1 + 2) and ln 3 are one atom (§6.2)
        {"id": "s5", "move": "close", "goal_after": None},
    ],
})
INT_SUBST_THEOREMS.update({
    "S2R": THEOREMS["S2"],
    "SUB2": "Int[x = 0 .. 4] 1/(1 + sqrt x) == 4 - 2*ln 3",
})

INT_SUBST_DERIV.update({
    # reverse mode's g' on the closed old range (E45)
    ("S2R", "s1"): {"var": "x", "F": "x^2",
                    "trace": [("d_pow_int", "x^2", ()), ("d_var", "x", ())],
                    "output": "2*x^1*1", "emits": ()},
    # S2's own pattern (PF8: u/2 routed, owing 2 # 0)
    ("S2R", "s2"): {"var": "u", "F": "exp(u)/2",
                    "trace": [("route_div", "exp(u)/2", ("2 # 0",)),
                              ("d_mul", "exp(u)*(1/2)", ()),
                              ("d_exp", "exp(u)", ()), ("d_var", "u", ()),
                              ("d_const", "1/2", ())],
                    "output": "exp(u)*1*(1/2) + exp(u)*0",
                    "emits": ("2 # 0",)},
    ("SUB2", "s1"): {"var": "t", "F": "t^2",
                     "trace": [("d_pow_int", "t^2", ()), ("d_var", "t", ())],
                     "output": "2*t^1*1", "emits": ()},
    ("SUB2", "s3"): {
        "var": "t", "F": SUB2_F,
        "trace": [("d_add", SUB2_F, ()), ("d_mul", "2*t", ()),
                  ("d_const", "2", ()), ("d_var", "t", ()),
                  ("route_neg", "-(2*ln(1 + t))", ()),
                  ("d_mul", "-1*(2*ln(1 + t))", ()), ("d_const", "-1", ()),
                  ("d_mul", "2*ln(1 + t)", ()), ("d_const", "2", ()),
                  ("d_ln", "ln(1 + t)", ("1 + t > 0 @ (0, 2)",)),
                  ("d_add", "1 + t", ()), ("d_const", "1", ()),
                  ("d_var", "t", ())],
        "output": ("0*t + 2*1 + (0*(2*ln(1 + t)) + (-1)*(0*ln(1 + t)"
                   " + 2*((0 + 1)/(1 + t))))"),
        "emits": ("1 + t > 0 @ (0, 2)",)},
})

# Per step, after discharge. Hand-derived (p1_expected INT_SUBST_RULE):
#   S2R s1 (reverse): I = [0, 1] is literal, so no orientation; the new
#     limits 0 and 1 are literal, so E46 keeps them. Step 9: g = x^2 owes
#     nothing, f(g(x)) = exp(x^2)/2 owes 2 # 0 (closed: true). Step 10:
#     g' = 2*x^1*1. Step 11: x*exp(x^2) == (exp(x^2)/2)*(2*x^1*1) on
#     [0, 1] by ring (division by the literal 2 is a coefficient). Step 12:
#     0^2 == 0 and 1^2 == 1 by ring. Step 13: the two Reg on [0, 1]. Step
#     14: f's /2 again (merged).
#   S2R s2: F = exp(u)/2 IS the integrand, so ftc's F in C^0 and f in C^0
#     premises are one key with two sources (E8), and ftc adds two
#     admissions, not three. deriv's route_div and F's and the new goal's
#     /2 are the one 2 # 0.
#   SUB2 goal: 1 + sqrt x # 0 @ [0, 4] by E49's label, (-(1 + sqrt x)) +
#     sqrt x = -1, no domain item used: ('linear', ('sqrt_nonneg',)); sqrt
#     x's own x >= 0 by range.
#   SUB2 s1: P1.1-sheet's s1 on [0, 2] with literal ends (no orientation,
#     no 2 # 0), and the composed divisor 1 + sqrt(t^2) # 0 closed as the
#     goal's was, the atom sqrt(t^2) matched by ring_nf of t^2.
#   SUB2 s3: F's ln(1 + t) on [0, 2]; d_ln's on (0, 2); field's 1 + t
#     divisor (in deriv's (0 + 1)/(1 + t) and in the integrand) on (0, 2);
#     the new goal's two literal ln arguments.
INT_SUBST_OBLIGATIONS.update({
    "S2R": {
        "goal": [],
        "s1": [
            ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
            (S2R_IDENTITY, "[0, 1]", (S_SUBST_INT,), DISCHARGED,
             T_DERIV_RING, True),
            ("0^2 == 0", "true", (S_SUBST_LO,), DISCHARGED, T_RING, True),
            ("1^2 == 1", "true", (S_SUBST_HI,), DISCHARGED, T_RING, True),
            ("x^2 in C^1([0, 1])", "[0, 1]", (S_SUBST_C1,), ADMITTED, T_REG,
             True),
            ("exp(x^2)/2 in C^0([0, 1])", "[0, 1]", (S_SUBST_C0,), ADMITTED,
             T_REG, True),
        ],
        "s2": [
            ("2 # 0", "true", (S_FORMER, S_ROUTE_DIV), DISCHARGED,
             T_NORM_NUM, False),
            ("exp(u)/2 in C^0([0, 1])", "[0, 1]", (S_FTC_C0F, S_FTC_C0f),
             ADMITTED, T_REG, True),
            ("exp(u)/2 in C^1((0, 1))", "(0, 1)", (S_FTC_C1F,), ADMITTED,
             T_REG, True),
            ("D[u](exp(u)/2) == exp(u)/2", "(0, 1)", (S_FTC_D,), DISCHARGED,
             T_DERIV_RING, True),
        ],
        "s3": [],
        "s4": [],
        "s5": [
            ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False),
        ],
    },
    "SUB2": {
        "goal": [
            ("1 + sqrt x # 0", "[0, 4]", (S_FORMER,), DISCHARGED,
             T_LINEAR_SQRT, True),
            ("x >= 0", "[0, 4]", (S_FORMER,), DISCHARGED, T_RANGE, True),
        ],
        "s1": [
            ("0^2 == 0", "true", (S_SUBST_LO,), DISCHARGED, T_RING, True),
            ("2^2 == 4", "true", (S_SUBST_HI,), DISCHARGED, T_RING, True),
            ("t^2 in C^1([0, 2])", "[0, 2]", (S_SUBST_C1,), ADMITTED, T_REG,
             True),
            ("1/(1 + sqrt(t^2)) in C^0([0, 2])", "[0, 2]", (S_SUBST_C0,),
             ADMITTED, T_REG, True),
            ("1 + sqrt(t^2) # 0", "[0, 2]", (S_FORMER,), DISCHARGED,
             T_LINEAR_SQRT, True),
            ("t^2 >= 0", "[0, 2]", (S_FORMER,), DISCHARGED, T_SIGN, True),
        ],
        "s2": [
            ("t >= 0", "[0, 2]", (S_SQRT_SQ,), DISCHARGED, T_RANGE, True),
        ],
        "s3": [
            ("1 + t > 0", "[0, 2]", (S_FORMER,), DISCHARGED, T_RANGE, True),
            (SUB2_F + " in C^0([0, 2])", "[0, 2]", (S_FTC_C0F,), ADMITTED,
             T_REG, True),
            (SUB2_F + " in C^1((0, 2))", "(0, 2)", (S_FTC_C1F,), ADMITTED,
             T_REG, True),
            (SUB2_F_INTEGRAND + " in C^0([0, 2])", "[0, 2]", (S_FTC_C0f,),
             ADMITTED, T_REG, True),
            ("1 + t > 0", "(0, 2)", (S_D_LN,), DISCHARGED, T_RANGE, True),
            ("1 + t # 0", "(0, 2)", (S_FIELD,), DISCHARGED, T_RANGE, True),
            ("D[t](" + SUB2_F + ") == " + SUB2_F_INTEGRAND, "(0, 2)",
             (S_FTC_D,), DISCHARGED, T_DERIV_FIELD, True),
            ("1 + 2 > 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
            ("1 + 0 > 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
        ],
        "s4": [],
        "s5": [
            ("3 > 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
        ],
    },
})

INT_SUBST_EXPECTED.update({
    "S2R": {},  # nothing a §5.3 method discharges; the rest is in-step
    "SUB2": {
        ("1 + sqrt x # 0", "[0, 4]"): (
            T_LINEAR_SQRT, _farkas({GOAL: "1", SQRT("x"): "1"}, ">")),
        ("x >= 0", "[0, 4]"): (T_RANGE, _RANGE_LO),
        ("1 + sqrt(t^2) # 0", "[0, 2]"): (
            T_LINEAR_SQRT, _farkas({GOAL: "1", SQRT("t^2"): "1"}, ">")),
        ("t^2 >= 0", "[0, 2]"): (T_SIGN, _sos("0", [("1", "t", 2)])),
        ("t >= 0", "[0, 2]"): (T_RANGE, _RANGE_LO),
        ("1 + t > 0", "[0, 2]"): (T_RANGE, _RANGE_LO),
        ("1 + t > 0", "(0, 2)"): (T_RANGE, _RANGE_LO),
        ("1 + t # 0", "(0, 2)"): (T_RANGE, _RANGE_LO_NZ),
    },
})

INT_SUBST_FINAL_TRACKER.update({
    "S2R": [
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        (S2R_IDENTITY, "[0, 1]", DISCHARGED, T_DERIV_RING),
        ("0^2 == 0", "true", DISCHARGED, T_RING),
        ("1^2 == 1", "true", DISCHARGED, T_RING),
        ("x^2 in C^1([0, 1])", "[0, 1]", ADMITTED, T_REG),
        ("exp(x^2)/2 in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
        ("exp(u)/2 in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
        ("exp(u)/2 in C^1((0, 1))", "(0, 1)", ADMITTED, T_REG),
        ("D[u](exp(u)/2) == exp(u)/2", "(0, 1)", DISCHARGED, T_DERIV_RING),
    ],
    "SUB2": [
        ("1 + sqrt x # 0", "[0, 4]", DISCHARGED, T_LINEAR_SQRT),
        ("x >= 0", "[0, 4]", DISCHARGED, T_RANGE),
        ("0^2 == 0", "true", DISCHARGED, T_RING),
        ("2^2 == 4", "true", DISCHARGED, T_RING),
        ("t^2 in C^1([0, 2])", "[0, 2]", ADMITTED, T_REG),
        ("1/(1 + sqrt(t^2)) in C^0([0, 2])", "[0, 2]", ADMITTED, T_REG),
        ("1 + sqrt(t^2) # 0", "[0, 2]", DISCHARGED, T_LINEAR_SQRT),
        ("t^2 >= 0", "[0, 2]", DISCHARGED, T_SIGN),
        ("t >= 0", "[0, 2]", DISCHARGED, T_RANGE),
        ("1 + t > 0", "[0, 2]", DISCHARGED, T_RANGE),
        (SUB2_F + " in C^0([0, 2])", "[0, 2]", ADMITTED, T_REG),
        (SUB2_F + " in C^1((0, 2))", "(0, 2)", ADMITTED, T_REG),
        (SUB2_F_INTEGRAND + " in C^0([0, 2])", "[0, 2]", ADMITTED, T_REG),
        ("1 + t > 0", "(0, 2)", DISCHARGED, T_RANGE),
        ("1 + t # 0", "(0, 2)", DISCHARGED, T_RANGE),
        ("D[t](" + SUB2_F + ") == " + SUB2_F_INTEGRAND, "(0, 2)", DISCHARGED,
         T_DERIV_FIELD),
        ("1 + 2 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("1 + 0 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("3 > 0", "true", DISCHARGED, T_NORM_NUM),
    ],
})

# S2R: int_subst's two Reg and ftc's two (its F in C^0 is its f in C^0);
# SUB2: two and three.
INT_SUBST_ADMISSIONS.update({"S2R": 4, "SUB2": 5})
INT_SUBST_VERDICTS = {name: VERDICT.format(n=n)
                      for name, n in INT_SUBST_ADMISSIONS.items()}
INT_SUBST_ANSWERS.update({"S2R": ANSWERS["S2"], "SUB2": "4 - 2*ln 3"})
INT_SUBST_NUMERIC.update({"S2R": NUMERIC["S2"],
                          "SUB2": 1.8027754226637804})  # 4 - 2 ln 3

INT_SUBST_WRONG_ANSWERS += [
    {"id": "S2R-W1",
     "what": "S2 by u := x^2 with f := exp(u), the factor 1/2 missing: "
             "exp(x^2)*(2x) is twice the integrand",
     "goal": INT_SUBST_GOALS["S2R"],
     "move": ("int_subst", {"mode": "reverse", "var": "x", "sub": "x^2",
                            "new_var": "u", "lo": "0", "hi": "1",
                            "f": "exp u", "check": "ring", "facts": []}),
     "refusal": "int-subst-check-failed",
     "message": ("int-subst-check-failed", {"f": "exp u"}),
     "residual": "x*exp(x^2) - exp(x^2)*(2*x^1*1)",
     "compare": ("ring", ())},
    {"id": "SUB2-W1",
     "what": "SUB2 with the old upper limit kept, t from 0 to 4 (the limits "
             "not changed with the variable)",
     "goal": INT_SUBST_GOALS["SUB2"],
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "0", "hi": "4", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-endpoint-mismatch",
     "message": ("int-subst-endpoint-mismatch",
                 {"image": "4^2", "limit": "4", "end": "upper"}),
     "residual": "4^2 - 4",
     "compare": ("ring", ())},
]

# The cross-check again, over every proof in section 12.
for _p, _rows in INT_SUBST_FINAL_TRACKER.items():
    _keys = [(r[0], r[1]) for r in _rows]
    assert len(set(_keys)) == len(_keys), _p
    _seen = set()
    for _sid, _obs in INT_SUBST_OBLIGATIONS[_p].items():
        for _ob in _obs:
            _fin = [r for r in _rows if (r[0], r[1]) == (_ob[0], _ob[1])]
            assert _fin and _fin[0][2:] == (_ob[3], _ob[4]), (_p, _sid, _ob)
            assert _ob[5] == ((_ob[0], _ob[1]) not in _seen), (_p, _sid, _ob)
        _seen |= {(o[0], o[1]) for o in _obs}
    assert _seen == set(_keys), _p
    assert [s["id"] for s in INT_SUBST_STEPS[_p]] == \
        [k for k in INT_SUBST_OBLIGATIONS[_p] if k != "goal"], _p
    assert sum(r[2] == ADMITTED for r in _rows) == INT_SUBST_ADMISSIONS[_p]
    assert all(r[3] == T_REG for r in _rows if r[2] == ADMITTED), _p
    for _k, (_tag, _c) in INT_SUBST_EXPECTED[_p].items():
        assert [r for r in _rows if (r[0], r[1]) == _k][0][2:] == \
            (DISCHARGED, _tag), (_p, _k)
assert set(INT_SUBST_PROOF_FILES) == set(INT_SUBST_FINAL_TRACKER)
del _p, _rows, _keys, _seen, _sid, _obs, _ob, _fin, _k, _tag, _c


# ---------------------------------------------------------------------------
# 13. The quarter circle, QC1 (consolidation spec 2026-09-24)
#
# p1_expected's section 13 states the rules (E51-E55); this is
# Int_0^1 sqrt(1 - x^2) = pi/4 by x := cos theta under them, derived by hand
# step by step, without reading kernel.py, discharge.py or search.py. The
# file is kernel/problems/consolidation/QC1.json: stage1/'s floor names its
# files exactly, so a new file there would turn the committed suite red.
# Staged until the build (p1_expected CONSOLIDATION_SWITCH). PF23.
T_PRODUCT = ("sign product", ())
T_PRODUCT_COS = ("sign product", ("cos_le_one", "cos_ge_neg_one"))
T_LINEAR_PI = ("linear", ("pi_pos",))
T_RING_COS_PI_HALF = ("ring", ("cos_pi_half",))
T_RING_COS_ZERO = ("ring", ("cos_zero",))
# theta <= pi follows from the range alone (theta >= 0 and theta <= pi/2 give
# pi >= 0): (theta - pi, strict) + theta + 2*(pi/2 - theta) = 0, strict, and
# TAG_RULES' deletion filter drops the unneeded pi_pos (CHANGES, adjudicated)
T_CITE_SIN = ("cite", ("sin_nonneg_on",))
T_DERIV_FIELD_PYTH = ("deriv+field", ("pyth_cos",))


def ATOM(name, u):
    return ("fact", name, u)


def _product(content, factors, sense=None):
    return {"method": "sign product", "sense": sense, "content": content,
            "factors": tuple(factors)}


def _cite(entry, inst, hyps):
    return {"method": "cite", "entry": entry, "inst": dict(inst),
            "hyps": tuple(hyps)}


CONSOLIDATION_PROOF_FILES = {"QC1": ("consolidation/QC1.json",
                                     "reference_proof")}
CONSOLIDATION_GOALS = {"QC1": "Int[x = 0 .. 1] sqrt(1 - x^2) == ?A"}
CONSOLIDATION_ECHO = {"QC1": "Int[x = 0 .. 1] sqrt(1 - x^2) == ?A"}

QC1_S1 = ("Int[theta = 0 .. pi/2] -(sqrt(1 - (cos theta)^2)"
          "*(-sin theta * 1)) == ?A")
QC1_S2 = ("Int[theta = 0 .. pi/2] -(sqrt(1 - (1 - (sin theta)^2))"
          "*(-sin theta * 1)) == ?A")
QC1_S3 = "Int[theta = 0 .. pi/2] -(sin theta * (-sin theta * 1)) == ?A"
QC1_F = "(theta - sin theta * cos theta)/2"
QC1_INTEGRAND = "-(sin theta * (-sin theta * 1))"
QC1_AFTER_FTC = ("(pi/2 - sin(pi/2)*cos(pi/2))/2 - (0 - sin 0 * cos 0)/2"
                 " == ?A")
CONSOLIDATION_STEPS = {
    "QC1": [
        # int_subst, flipped (E46): pi/2 <= 0 is not discharged, 0 <= pi/2
        # is, so the new integral is Int[theta = 0 .. pi/2] -(F*phi')
        {"id": "s1", "move": "int_subst", "goal_after": QC1_S1},
        # pyth_cos at (cos theta)^2, a tree match (REWRITE_RULE step 3)
        {"id": "s2", "move": "rewrite", "occurrences": 1,
         "goal_after": QC1_S2},
        # sqrt_sq with u := sin theta: ring_nf(1 - (1 - (sin theta)^2)) is
        # (sin theta)^2
        {"id": "s3", "move": "rewrite", "occurrences": 1,
         "goal_after": QC1_S3},
        {"id": "s4", "move": "fact", "goal_after": QC1_S3,
         "conclusion": "(cos theta)^2 == 1 - (sin theta)^2"},
        {"id": "s5", "move": "ftc", "goal_after": QC1_AFTER_FTC},
        {"id": "s6", "move": "rewrite", "occurrences": 1,
         "goal_after": "(pi/2 - 1*cos(pi/2))/2 - (0 - sin 0 * cos 0)/2 == ?A"},
        {"id": "s7", "move": "rewrite", "occurrences": 1,
         "goal_after": "(pi/2 - 1*0)/2 - (0 - sin 0 * cos 0)/2 == ?A"},
        {"id": "s8", "move": "rewrite", "occurrences": 1,
         "goal_after": "(pi/2 - 1*0)/2 - (0 - 0*cos 0)/2 == ?A"},
        # ring: pi/4 - 0 (cos 0 is multiplied by 0)
        {"id": "s9", "move": "close", "goal_after": None},
    ],
}
CONSOLIDATION_THEOREMS = {"QC1": "Int[x = 0 .. 1] sqrt(1 - x^2) == pi/4"}

CONSOLIDATION_DERIV = {
    ("QC1", "s1"): {"var": "theta", "F": "cos theta",
                    "trace": [("d_cos", "cos theta", ()),
                              ("d_var", "theta", ())],
                    "output": "-sin theta * 1", "emits": ()},
    ("QC1", "s5"): {
        "var": "theta", "F": QC1_F,
        "trace": [("route_div", QC1_F, ("2 # 0",)),
                  ("d_mul", "(theta - sin theta * cos theta)*(1/2)", ()),
                  ("d_add", "theta - sin theta * cos theta", ()),
                  ("d_var", "theta", ()),
                  ("route_neg", "-(sin theta * cos theta)", ()),
                  ("d_mul", "-1*(sin theta * cos theta)", ()),
                  ("d_const", "-1", ()),
                  ("d_mul", "sin theta * cos theta", ()),
                  ("d_sin", "sin theta", ()), ("d_var", "theta", ()),
                  ("d_cos", "cos theta", ()), ("d_var", "theta", ()),
                  ("d_const", "1/2", ())],
        "output": ("(1 + (0*(sin theta * cos theta) + (-1)*(cos theta * 1"
                   " * cos theta + sin theta * (-sin theta * 1))))*(1/2)"
                   " + (theta - sin theta * cos theta)*0"),
        "emits": ("2 # 0",)},
}

# Per step, after discharge. Hand-derived:
#   goal: sqrt's 1 - x^2 >= 0 on [0, 1]: FM sees x^2 as opaque, sign finds
#     no form, and the non-strict sign product (E53) factors it as
#     -(x - 1)(x + 1): x - 1 <= 0 by the upper end, x + 1 > 0 by the lower.
#   s1 (INT_SUBST_RULE): step 8, lo's pi/2 owes 2 # 0, and the order
#     0 <= pi/2 is the one discharged (flip); step 10, deriv emits nothing;
#     step 12, cos(pi/2) == 0 and cos 0 == 1 after the exact values; step
#     13, the two Reg on [0, pi/2]; step 14, the new integrand's sqrt owes
#     1 - (cos theta)^2 >= 0 on [0, pi/2], -(cos theta - 1)(cos theta + 1),
#     cos theta - 1 <= 0 by cos_le_one and cos theta + 1 >= 0 (not > 0:
#     cos theta >= -1 gives no strict bound) by cos_ge_neg_one.
#   s2: pyth_cos has no hypothesis, and its R = 1 - (sin theta)^2 no
#     former: nothing; no key uses the range, so no orientation.
#   s3: sqrt_sq's sin theta >= 0 on [0, pi/2], by cite sin_nonneg_on
#     (theta >= 0 by the lower end; theta <= pi by the upper end and
#     pi_pos); R = sin theta owes nothing; the orientation again.
#   s4: fact emits nothing.
#   s5 (ftc, check field, fact h_pyth): F's /2; the premises; deriv's
#     route_div 2 # 0; field's divisor 2 (in 1/2); the fact owes nothing.
#     The check: F' = (1 - cos^2 + sin^2)/2 and the integrand is sin^2,
#     equal once cos^2 is replaced by 1 - sin^2.
#   s6-s8: exact-value rewrites, owing nothing.
#   s9: the value pi/4 owes 4 # 0.
CONSOLIDATION_OBLIGATIONS = {
    "QC1": {
        "goal": [
            ("1 - x^2 >= 0", "[0, 1]", (S_FORMER,), DISCHARGED, T_PRODUCT,
             True),
        ],
        "s1": [
            ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
            ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI, True),
            ("cos(pi/2) == 0", "true", (S_SUBST_LO,), DISCHARGED,
             T_RING_COS_PI_HALF, True),
            ("cos 0 == 1", "true", (S_SUBST_HI,), DISCHARGED, T_RING_COS_ZERO,
             True),
            ("cos theta in C^1([0, pi/2])", "[0, pi/2]", (S_SUBST_C1,),
             ADMITTED, T_REG, True),
            ("sqrt(1 - (cos theta)^2) in C^0([0, pi/2])", "[0, pi/2]",
             (S_SUBST_C0,), ADMITTED, T_REG, True),
            ("1 - (cos theta)^2 >= 0", "[0, pi/2]", (S_FORMER,), DISCHARGED,
             T_PRODUCT_COS, True),
        ],
        "s2": [],
        "s3": [
            ("sin theta >= 0", "[0, pi/2]", (S_SQRT_SQ,), DISCHARGED,
             T_CITE_SIN, True),
            ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI,
             False),
        ],
        "s4": [],
        "s5": [
            ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI,
             False),
            ("2 # 0", "true", (S_FORMER, S_ROUTE_DIV, S_FIELD), DISCHARGED,
             T_NORM_NUM, False),
            (QC1_F + " in C^0([0, pi/2])", "[0, pi/2]", (S_FTC_C0F,),
             ADMITTED, T_REG, True),
            (QC1_F + " in C^1((0, pi/2))", "(0, pi/2)", (S_FTC_C1F,),
             ADMITTED, T_REG, True),
            ("D[theta](" + QC1_F + ") == " + QC1_INTEGRAND, "(0, pi/2)",
             (S_FTC_D,), DISCHARGED, T_DERIV_FIELD_PYTH, True),
            (QC1_INTEGRAND + " in C^0([0, pi/2])", "[0, pi/2]", (S_FTC_C0f,),
             ADMITTED, T_REG, True),
        ],
        "s6": [],
        "s7": [],
        "s8": [],
        "s9": [
            ("4 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
        ],
    },
}

CONSOLIDATION_EXPECTED = {
    "QC1": {
        ("1 - x^2 >= 0", "[0, 1]"): (T_PRODUCT, _product(
            "-1", [("x - 1", "<=", _farkas({GOAL: "1", HI(0): "1"})),
                   ("x + 1", ">", _RANGE_LO)])),
        ("0 <= pi/2", "true"): (T_LINEAR_PI, _farkas({GOAL: "1",
                                                      FACT("pi_pos"): "1/2"})),
        ("1 - (cos theta)^2 >= 0", "[0, pi/2]"): (T_PRODUCT_COS, _product(
            "-1", [("cos theta - 1", "<=",
                    _farkas({GOAL: "1", ATOM("cos_le_one", "theta"): "1"})),
                   ("cos theta + 1", ">=",
                    _farkas({GOAL: "1",
                             ATOM("cos_ge_neg_one", "theta"): "1"}))])),
        ("sin theta >= 0", "[0, pi/2]"): (T_CITE_SIN, _cite(
            "sin_nonneg_on", {"u": "theta"},
            [("theta >= 0", _RANGE_LO),
             ("theta <= pi", _farkas({GOAL: "1", LO(0): "1",
                                      HI(0): "2"}))])),
    },
}

CONSOLIDATION_FINAL_TRACKER = {
    "QC1": [
        ("1 - x^2 >= 0", "[0, 1]", DISCHARGED, T_PRODUCT),
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("0 <= pi/2", "true", DISCHARGED, T_LINEAR_PI),
        ("cos(pi/2) == 0", "true", DISCHARGED, T_RING_COS_PI_HALF),
        ("cos 0 == 1", "true", DISCHARGED, T_RING_COS_ZERO),
        ("cos theta in C^1([0, pi/2])", "[0, pi/2]", ADMITTED, T_REG),
        ("sqrt(1 - (cos theta)^2) in C^0([0, pi/2])", "[0, pi/2]", ADMITTED,
         T_REG),
        ("1 - (cos theta)^2 >= 0", "[0, pi/2]", DISCHARGED, T_PRODUCT_COS),
        ("sin theta >= 0", "[0, pi/2]", DISCHARGED, T_CITE_SIN),
        (QC1_F + " in C^0([0, pi/2])", "[0, pi/2]", ADMITTED, T_REG),
        (QC1_F + " in C^1((0, pi/2))", "(0, pi/2)", ADMITTED, T_REG),
        ("D[theta](" + QC1_F + ") == " + QC1_INTEGRAND, "(0, pi/2)",
         DISCHARGED, T_DERIV_FIELD_PYTH),
        (QC1_INTEGRAND + " in C^0([0, pi/2])", "[0, pi/2]", ADMITTED, T_REG),
        ("4 # 0", "true", DISCHARGED, T_NORM_NUM),
    ],
}
# int_subst's two Reg and ftc's three; none tagged none
CONSOLIDATION_ADMISSIONS = {"QC1": 5}
CONSOLIDATION_VERDICTS = {n: VERDICT.format(n=k)
                          for n, k in CONSOLIDATION_ADMISSIONS.items()}
CONSOLIDATION_ANSWERS = {"QC1": "pi/4"}
CONSOLIDATION_NUMERIC = {"QC1": 0.7853981633974483}  # pi/4

CONSOLIDATION_WRONG_ANSWERS = [
    # the check without the fact: cos theta^2 and sin theta^2 are unrelated
    # atoms to field, so F' - f = (1 - cos^2 - sin^2)/2 is left over
    {"id": "QC1-W1",
     "what": "QC1's ftc without pyth_cos",
     "state": ("QC1", "s4"),
     "move": ("ftc", {"F": QC1_F, "check": "field", "facts": []}),
     "refusal": "ftc-check-failed",
     "residual": ("(1 + (0*(sin theta * cos theta) + (-1)*(cos theta * 1"
                  " * cos theta + sin theta * (-sin theta * 1))))*(1/2)"
                  " + (theta - sin theta * cos theta)*0 - " + QC1_INTEGRAND),
     "compare": ("field", ())},
    # sqrt_sq before pyth_cos: ring_nf(1 - (cos theta)^2) is not
    # (sin theta)^2
    {"id": "QC1-W2",
     "what": "sqrt_sq at sqrt(1 - (cos theta)^2) straight after s1",
     "state": ("QC1", "s1"),
     "move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "sin theta"},
                          "at": "sqrt(1 - (cos theta)^2)"}),
     "refusal": "rewrite-lhs-mismatch"},
]

# Cross-check.
for _p, _rows in CONSOLIDATION_FINAL_TRACKER.items():
    _seen = set()
    for _sid, _obs in CONSOLIDATION_OBLIGATIONS[_p].items():
        for _ob in _obs:
            _fin = [r for r in _rows if (r[0], r[1]) == (_ob[0], _ob[1])]
            assert _fin and _fin[0][2:] == (_ob[3], _ob[4]), (_p, _sid, _ob)
            assert _ob[5] == ((_ob[0], _ob[1]) not in _seen), (_p, _sid, _ob)
        _seen |= {(o[0], o[1]) for o in _obs}
    assert _seen == {(r[0], r[1]) for r in _rows}, _p
    assert [s["id"] for s in CONSOLIDATION_STEPS[_p]] == \
        [k for k in CONSOLIDATION_OBLIGATIONS[_p] if k != "goal"], _p
    assert sum(r[2] == ADMITTED for r in _rows) == CONSOLIDATION_ADMISSIONS[_p]
    for _k, (_tag, _c) in CONSOLIDATION_EXPECTED[_p].items():
        assert [r for r in _rows if (r[0], r[1]) == _k][0][2:] == \
            (DISCHARGED, _tag), (_p, _k)
del _p, _rows, _seen, _sid, _obs, _ob, _fin, _k, _tag, _c
