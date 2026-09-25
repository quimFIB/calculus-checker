"""Readiness P1, written out before the kernel exists.

This is WHAT.md's "Before any code" items 2 and 3: both P1 proofs as
(move, args) data with every rewrite instantiated, and the obligation list
each step is expected to emit. `kernel/proof_of_life.py` imports it and
asserts the kernel against it. Everything here was derived by hand from
DESIGN.md revision 9 and kernel/GRAMMAR.md, not from code. It was checked at
build time with SymPy in a scratch directory, and that check is not part of
this file (see VERIFIED at the end).

Nothing here imports anything. Terms are strings in GRAMMAR.md's concrete
syntax. The script parses them with the kernel's parser and compares trees,
never strings: `parse_term(s) == kernel_term`. The printer's exact output
is asserted only in PRINT_EXACT (section 9), for the Neg-base cases §15.6
names.

Two protection models are in force (§15.3: "say which is in force"), one
per kind of object, and HANDLES_IN_FORCE says so. Fact slots take handles.
A step that needs a theorem, such as `field`'s facts, names a handle that
an earlier `fact` step bound (`("handle", "h_sqrt3")`), and the script
passes the handle object the kernel returned for that step. Proof states,
which carry the verdict, are protected by §15.3's sentinel fallback. The
comment at HANDLES_IN_FORCE gives the reason that is enough here.

E17, the handle model. It interprets §15.3's "opaque identifier", and
WHAT.md Done-when item 5, which requires copies and pickles to be refused:
  * A handle is an instance of a kernel-private class, minted only by `fact`.
    It carries an integer id, unique across the whole kernel, and the
    lineage of the proof state it was minted in. The states a step produces
    inherit their predecessor's lineage and registry.
  * The kernel keeps a private map from id to (minted object, lineage). A
    step accepts a fact only if the map's entry for fact.id exists, its
    object `is` fact, and its lineage is the lineage of the state the step
    runs in. A minted object from another lineage gives
    'fact-foreign-state-handle'. Anything else gives
    'fact-not-minted-handle': a bare int, any other object, a Judgement, a
    copy, an unpickled object, or a real handle whose id was altered.
  * The handle class does NOT override __copy__, __deepcopy__ or __reduce__.
    Copying and pickling therefore produce new objects, and the identity
    check refuses them. Of the two options (identity check, or those
    methods raising TypeError), this one is chosen because it does not
    depend on the class cooperating. A copy built by hand, through
    object.__new__ and a copied __dict__, is refused by the same check.
  * A handle's lineage is a plain picklable token (e.g. an int), and the
    handle class is defined at module level, so copy, deepcopy and pickle
    round trips all succeed and are refused by the identity check, not by
    copying or pickling failing (E21, FORGERIES).
  * An id-only model is rejected, because it cannot tell a copy from the
    original.

Decisions are marked E1, E2, … and each cites the § it interprets. They are
collected in DECISIONS near the end, and the places where DESIGN.md is wrong
or self-contradictory are in DESIGN_DEFECTS.
"""

# ---------------------------------------------------------------------------
# 0. Conventions

# §15.3 asks which protection is in force. Both are, one per kind of object
# (decided on the owner's behalf on 2026-09-24; the owner expressed no
# preference on PROOF_OF_LIFE.md question 3):
#   * handles for facts. A fact slot accepts only the object `fact` minted,
#     by identity with the kernel's record for its id and lineage (E17), so
#     a theorem cannot be built, copied, pickled or faked from outside the
#     kernel;
#   * the sentinel for proof states. A ProofState, which carries the verdict
#     report() prints, demands a kernel-private token to construct, and
#     step() and report() refuse any state the kernel did not make.
# The sentinel is enough for states because a finished state, the only kind
# report() gives a verdict for, is only ever produced by step(): install()
# makes the first state, open, and every later one is step()'s output. No
# caller assembles one. §15.3's realistic failure is a buggy tactic that
# builds a result object instead of calling the kernel, and a state built
# without the token, or copied, is refused. What the sentinel does not stop
# is a deliberate write through private names (§15.3: "forgeable in five
# lines by anyone who wants to"). §16.3's API boundary, not built in this
# milestone, replaces in-process states with ids, so that no state crosses
# it.
HANDLES_IN_FORCE = "handles for facts, sentinel for proof states"
SIG = {}  # P1 declares no function symbols (§5.1 f(e, ..., e))

# The one report string the kernel may print for a finished proof with
# admissions (§5.4, §15.6). PROVED is the report for N == 0. No PROOFS run
# reaches it. DEFINEDNESS_CASES' literal cases do, which shows E26 charging a
# literal condition and norm_num discharging it (E7).
VERDICT = "Proved modulo {n} admissions"
PROVED = "Proved."
ADMISSION_REASON = "discharge not built"  # WHAT.md, Scope, Stubbed

# Obligation statuses (§5.4 has three states; "open" never survives a
# successful step in this milestone, because every undischarged side condition
# is minted as an admission when it is emitted).
DISCHARGED = "discharged"
ADMITTED = "admitted"

# Tags. A tag is (method, cites): the §5.3 method expected to close an
# admission, or the procedure that closed a discharged obligation, plus the
# §6.8 entries it cites. E15: methods for admissions are §5.3's list plus
# `reg` (§6.9/§7, regularity closure, which is not a §5.3 method). E24
# (TAG_RULES, below) says which method a given admission gets. WHAT.md says
# an admission tagged `none` fails the milestone. The script asserts
# `tag[0] != "none"` for every admission of every proof in PROOFS, run
# unmutated, and asserts the whole tag equals the one given here. The no-none
# assertion does not cover OCCURRENCE_CASE, DEFINEDNESS_CASES, BAD_MOVES or
# planted-bug runs: OCCURRENCE_CASE's false t >= 0 @ [-1, 0] is expected to be
# tagged none, as a positive test that the tagger flags a false obligation,
# and so are DEFINEDNESS_CASES' false cos(pi/2) # 0 and x > 0 @ x < 0, the
# same test for a definedness obligation (E26) (for x > 0 only:
# ln_true_by_hyp is its true contrast; cos u # 0 is tagged none unless the
# goal's own domain Γ states it, or an order item it follows from
# (cos u > 0, cos u < 0), which hyp closes (§5.3 method 1). This holds until
# cos_nonzero_on is pinned, as DEFINEDNESS_CASES tan_zero_true pins. So a
# PROOFS run with tan on a goal whose domain does not state that condition
# cannot yet pass the no-none check). Tag
# equality is asserted everywhere a tag is given.
ADMISSION_METHODS = {
    "none": "no method's feasibility check passed (E24). Fails the milestone "
            "in an unmutated PROOFS run",
    "hyp": "§5.3 method 1, by hypothesis",
    "range": "§5.3 method 2 then 3: linear over the domain's range interval",
    "linear": "§5.3 method 3, Fourier–Motzkin; pi and e_const bring their "
              "sign facts (§5.3 rev 9)",
    "sign": "§5.3 method 4, sign certificate (the goal as written first). "
            "Per E20, for a non-strict `>= 0` goal it also accepts a zero "
            "rational constant, which §5.3 as written does not state (see "
            "DESIGN_DEFECTS)",
    "sign product": "§5.3 method 5, factorisation re-checked by ring. Per "
                    "E18 it also splits off a nonzero rational content "
                    "(3*sqrt 3, 2*sqrt x), which §5.3 as written does not "
                    "allow (see DESIGN_DEFECTS)",
    "cite": "§5.3 method 6, a §6.8 entry",
    "reg": "§6.9's closure rules, a derivation checked rule by rule (E60, "
           "section 17's REG_CHECK_RULE); an admitted Reg is tagged "
           "('reg', cites) or ('none', ()) by TAG_RULES' reg paragraph "
           "(regularity build 2026-09-25; before it, 'regularity is only "
           "listed in this milestone')",
}
DISCHARGE_METHODS = {
    "norm_num": "§6.2, closes a goal over rational literals exactly (E7)",
    "deriv+ring": "§6.3 deriv then §6.2 ring, run inside the ftc step (E9)",
    "deriv+field": "§6.3 deriv then §6.2 field, facts as cited (E9)",
    # regularity build 2026-09-25 (section 17's DISCHARGE_METHODS_REG)
    "reg": "§6.9's closure rules as a checked derivation by term structure, "
           "each side condition a §5.3 certificate (E60, REG_CHECK_RULE)",
}

T_NONE = ("none", ())
T_REG = ("reg", ())
T_HYP = ("hyp", ())
T_RANGE = ("range", ())
T_LINEAR = ("linear", ())
T_LINEAR_PI = ("linear", ("pi_pos",))
T_SIGN = ("sign", ())
T_PRODUCT = ("sign product", ())
T_PRODUCT_SQRT = ("sign product", ("sqrt_pos",))
T_SQRT_POS = ("cite", ("sqrt_pos",))
T_NORM_NUM = ("norm_num", ())
T_DERIV_RING = ("deriv+ring", ())
T_DERIV_FIELD = ("deriv+field", ())
T_DERIV_FIELD_FACT = ("deriv+field", ("sqrt_sq_val",))

# E24, the tagger. It interprets §5.3's "in the order tried" and WHAT.md's
# "an admission tagged `none` fails the milestone". Without a stated rule the
# tagger could only be fitted to the lists below, and a tagger that picked by
# the domain's shape (and cited pi_pos wherever pi occurs) would never
# produce `none`, so the check WHAT.md relies on would be empty. The tagger
# is untrusted (§7): it proposes a method, the kernel relies on it for
# nothing, and discharge stays stubbed. A discharged obligation is not
# tagged by it; its tag is the procedure that closed it (DISCHARGE_METHODS).
TAG_RULES = (
    "An admission (prop, dom) is tagged with the first method below, in "
    "§5.3's order, whose cheap untrusted feasibility check passes. The cites "
    "are the §6.8 entries that check used, including those its "
    "sub-obligations used, without repeats. If no check passes, the tag is "
    "('none', ()).",

    # regularity build 2026-09-25: REG_TAG_RULE (E60) replaces the stub
    # phase's 'tagged ('reg', ()) by its shape alone'
    "reg. A regularity judgement e in C^k(D) is tagged ('reg', cites) when "
    "its derivation exists (every node of e has a rule, REG_CHECK_RULE) "
    "and every side condition of it, keyed at D, is not tagged none by "
    "this same list (the side's tag, recursively, as sub-obligations are); "
    "cites are the sides' cites in pre-order first use. Otherwise "
    "('none', ()). No other method sees a regularity judgement, and reg "
    "sees nothing else.",

    "hyp (§5.3 method 1). prop is in Γ, or follows from Γ's ordering "
    "hypotheses by reflexive-transitive closure. Γ is the goal's own "
    "hypotheses: the items the goal's own domain contributed to dom (E1 "
    "step 7, first part). The interval items that Int ranges and ftc's "
    "[a, b] and (a, b) put into dom belong to method 2, not to Γ. Every P1 "
    "goal's domain is true, so hyp never fires in P1.",

    "range, linear (§5.3 methods 2 and 3). Run Fourier–Motzkin over Q on "
    "three things: the negated goal; dom's items, where an interval item on "
    "v gives c <= v and v <= d, with < at an open end and nothing at an "
    "infinite end; and the sign fact of each named constant that occurs in "
    "prop or dom (pi_pos : pi > 0, e_gt_one : e_const > 1; §5.3 rev 9). "
    "Every atom and every non-linear monomial (pi^2, sqrt x, x^3, "
    "x*inv(x)) is treated as a fresh opaque variable, so only the linear "
    "fragment is used. A goal e # 0 is tried as e > 0, then as e < 0. If "
    "the set is infeasible, the tag is 'range' when some item of dom has a "
    "nonzero multiplier in the Farkas combination, and 'linear' otherwise. "
    "A sign fact goes into cites only if its multiplier is nonzero. The "
    "combination is an irreducible one: no constraint in it can be dropped. "
    "So when the negated goal is infeasible by itself, as when ring cancels "
    "it to a false constant, no item of dom is used and the tag is "
    "'linear': 1/x - 1/x + 1 > 0 @ [1, 2] normalises to 1 > 0 (MATCH_ACCEPTS "
    "ring_cancels_inv_atom, E26).",

    "sign (§5.3 method 4). First the goal as written, then its ring normal "
    "form, is matched against two forms: a positive rational plus a sum of "
    "even powers, each with a positive rational coefficient; or a "
    "quadratic in one variable or atom with a positive leading coefficient "
    "and a negative discriminant. For a non-strict `e >= 0` or `0 <= e` "
    "goal, a zero constant is also accepted (E20). A goal e # 0 is tried "
    "as e > 0.",

    "sign product (§5.3 method 5). It closes >, < and # 0 goals only, never "
    ">= or <=. (i) E18: the ring normal form is c*p with c a rational other "
    "than 0 and 1, and p's obligation at dom (p # 0, or p's sign goal with "
    "c's sign decided by norm_num) is not tagged none. (ii) Otherwise, an "
    "untrusted factorisation into factors of strictly lower degree, in which "
    "every factor's obligation at dom is not tagged none. The factorisation "
    "comes from a step argument or, failing that, from a small stdlib "
    "rational-root factoriser in the untrusted layer (§5.3 allows §8.2's "
    "factoriser). It need not come from F: 1 + x^3 # 0 @ [0, 1] is emitted "
    "when the goal is installed, before any F exists. The cites are the "
    "union of the parts' cites.",

    "cite (§5.3 method 6). A §6.8 entry whose instantiated conclusion "
    "implies prop syntactically, and whose instantiated hypotheses at dom "
    "are each not tagged none. 'Implies syntactically' means one of two "
    "things. Either the conclusion is prop as a tree, or the conclusion is "
    "`a > 0` (or `0 < a`) and prop is `a # 0`, `a >= 0` or `0 <= a` with "
    "the same a as a tree. So sqrt_pos's sqrt a > 0 gives sqrt a # 0, and "
    "pi_pos's pi > 0 gives neither pi/2 >= 0 nor 0 <= pi/2.",

    "Sub-obligations (a factor's sign, the p of a content split, a cited "
    "entry's hypotheses) are tagged by this same list, recursively. "
    "Termination is §5.3's own: strictly lower degree in (ii), a literal "
    "content in (i). Sub-obligations are not recorded as admissions. They "
    "only decide whether the parent's check passes, and they contribute "
    "cites.",
)

# Sources: which rule emitted an obligation. One key may have several.
# The kernel reports these codes verbatim as an obligation's sources. They are
# the stable thing to assert, like REFUSAL_CODES, and the prose is
# documentation only, so no § reference has to be copied into trusted code.
SOURCES = {
    "former": "a former in a term entering the proof (§5.1): '/' or a "
              "negative power owes its divisor d # 0 and a real power its "
              "base > 0 (E6), a partial builtin its natural domain "
              "(E26: ln u owes u > 0, sqrt u owes u >= 0, tan u owes "
              "cos u # 0, and so on), a statable Int[x = a .. b] f its "
              "integrand in C^0 on its range, and a D[x] e its body in C^1 "
              "at its position domain (E64)",
    "orient": "range orientation lo <= hi (E4; §5.1 reversed limits, §5.3 "
              "method 2)",
    "rewrite_hyp": "rewrite by a §6.8 entry: its hypothesis instantiated "
                   "(sqrt_sq u >= 0; §6.8, §6.1)",
    "ftc_F_C0": "ftc premise F in C^0([a, b]) (§6.4)",
    "ftc_F_C1": "ftc premise F in C^1((a, b)) (§6.4)",
    "ftc_D": "ftc premise D[x] F == f @ (a, b) (§6.4)",
    "ftc_f_C0": "ftc premise f in C^0([a, b]) (§6.4)",
    "d_ln": "d_ln: u > 0 (§6.3)",
    "d_sqrt": "d_sqrt: u > 0 (§6.3)",
    "route_div": "deriv routes u / v as u * (1/v) by field, owing v # 0 "
                 "(§6.3 rev 7)",
    "field_div": "field: every divisor in its input, atom arguments included "
                 "(§6.2 rev 7)",
    "fact_hyp": "fact hypothesis inherited by the result (§6.2 facts; "
                "sqrt_sq_val a >= 0)",
}
S_FORMER, S_ORIENT, S_SQRT_SQ = "former", "orient", "rewrite_hyp"
S_FTC_C0F, S_FTC_C1F, S_FTC_D, S_FTC_C0f = (
    "ftc_F_C0", "ftc_F_C1", "ftc_D", "ftc_f_C0")
S_D_LN, S_D_SQRT, S_ROUTE_DIV = "d_ln", "d_sqrt", "route_div"
S_FIELD, S_FACT = "field_div", "fact_hyp"
assert all(s in SOURCES for s in (
    S_FORMER, S_ORIENT, S_SQRT_SQ, S_FTC_C0F, S_FTC_C1F, S_FTC_D, S_FTC_C0f,
    S_D_LN, S_D_SQRT, S_ROUTE_DIV, S_FIELD, S_FACT))

# ---------------------------------------------------------------------------
# 1. The §6.8 entries P1 uses, pinned by exact statement
#
# `statement` is a judgement for parse_judgement. `schema` lists the
# variables `inst` must bind; in GRAMMAR.md's §9 pinning they are the ordinary
# variables u and a. `hyps` are the statement's domain items. Each becomes an
# obligation when the entry is used, at the position's domain (E1 step 8).
#
# §6.8 writes sqrt_sq with t (√(t²) ≐ t @ t ≥ 0). It is stated with u here,
# as GRAMMAR.md pins it, so that the schema variable is never the same name as
# §11.1's bound t. The instantiation u := t is then visible, not a coincidence
# of names (§15.2 item 3).
#
# No entry had to be added. The fallback route's `sqrt 0` closes by sqrt_sq
# with u := 0 (hypothesis 0 >= 0, norm_num), so §6.8's table row
# "sqrt: 0, 1" is not needed as a separate entry. `cos 0` is never evaluated,
# because ring removes 2*0*cos 0 (§11.1 revision 9 dropped cos_zero).

NAMED_ENTRIES = {
    "sqrt_sq": {
        "statement": "sqrt(u^2) == u @ u >= 0",
        "schema": ("u",),
        "lhs": "sqrt(u^2)",
        "rhs": "u",
        "hyps": ("u >= 0",),
        "use": "rewrite",
        "cite": "§6.8 (sqrt_sq)",
        "used_in": ("P1.1 s1 (u := t, under Int)",
                    "P1.1-fallback s2 (u := pi/2), s3 (u := 0)",
                    "BAD_MOVES rewrite_under_D (u := x, refused)"),
    },
    "pi_pos": {
        "statement": "pi > 0",
        "schema": (),
        "hyps": (),
        "use": "sign fact: joins §5.3's constraint set whenever pi occurs "
               "(rev 9); appears here only as a cite in tags",
        "cite": "§6.8 rev 9 (Rocq PI_RGT_0, per §6.8)",
        "used_in": ("tags of 0 <= pi/2 and pi/2 >= 0",),
    },
    "sin_pi_half": {
        "statement": "sin(pi/2) == 1",
        "schema": (),
        "lhs": "sin(pi/2)",
        "rhs": "1",
        "hyps": (),
        "use": "rewrite",
        "cite": "§6.8 table, sin at π/2",
        "used_in": ("P1.1 s3", "P1.1-fallback s4"),
    },
    "cos_pi_half": {
        "statement": "cos(pi/2) == 0",
        "schema": (),
        "lhs": "cos(pi/2)",
        "rhs": "0",
        "hyps": (),
        "use": "rewrite",
        "cite": "§6.8 (cos_pi_half)",
        "used_in": ("P1.1 s4", "P1.1-fallback s5"),
    },
    "sin_zero": {
        "statement": "sin 0 == 0",
        "schema": (),
        "lhs": "sin 0",
        "rhs": "0",
        "hyps": (),
        "use": "rewrite",
        "cite": "§6.8 (sin_zero)",
        "used_in": ("P1.1 s5", "P1.1-fallback s6"),
    },
    "ln_one": {
        "statement": "ln 1 == 0",
        "schema": (),
        "lhs": "ln 1",
        "rhs": "0",
        "hyps": (),
        "use": "rewrite",
        "cite": "§6.8 (ln_one)",
        "used_in": ("P1.2 s3, s4, s5",
                    "BAD_MOVES rewrite_needs_field (refused)"),
    },
    "atan_one_sqrt3": {
        # The divisor sqrt 3 in the statement is part of a trusted library
        # statement (§6.8, §15.2 item 7) and is not re-charged when the entry
        # is used, and neither is its sqrt's 3 >= 0 (E26). The target the
        # rewrite acts on was charged when it entered the goal (E6, E26).
        "statement": "atan(1/sqrt 3) == pi/6",
        "schema": (),
        "lhs": "atan(1/sqrt 3)",
        "rhs": "pi/6",
        "hyps": (),
        "use": "rewrite",
        "cite": "§6.8 (atan_one_sqrt3)",
        "used_in": ("P1.2 s6, s8", "BAD_MOVES rewrite_lhs_mismatch (refused)"),
    },
    "atan_odd": {
        "statement": "atan(-u) == -atan u",
        "schema": ("u",),
        "lhs": "atan(-u)",
        "rhs": "-atan u",
        "hyps": (),
        "use": "rewrite",
        "cite": "§6.8 parity row (atan_odd)",
        "used_in": ("P1.2 s7 (u := 1/sqrt 3)",),
    },
    "sqrt_sq_val": {
        "statement": "(sqrt a)^2 == a @ a >= 0",
        "schema": ("a",),
        "lhs": "(sqrt a)^2",
        "rhs": "a",
        "hyps": ("a >= 0",),
        "use": "fact for field (§6.2 facts), never a rewrite (§6.8, rev 7)",
        "cite": "§6.8 (sqrt_sq_val)",
        "used_in": ("P1.2 s1 (a := 3), consumed by s2 and by P1.2-alt's close",),
    },
    "sqrt_pos": {
        "statement": "sqrt a > 0 @ a > 0",
        "schema": ("a",),
        "hyps": ("a > 0",),
        "use": "named, not used until discharge exists (WHAT.md Scope); "
               "appears as a cite in tags",
        "cite": "§6.8 (sqrt_pos), written with @ per GRAMMAR.md D14",
        "used_in": ("tags of sqrt 3 # 0, 3*sqrt 3 # 0, 2*sqrt x # 0",),
    },
}
ADDED_ENTRIES = ()  # none were needed; see the note above NAMED_ENTRIES

# ---------------------------------------------------------------------------
# 2. How rewrite matches (§18 Q21, settled for this milestone) and where
#    domains come from

# E1. The Q21 default, made precise. WHAT.md names it as the default to trial.
REWRITE_RULE = (
    "Arguments: entry (a NAMED_ENTRIES key), inst (a dict from each schema "
    "variable to a term; exactly the entry's schema, no more, no fewer), "
    "at (the target subterm, a term), and optionally occurrence (E2): a "
    "0-based index into the structural occurrences of `at` in the goal's "
    "non-?A side (both sides, lhs first, for a goal with no ?A), enumerated "
    "in pre-order, left to right over the tree (children in GRAMMAR.md §7's "
    "field order, so an Int's lo and hi before its body). An "
    "Int[v = lo .. hi] e encloses an occurrence only when the occurrence "
    "lies in its body e. An occurrence in lo or hi is outside v's scope "
    "(GRAMMAR.md §5: the bound variable may not occur in its own endpoints; "
    "fv(Int[v = a .. b] e) = (fv(e) - {v}) ∪ fv(a) ∪ fv(b)). It gets "
    "neither v nor v's range. It still gets the binder and range of any "
    "outer Int whose body contains it. When given, it is §6.1's "
    "position p: only that occurrence is matched, scope-checked (step 6), "
    "given its domain (step 7), charged (steps 8 and 10) and replaced (step "
    "11). An index out of range gives 'rewrite-target-not-found'. No P1 "
    "step passes it.",

    "1. L := lhs[inst], R := rhs[inst], H := [h[inst] for h in hyps]. The "
    "substitution is capture-avoiding. Entry statements contain no binders, "
    "so nothing can be captured inside them.",

    "2. `at` must occur structurally (tree ==) in the goal's non-?A side. "
    "When `occurrence` is absent, every occurrence is rewritten (E2), and "
    "steps 6 to 10 apply to each one. When it is given, only that one is. No "
    "occurrence gives refusal 'rewrite-target-not-found'. The ?A side is "
    "never rewritten (§9).",

    "3. Match. If L is an application h(a) of a builtin, `at` must be an "
    "application of the same h, and ring_nf(a) == ring_nf(b), where b is the "
    "argument of `at`. If L is anything else, L == at as trees. Every rewrite "
    "entry P1 uses has an application on its left, so the first case is the "
    "only one exercised. Mismatch gives 'rewrite-lhs-mismatch'.",

    "4. ring_nf is §6.2's ring normal form over Q[atoms], and nothing more. A "
    "division a/d by a nonzero rational literal d is a coefficient. A "
    "division a/d by anything else is a * inv(d), with inv(d) an opaque atom "
    "keyed by ring_nf(d) (E3). Negative powers are handled the same way. "
    "Atoms (applications, inv, RPow) are identified by their head and the "
    "ring_nf of their arguments, recursively (§6.2, atoms). It is never "
    "field_nf, which cancels and would owe obligations (Q21). So ln(x/x) does "
    "not match ln 1: x*inv(x) is not 1 in ring.",

    "5. Why it is sound. ring_nf(a) == ring_nf(b) is an identity in "
    "Q[atoms]: it holds for every value of every atom, inv atoms included. "
    "Read inv(d) as 1/d, defined only where d # 0. That is the partial "
    "reading §14 requires; the design gives no total 1/0. §5.1 keeps oo out "
    "of arithmetic, so every atom is a real, and §6.2 makes every "
    "non-literal divisor an opaque atom. So the identity specialises to "
    "a = b at every point where every divisor of a and of b is nonzero: a "
    "and b are equal wherever both are defined. The same holds for the "
    "partial builtins' atoms (E26): ln u is a real only where u > 0, and so "
    "on, so 'defined' means every divisor nonzero and every partial builtin "
    "inside its domain. An Int or D atom has no domain the kernel can "
    "state, so ring refuses to normalise one, and the match is refused "
    "'Int-or-D-not-normalisable' (E26 (b)). ring cancels no divisor "
    "(x*inv(x) is not 1, §6.2), which is why this equality never needs a "
    "d # 0 obligation. But it does cancel monomials that sum to zero, "
    "including monomials that contain an inv atom: inv(y) - inv(y) is 0. "
    "So a and b need NOT have the same inverse atoms or the same divisors, "
    "and soundness does not rest on that. For example sqrt(1/y - 1/y) "
    "matches sqrt_sq's L = sqrt(0^2), and ln(1/x - 1/x + 1) matches ln 1 "
    "(MATCH_ACCEPTS). The divisors and domains that matter are those of "
    "terms left in the goal. The target's own were charged when it entered "
    "the goal (E6, E26). Any divisor inst carries into the result appears "
    "in R and is charged at P by step 10: atan_odd with u := x/x - x/x at "
    "atan(0) matches, and its R, -atan(x/x - x/x), owes x # 0. So does any "
    "partial builtin: atan_odd with u := y + (ln(-1) - ln(-1)) at atan(-y) "
    "matches, and its R owes -1 > 0, which norm_num refutes (BAD_MOVES "
    "rewrite_R_owes_domain). A divisor of L that does not reach R leaves "
    "the goal and owes nothing; in P1 every schema variable of an entry's "
    "lhs occurs in its rhs. So the matcher owes no divisor or domain that "
    "has not been charged. Congruence then gives h(a) == h(b), the entry "
    "gives L == R on H, and so at == R on H at every point where the "
    "charged divisors are nonzero and the charged domains hold.",

    "6. Scope. Every free variable of every inst value must be in scope at "
    "each occurrence: free in the goal, or bound by an Int enclosing the "
    "occurrence (step 2: the occurrence is in that Int's body). The binder "
    "case is exactly this. sqrt_sq's u := t is legal "
    "at sqrt(t^2) because t is bound by the enclosing Int[t = 0 .. pi/2]. "
    "A free variable out of scope gives the refusal 'rewrite-scope'. In "
    "particular, an inst value mentioning v at an occurrence in "
    "Int[v = ..]'s own lo or hi is refused 'rewrite-scope' (BAD_MOVES "
    "rewrite_in_own_endpoint).",

    "7. Position domain P of an occurrence: the goal's own domain (true for "
    "every P1 goal), plus the range interval of each Int[v = lo .. hi] "
    "enclosing the occurrence in the step-2 sense (its body, not its "
    "endpoints), built by DOMAIN_RULES E4, which says what an infinite end "
    "gives. The E4 orientation obligation comes only from those Ints. Under "
    "Int that interval is all "
    "§6.1 asks for, since the integral depends only on values on the range.",

    "8. Side conditions: for each occurrence and each h in H, emit h @ P. A "
    "closed h, with no free variables, is emitted with domain true (E5). For "
    "sqrt_sq at sqrt(t^2) under Int[t = 0 .. pi/2] this gives "
    "t >= 0 @ [0, pi/2], plus the range orientation 0 <= pi/2 (E4). The "
    "orientation is where pi_pos is needed.",

    "9. Under D[x] (revision 9, §6.1). If an occurrence lies anywhere below a "
    "D[x], the equation's whole domain in x must be open (E11). Two tests, "
    "and failing either gives the refusal "
    "'rewrite-under-D-needs-open-domain'. "
    "(a) Every h in H that mentions x must be open: a strict < or >, a # 0, "
    "or an open interval, and no subterm of h that mentions x may be an "
    "application of sqrt, asin, acos or acosh, or a D or Int node. The "
    "same test applies to every obligation step 10 charges from R at the "
    "occurrence: each E6 former ('/', negative powers, RPow bases) and "
    "each E26 former, formers nested inside a divisor included. Both bound "
    "the equation's domain (step 5: at == R holds where H holds and where "
    "R's charged divisors and domains hold), so both must be open in x. "
    "In practice R may not carry sqrt, asin, acos or acosh of an x-term, "
    "even buried in a divisor such as 1/(sqrt x + 1), whose d # 0 is "
    "strict but holds exactly on [0, oo). The strict open formers stay "
    "allowed: ln (u > 0), tan (cos u # 0), '/' and negative powers "
    "(d # 0), RPow (base > 0) and atanh (u > -1, u < 1). An inst value "
    "holding a D or Int is refused earlier, at step 3's ring_nf "
    "(E26 (b)), whenever it lies in L's argument, as every P1 entry's "
    "does; the subterm clause refuses it otherwise (BAD_MOVES "
    "rewrite_under_D_R_closed_former, rewrite_under_D_R_divisor). An item "
    "not mentioning x is allowed, because the set of x where it holds is "
    "all of R or empty, and both are open. The subterm clause is needed "
    "because 'strict' alone does not give an open set under the partial "
    "reading of step 5. sqrt x + 1 > 0 and sqrt x + 1 # 0 are strict, but "
    "both hold exactly on [0, oo). A term is continuous on its natural "
    "domain, so its > 0, < 0 and # 0 sets are open whenever that domain is "
    "open. That domain is open when every partial former in the term has an "
    "open natural domain. '/', negative integer powers, ln, tan, atanh and "
    "RPow (base > 0, §5.1) do. sqrt (u >= 0), asin and acos (|u| <= 1) and "
    "acosh (u >= 1) do not (§6.9). D and Int are refused because this "
    "argument does not cover them. "
    "(b) If H or step 10's charges from R at the occurrence are "
    "non-empty, then no Int[v = lo .. hi] that lies below the "
    "D[x] and encloses the occurrence (in step 2's body sense) may have a "
    "lo or hi that mentions x. Such an Int puts its range interval into P "
    "(step 7), and steps 8 and 10 emit the equation's hypotheses and R's "
    "charged formers on it. E4 always "
    "builds that interval closed at every finite end, and it emits the "
    "non-strict lo <= hi, so the equation's domain in x is closed (§6.1 rev "
    "9). An Int whose ends are both x-free contributes an x-free interval. "
    "Its set of x is R or empty, so it is allowed, by (a)'s argument. An "
    "occurrence where H is empty and R charges nothing emits nothing at P, "
    "and is not affected. Test (b) is "
    "conservative. With continuous integrands the Leibniz rule would make "
    "such a rewrite sound, but the design does not state that argument, so "
    "the kernel follows §6.1's letter (BAD_MOVES "
    "rewrite_under_D_through_Int, rewrite_under_D_through_Int_R_former). "
    "sqrt_sq's u >= 0 with u := x is refused by (a). That is WHAT.md's "
    "must-refuse D[x] sqrt(x^2). E16's cong inherits both tests unchanged. "
    "No accepted P1 rewrite is under a D, so neither test changes a P1 "
    "result. Test (a) on step 10's charges was added after E26 (a review "
    "fix, DATA_CHANGES): E26 made step 10 charge closed domains (sqrt's "
    "u >= 0 and the like), and the gap already existed before E26 through "
    "a divisor holding sqrt of x.",

    "10. Formers: every former in R, and so in the inst values it carries "
    "into the goal, is charged at P: '/', negative powers and RPow bases "
    "(E6), and the partial builtins (E26).",

    "11. Result: when `occurrence` is absent, every occurrence of `at` is "
    "replaced by R; when it is given, only that one. The step emits the "
    "obligations of steps 8 and 10, and nothing else.",
)

# Accepted rewrites that pin REWRITE_RULE's reading: step 5's match, and
# E4's infinite ends (DOMAIN_RULES). They are acceptances, so they are not in
# BAD_MOVES, which holds only refusals. Each is run on a fresh goal; `emits`
# is the step's whole obligation list.
MATCH_ACCEPTS = [
    {"id": "ring_cancels_inv_atom",
     "goal": "Int[x = 1 .. 2] ln(1/x - 1/x + 1) == ?A",
     # goal creation charges the former x # 0 @ [1, 2] (E6) and ln's own
     # 1/x - 1/x + 1 > 0 @ [1, 2] (E26); the range is literal, so no
     # orientation (E4). The ln key's ring normal form is 1 > 0, so its
     # negated goal 1 <= 0 is infeasible by itself and TAG_RULES gives
     # 'linear' with no dom item used.
     "goal_emits": [("x # 0", "[1, 2]", (S_FORMER,), ADMITTED, T_RANGE,
                     True),
                    ("1/x - 1/x + 1 > 0", "[1, 2]", (S_FORMER,), ADMITTED,
                     T_LINEAR, True)],
     "move": ("rewrite", {"entry": "ln_one", "inst": {},
                          "at": "ln(1/x - 1/x + 1)"}),
     "goal_after": "Int[x = 1 .. 2] 0 == ?A",
     "emits": [],
     "why": "ring_nf(inv(x) - inv(x) + 1) = 1 = ring_nf(1), checked with "
            "SymPy with inv(x) a free symbol. The match owes nothing beyond "
            "what the goal's creation charged: x # 0, and ln's domain "
            "1/x - 1/x + 1 > 0 (E26). Contrast BAD_MOVES "
            "rewrite_needs_field, where x*inv(x) does not reduce to 1."},
    {"id": "rewrite_under_infinite_range",
     "goal": "Int[x = 0 .. oo] sqrt(x^2)*exp(-x) == ?A",
     # no divisor in the integrand. Goal creation charges sqrt's domain
     # x^2 >= 0 @ [0, oo) (E26), open at oo, with no orientation (E4). Its
     # tag is sign by E20: range sees x^2 as opaque, and x^2 is an even
     # power with constant 0 on a non-strict goal.
     "goal_emits": [("x^2 >= 0", "[0, oo)", (S_FORMER,), ADMITTED, T_SIGN,
                     True)],
     "move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "x"},
                          "at": "sqrt(x^2)"}),
     "goal_after": "Int[x = 0 .. oo] x*exp(-x) == ?A",
     "emits": [("x >= 0", "[0, oo)", (S_SQRT_SQ,), ADMITTED, T_RANGE,
                True)],
     "why": "E4 with an infinite end: the hypothesis is emitted @ [0, oo), "
            "open at oo, and no orientation obligation `0 <= oo` is "
            "emitted, since that is not a term (§5.1). sqrt(x^2) == x holds "
            "for x >= 0 (SymPy)."},
    # Added (user decision 2026-09-24, review fix): E26's position domains
    # at the two sites no other case inspects, a rewrite's R under an Int
    # and a builtin in an Int's limit. BAD_MOVES assert only refusal codes,
    # so an emission's domain is pinned only by an accepted case.
    {"id": "rewrite_R_former_at_position",
     "goal": "Int[x = 1 .. 2] atan(-ln x) == ?A",
     # installation: ln x owes x > 0 @ [1, 2] (E26); the range is literal,
     # so no orientation (E4). FM: the negated goal x <= 0 with the dom
     # item 1 <= x is infeasible, a dom item used, so range.
     "goal_emits": [("x > 0", "[1, 2]", (S_FORMER,), ADMITTED, T_RANGE,
                     True)],
     "move": ("rewrite", {"entry": "atan_odd", "inst": {"u": "ln x"},
                          "at": "atan(-ln x)"}),
     "goal_after": "Int[x = 1 .. 2] -atan(ln x) == ?A",
     "emits": [("x > 0", "[1, 2]", (S_FORMER,), ADMITTED, T_RANGE, False)],
     "why": "REWRITE_RULE step 10 charges R's formers at the occurrence's "
            "position domain P (the goal's domain plus the enclosing range, "
            "step 7), not at the goal's domain. R = -atan(ln x) re-owes "
            "ln's x > 0 on [1, 2], the key installation minted, so it is "
            "not new. A kernel charging at the goal's domain would emit "
            "x > 0 @ true, a new key, tagged none. atan_odd has no "
            "hypotheses, and the scope check passes because x is bound by "
            "the enclosing Int (step 6). SymPy: atan(-ln x) + atan(ln x) "
            "= 0."},
    # Added (user decision 2026-09-24, review fix): the goal-domain half of
    # step 7's P for step 10's charges of R. In rewrite_R_former_at_position
    # Γ is true, so dropping Γ changes no key there.
    {"id": "rewrite_R_former_at_goal_and_range",
     "goal": "Int[x = 1 .. 2] atan(-ln(x + y)) == ?A @ y > 0",
     # installation: ln(x + y) owes x + y > 0 at P = (y > 0, x in [1, 2]),
     # the goal's domain then the enclosing range (step 7), the interval
     # named since the judgement's free variables are {x, y} (GRAMMAR.md
     # D13, R4). The range is literal, so no orientation (E4). hyp fails:
     # y > 0 alone does not give x + y > 0. FM over the negated goal
     # x + y <= 0 with the dom items y > 0 and 1 <= x <= 2 is infeasible
     # (sum x + y <= 0, 1 - x <= 0 and -y < 0: 1 < 0), with dom items used,
     # so range.
     "goal_emits": [("x + y > 0", "y > 0, x in [1, 2]", (S_FORMER,),
                     ADMITTED, T_RANGE, True)],
     "move": ("rewrite", {"entry": "atan_odd", "inst": {"u": "ln(x + y)"},
                          "at": "atan(-ln(x + y))"}),
     "goal_after": "Int[x = 1 .. 2] -atan(ln(x + y)) == ?A @ y > 0",
     "emits": [("x + y > 0", "y > 0, x in [1, 2]", (S_FORMER,), ADMITTED,
                T_RANGE, False)],
     "why": "step 10 charges R at P = Γ plus the enclosing range (step 7). "
            "R = -atan(ln(x + y)) re-owes the key installation minted, so "
            "it is not new. A kernel that drops Γ emits x + y > 0 on "
            "x in [1, 2] alone: a new key, and FM over {x + y <= 0, "
            "1 <= x <= 2} is feasible (x = 1, y = -5), sign and sign "
            "product see a degree-1 sum with no content and no factor, and "
            "no entry concludes it, so it is tagged none. atan_odd has no "
            "hypotheses. The scope check passes, since y is free in the "
            "goal and x is bound by the enclosing Int (step 6). SymPy: "
            "atan(-ln(x + y)) + atan(ln(x + y)) = 0, and the LP "
            "{x + y <= 0, 1 <= x <= 2, y >= 0} is infeasible."},
    {"id": "limit_former_at_outer_domain",
     "goal": "(Int[t = 0 .. sqrt y] t) + atan(-y) == ?A @ y >= 0",
     # installation: the limit's sqrt y owes y >= 0 at the limit's position
     # domain, which is the goal's, y >= 0. prop is in Γ, so hyp. The body t
     # owes nothing, so no key uses the range [0, sqrt y] and no orientation
     # 0 <= sqrt y is owed (E4, as DEFINEDNESS_MUTATIONS no_sqrt_former's
     # trace of P1.1 reads it).
     "goal_emits": [("y >= 0", "y >= 0", (S_FORMER,), ADMITTED, T_HYP,
                     True)],
     "move": ("rewrite", {"entry": "atan_odd", "inst": {"u": "y"},
                          "at": "atan(-y)"}),
     "goal_after": "(Int[t = 0 .. sqrt y] t) - atan y == ?A @ y >= 0",
     "emits": [],
     "why": "a limit is outside its Int's scope (REWRITE_RULE's "
            "'encloses', GRAMMAR.md §5), so its formers are charged at the "
            "outer position domain and never on [0, sqrt y]. A kernel that "
            "charged it on its own range would emit a key whose domain "
            "carries t's interval, and the orientation 0 <= sqrt y with "
            "it. The move is a plain rewrite outside the Int (R = -atan y "
            "owes nothing), so the case asserts installation's list and "
            "that nothing is re-owed. SymPy: the integral is y/2."},
]

# E2's optional `occurrence`, pinned by one case (not required by
# Done-when). Two sibling integrals over sqrt(t^2); D7 needs the
# parentheses. Without `occurrence` the step acts on both and emits the false
# t >= 0 @ [-1, 0], admitted while discharge is stubbed and tagged none by
# E24. With occurrence := 0
# (the first in pre-order, under Int[t = 0 .. 1]) it emits only
# t >= 0 @ [0, 1]. A rewrite with `occurrence` given has "occurrences": 1.
# Installing the goal charges sqrt's domain on both ranges, t^2 >= 0 @ [0, 1]
# and t^2 >= 0 @ [-1, 0] (E26), both true and tagged sign. The case asserts
# only the rewrite's list, and its t >= 0 keys are new either way.
OCCURRENCE_CASE = {
    "goal": "(Int[t = 0 .. 1] sqrt(t^2)) + (Int[t = -1 .. 0] sqrt(t^2)) == ?A",
    "all": {"move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "t"},
                                 "at": "sqrt(t^2)"}),
            "occurrences": 2,
            "goal_after": "(Int[t = 0 .. 1] t) + (Int[t = -1 .. 0] t) == ?A",
            # t >= 0 @ [-1, 0] is false, and E24 tags it none: the
            # Fourier–Motzkin set {t < 0, -1 <= t, t <= 0} is feasible
            # (t = -1/2), t is no sign-certificate form, sign product does
            # not close >=, and no §6.8 entry concludes t >= 0. This is the
            # positive test that the tagger flags a false obligation. It is
            # outside the no-none assertion, which covers PROOFS runs only.
            "emits": [("t >= 0", "[0, 1]", (S_SQRT_SQ,), ADMITTED, T_RANGE,
                       True),
                      ("t >= 0", "[-1, 0]", (S_SQRT_SQ,), ADMITTED, T_NONE,
                       True)]},
    "one": {"move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "t"},
                                 "at": "sqrt(t^2)", "occurrence": 0}),
            "occurrences": 1,
            "goal_after":
                "(Int[t = 0 .. 1] t) + (Int[t = -1 .. 0] sqrt(t^2)) == ?A",
            "emits": [("t >= 0", "[0, 1]", (S_SQRT_SQ,), ADMITTED, T_RANGE,
                       True)]},
}

# E4 and friends: where the domain of an obligation comes from.
DOMAIN_RULES = (
    "E4 range orientation. Wherever the kernel turns Int[v = lo .. hi] into "
    "an interval on v, it has to know the order of lo and hi. That happens in "
    "rewrite under Int (E1 step 7), in ftc's premises, and in the formers of "
    "a goal's integrand (E6, E26). If lo and hi are both rational literals, "
    "norm_num orders them and the interval is [min, max], with no obligation "
    "recorded. Otherwise the interval is [lo, hi] and the step emits "
    "`lo <= hi`. Reason: [lo, hi] with hi < lo is empty, so every obligation "
    "on it would be vacuously true. That is §5.1's reversed-limit exploit, "
    "and §5.3 method 2 says the range is usable only once the order follows. "
    "For P1.1 this obligation is 0 <= pi/2. It closes only with pi_pos, so it "
    "is where the π gap of revision 9 shows up as a tag. It is first emitted "
    "when the goal is installed, because sqrt(t^2) in the integrand owes "
    "t^2 >= 0 on the range (E26); the fallback's 0 <= pi^2/4 likewise, for "
    "sqrt x. In this milestone a "
    "non-literal reversed range, such as Int[t = pi/2 .. 0], gets the false "
    "obligation pi/2 <= 0. That is admitted with discharge stubbed, and "
    "refused once discharge exists. An `orient` argument is future work. "
    "Infinite ends (§5.1 class b endpoints; GRAMMAR.md §5 and §7): if either "
    "end of Int[v = lo .. hi] is infinite, orientation is determined and no "
    "`lo <= hi` is emitted. PosInf is always the open upper end and NegInf "
    "always the open lower end, whichever limit it was written as (§5.1 "
    "allows reversed limits). With one end infinite and the other a term c, "
    "the interval is [c, oo) or (-oo, c]. With PosInf and NegInf it is "
    "(-oo, oo). With both ends the same infinity the step that builds the "
    "interval (or the goal installation, E6) is refused with "
    "'range-same-infinity': the range is empty, and every obligation on it "
    "would be vacuous. The interval is never closed at an oo end, and "
    "PosInf is only ever its upper end and NegInf its lower (GRAMMAR.md "
    "D18, which the Interval constructor enforces with 'oo-misplaced'; E4 "
    "never trips it, because it orients before it builds). Reason: "
    "`lo <= hi` with hi = oo is not a term "
    "(§5.1 keeps oo out of arithmetic), and [c, oo] cannot exist. Pinned by "
    "MATCH_ACCEPTS rewrite_under_infinite_range.",

    "E5 closed obligations. An obligation whose proposition has no free "
    "variable is emitted with domain true, whatever its position's domain. "
    "This strengthens it, which is always sound, and it lets identical "
    "closed facts share a key: sqrt 3 # 0 is one obligation, not one per "
    "interval. §11.2 already writes it that way.",

    "Open and closed intervals are distinct trees and distinct keys "
    "(GRAMMAR.md §6). ftc's derivative premise and everything deriv and its "
    "check emit are on the open (a, b). The two regularity premises and the "
    "formers of F and of the integrand are on the closed [a, b] (§6.4).",

    "A bare interval in an expected judgement names the judgement's only "
    "free variable (GRAMMAR.md D13, R4).",
)

# E8: how obligations are keyed and merged.
KEYING = (
    "Key = the judgement tree parse_judgement(judgement_string(prop, dom)) "
    "builds: the proposition and its domain tuple, compared structurally, "
    "with bound names literal. There is no canonical orientation (GRAMMAR.md "
    "D12). Each rule mints its obligation in the orientation its own "
    "statement uses. sqrt_sq gives t >= 0, not §11.1's display 0 <= t. The "
    "orientation obligation is lo <= hi. d_ln and d_sqrt give u > 0. field "
    "gives d # 0. E26's formers give ln's u > 0, sqrt's u >= 0, tan's "
    "cos u # 0, asin's and acos's u >= -1 and u <= 1, acosh's u >= 1, and "
    "atanh's u > -1 and u < 1.",

    "Two emissions with one key are one obligation and at most one admission. "
    "The second emission adds its source and does not change the status.",

    "Different domains are different keys: 1 + x^3 # 0 @ [0, 1] (the goal's "
    "former) and 1 + x^3 # 0 @ (0, 1) (field's divisor) are two admissions. "
    "No subsumption is attempted, because weakening one to the other is "
    "discharge work (§6.1 weaken).",

    "Per step, the expected list below gives each key once, with all of that "
    "step's sources for it, and new = True when the key was not in the "
    "tracker before the step. The script compares each step as a set, never "
    "as a sequence.",

    "A refused step emits nothing and leaves the state unchanged (E13).",

    "Obligation propositions are not charged for their own formers, "
    "divisors or partial builtins. Their subterms came from terms already "
    "charged where they entered (E6, E26): tan(pi/2)'s cos(pi/2) # 0 owes "
    "no second 2 # 0, because pi/2 was charged as part of tan(pi/2).",
)


def judgement_string(prop, dom):
    """The parse_judgement input for an obligation. A regularity judgement
    carries its domain inside C^k(...), so its prop is already complete."""
    if " in C^" in prop or dom == "true":
        return prop
    return prop + " @ " + dom


# ---------------------------------------------------------------------------
# 3. The proofs
#
# A step is {"id", "move", "args", "goal_after"}. The script calls
# step(state, move, args) and asserts the goal is goal_after as a tree.
# Moves and their argument shapes:
#
#   ("rewrite", {"entry": str, "inst": {var: term}, "at": term,
#                ["occurrence": int]})                               E1, E2
#   ("fact",    {"entry": str, "inst": {var: term}, "bind": name})  E10
#   ("ftc",     {"F": term, "check": "ring" | "field",
#                "facts": [("handle", name), ...]})                  E9
#   ("close",   {"value": term, "check": "ring" | "field",
#                "facts": [("handle", name), ...]})                  §9
#
# E16. refl, trans and cong (§6.1, in scope per WHAT.md Scope) are not step
# moves in this milestone. They live inside other rules. trans is the linear
# proof state: each accepted step replaces the goal by one proved equal to
# it. cong is REWRITE_RULE step 5, so it inherits rewrite's revision 9 check
# (E11) and is refused by the same 'rewrite-under-D-needs-open-domain'. refl
# is close proving lhs == value by `check` (§9), behind the scope check and
# the `closed` whitelist. Reason: none of P1's proofs needs them as
# standalone moves. Exposing cong as a move would open a second route to §6.1
# rev 9's forbidden case, and that route would need its own must-refuse
# (a 'cong_under_D' BAD_MOVES entry sharing the rewrite code). sym and weaken
# are out for the same reason; weaken appears only as discharge work.
# (User decision 2026-09-24, evaluated answers: refl-by-close is also behind
# E27's evaluated-form check, which runs last, EVALUATED_RULE below.)
#
# "occurrences" records how many places a rewrite acts on (E2). A rewrite
# with `occurrence` given has "occurrences": 1. No P1 step passes it.
#
# E9, ftc. The move takes F and the procedure that checks the derivative
# premise. Before anything is emitted, ftc refuses with
# 'ftc-infinite-endpoint' when lo or hi is PosInf or NegInf (§5.1: oo is
# inadmissible inside arithmetic; §6.4's F(b) - F(a) needs ordinary terms;
# infinite ranges are int_improper's, which this milestone does not
# include; WHAT.md's Scope names no int_improper). By E13 a refused step
# emits nothing (BAD_MOVES ftc_infinite_endpoint). In one step it (i) emits the orientation of [a, b] (E4), (ii)
# emits F's formers on [a, b] (E6), (iii) emits the two regularity premises
# and f in C^0([a, b]) as admissions tagged reg, (iv) runs deriv on F,
# collecting each d_* side condition @ (a, b), (v) runs `check` on
# deriv(F) == f @ (a, b) with the given facts, collecting every divisor @
# (a, b) and every fact's hypotheses, and (vi) on success records the
# derivative premise itself as DISCHARGED, then replaces the goal's integral
# by F[x := b] - F[x := a], which is Add(F[b], Neg(F[a])). There is no
# subtraction node. If check fails, the step is refused with the residual
# deriv(F) - f (WRONG_ANSWERS) and emits nothing (E13). If deriv refuses in
# (iv), for example on a Deriv subterm with x free (E12), the step is refused
# with 'deriv-no-rule' before any substitution. So F[x := b] never meets a D
# that mentions x, and substitution into D (GRAMMAR.md §5) only ever reaches
# its unchanged case (BAD_MOVES ftc_F_contains_D). An x-free subterm of F
# holding an Int or Deriv node is refused in (iv) as well, with
# 'Int-or-D-not-normalisable' (E12's d_const guard, E26 (b); BAD_MOVES
# ftc_F_holds_x_free_Int and ftc_F_holds_x_free_D), so no F holding an Int
# or D gets past (iv) at all.
#
# E10, facts. `fact` instantiates a §6.8 entry and returns a theorem handle
# for `stmt[inst]`, hypotheses included: (sqrt 3)^2 == 3 @ 3 >= 0. It emits
# nothing. A step that uses the handle inherits its hypotheses as obligations
# (WHAT.md: "the result inherits each fact's obligations"), and its inst
# values' formers (E6, E26 (a)), charged at that step's domain. The
# statement's own formers are not re-charged (the §6.8 library is trusted).
# A raw judgement
# where a handle is expected is refused (BAD_MOVES field_raw_fact).
#
# §9, close. The move checks the scope of `value`, then the `closed`
# whitelist, then proves `lhs == value` with `check`, emitting that
# procedure's obligations and the value's formers. The theorem reported is
# the ORIGINAL goal with ?A := value. Last of all (user decision 2026-09-24,
# evaluated answers), E27 refuses a value that is not fully evaluated
# (EVALUATED_RULE, after E19 below).
# E23, interpreting §9 "The `closed` schema, as a whitelist":
#   * The whitelist admits these node kinds: Num, Const (pi, e_const), Var,
#     Neg, Add, Mul, Div, Pow, RPow, and App over the sixteen builtins (sin
#     cos tan asin acos atan exp ln sqrt abs sinh cosh tanh asinh acosh
#     atanh; abs is admitted in goals, §5.1 rev 6).
#   * It refuses Call (declared symbols, per §9's "declared symbols
#     excluded"), Deriv, Integral and MVar. Sum and lim are not in this
#     milestone's grammar (GRAMMAR.md D2).
#   * Var is admitted, although §9's list does not name variables. §5.1
#     lists `x variable` among the term formers §9 points to. §9's
#     exclusions target opaque and non-elementary nodes, not leaves. An
#     answer stated in a goal's free variables (a D goal, as in BAD_MOVES
#     close_D_goal_scope_passes) needs Var. Bound names are handled by the
#     trusted scope check (E19), which runs first, so the untrusted
#     whitelist needs no variable rule.
#   * The check runs on the raw value, before any unfolding (§9).
#   * Every goal in PROOFS, BAD_MOVES, MATCH_ACCEPTS and the forgery bank
#     carries `answer schema closed` (as §11 declares for P1.1 and P1.2),
#     with no `+ f` extensions. So 'close-schema-not-closed' fires only for
#     a value with a node outside the list above.
#   If Var were excluded instead, close_D_goal_scope_passes would expect
#   'close-schema-not-closed', or would use a value with no variable (`2`,
#   which ring also fails to match against the opaque D atom).
# E19, the scope check: fv(value) ∩ bv(ORIGINAL goal) = ∅ (GRAMMAR.md §5
# bv; D's variable is not in bv, so ?A := 2*x passes for D[x] x^2 == ?A,
# BAD_MOVES close_D_goal_scope_passes). That goal is the one the reported theorem instantiates, not
# the current goal, which ftc may already have stripped of its binders.
# GRAMMAR.md D11 must hold of the reported theorem, and D11 makes this a name
# check. Decision, interpreting §9 and §15.2 item 1: the check is trusted, so
# it must not depend on the untrusted whitelist or on `check` failing to
# catch a bound name (BAD_MOVES close_bound_variable_after_ftc and
# close_bound_variable_ring_true).

# E27, the evaluated-form check (user decision 2026-09-24, evaluated
# answers). Stated as REWRITE_RULE is, one paragraph per point, so that the
# cases in BAD_MOVES (the e27_* entries) and EVALUATED_ACCEPTS are checks of
# a stated rule and not fitted to an implementation.
EVALUATED_RULE = (
    "The rule. A value closing a goal under the `closed` schema (every goal "
    "in this file and in problems/stage0, E23) must be FULLY EVALUATED: "
    "(a) no subterm of it can still be evaluated by an equation entry in "
    "force, and (b) it contains no unreduced literal arithmetic. Otherwise "
    "close is refused 'close-not-evaluated', naming one offending subterm "
    "and, for (a), the entry that still applies. 'Fully evaluated' is a "
    "checkable PROPERTY, the absence of a redex, and not a canonical form: "
    "equality of closed constants is undecidable in general, and a "
    "canonical form would reject one of P1.2's two accepted answers "
    "(ring's normal form of pi/(3*sqrt 3) is pi*inv(3*sqrt 3), of "
    "pi*sqrt 3 / 9 it is (1/9)*pi*sqrt 3, and each is a legitimate way to "
    "print the value). So E27 never compares the value with its own ring "
    "normal form or with any printout, and no test below depends on the "
    "order of summands or factors. The check only reads the value: it "
    "never rewrites, simplifies or normalises it in the goal. The learner "
    "makes the rewrite moves (§2), and E27 names the one still available.",

    "Reasons. (i) §9: an unrestricted ?A is vacuous, and the whitelist "
    "(E23) removed refl's Int. But after ftc the goal's own F(b) - F(a) is "
    "itself a whitelisted value, so closing with the current left side is "
    "refl again one step later, and the theorem says no more than ftc "
    "did. S2 closed as (exp 1 - exp 0)/2 and S3 as (ln e_const)^2/2 - "
    "(ln 1)^2/2 using no §6.8 entry (stage 0 FINDINGS 12); P1.1 at s2 "
    "would close the same way with its own left side (BAD_MOVES "
    "e27_goal_lhs_after_ftc). §9's reading of `closed`, 'this integral "
    "has an elementary closed form, and it is this one', needs the form "
    "evaluated. (ii) §6.8: 'no ftc step closes without evaluating F at "
    "both endpoints, so every authored goal terminates in this table'. "
    "Before E27 nothing enforced that; with (a) it holds of every accepted "
    "close, relative to the entries in force. (iii) The user's decision of "
    "2026-09-24: answers under `closed` must be fully evaluated.",

    "Placement. E27 lives with the closed whitelist in schema.py and is "
    "UNTRUSTED (§9: 'the schema checker is not in the trusted base'; "
    "ARCHITECTURE.md §1). It can only refuse, never prove: a bug in it can "
    "refuse a good answer or accept an unevaluated one, and neither is a "
    "false theorem, because the value it passes was already proved equal "
    "to the goal's left side by the trusted check. To test (a) and (b) it "
    "needs §6.2's ring normal form (E1 step 4, E3) and the read-only "
    "entries.ENTRIES, so schema.py imports them, as tagger.py already "
    "does.",

    "Order in close, and which refusal wins. close runs: 'bad-args' (an "
    "MVar or oo in the value); E19's scope check, trusted "
    "('close-scope-bound-variable'); E23's whitelist, untrusted "
    "('close-schema-not-closed'); the value's formers, E6, E25, E26 and "
    "E7 ('divisor-normalises-to-zero', 'obligation-refuted'); the check "
    "('close-check-failed', 'Int-or-D-not-normalisable', the fact "
    "refusals); check_goal on the theorem ('D5-uncalled' and the other "
    "GRAMMAR.md §1 codes); and LAST, E27 ('close-not-evaluated'). Only a "
    "value that passes all of them closes the goal. Any earlier refusal "
    "wins. Reasons: (1) E27 is untrusted and can only turn an acceptance "
    "into a refusal. Run last, it cannot change which trusted refusal any "
    "move gets, and every existing case keeps its code: "
    "close_bound_variable_ring_true's t - t + 2, which E27 alone would "
    "refuse (b2), stays 'close-scope-bound-variable'; "
    "close_value_owes_domain's 0*ln(-1) (b3) stays 'obligation-refuted'; "
    "and the suite's close_theorem_check value f - f (b2) stays "
    "'D5-uncalled'. (2) The code then means one thing: the value WAS "
    "proved equal to the goal's left side, and only its form is refused. "
    "The refusal is about form, not truth, and a wrong, unevaluated value "
    "is reported wrong, with its residual, which is the more useful "
    "feedback (BAD_MOVES e27_check_failed_wins). (3) E23 precedes the check "
    "because without it refl closes anything; E27 needs no such place, "
    "because what it refuses has already been proved, and a refused step "
    "emits nothing (E13), so the check's emissions are discarded. E19 "
    "running first also means E27 never sees a bound name, and E23 "
    "running first means it never sees an Int, D, Call or MVar, so its "
    "ring normal forms never refuse 'Int-or-D-not-normalisable'. The cost: "
    "the check runs on a value E27 then refuses.",

    "(a) Entries. The entries in force are entries.ENTRIES at the time of "
    "the check. Those whose statement is an equation L == R take part "
    "(today eleven: all but pi_pos, sqrt_pos and e_gt_one; thirteen once "
    "cos_zero and sqrt_zero are pinned, E35: sqrt_zero immediately before "
    "sqrt_sq, which makes it the first entry, and cos_zero appended last, "
    "after exp_one). Every subterm s "
    "of the value is tested against each, in ENTRIES order, and the first "
    "that COUNTS at s is the one named. The matching notion is rewrite's, "
    "E1 steps 3 and 4: an application is matched through the ring normal "
    "forms of its argument (E3's inv atoms included), never through field. "
    "Per kind of entry:",

    "(a1) No schema variable, L = h(p), an application: ln_one, ln_e, "
    "exp_zero, exp_one, sin_zero, sin_pi_half, cos_pi_half, "
    "atan_one_sqrt3, and, once pinned (E35), cos_zero and sqrt_zero. "
    "Because sqrt_zero precedes sqrt_sq in ENTRIES, sqrt 0 (refused "
    "already, by sqrt_sq's (a2) reading) is refused naming the direct "
    "move sqrt_zero; cos 0 is refused naming cos_zero, the only entry "
    "that counts there. It counts at s exactly when E1 step 3 accepts: s is "
    "h(b) for the same builtin h and ring_nf(b) == ring_nf(p). So "
    "exp(0^2), exp(1 - 1), exp(x - x), exp(0*x), exp(1^2) and "
    "ln(1/x - 1/x + 1) count, and ln(x/x) does not (MATCH_ACCEPTS "
    "ring_cancels_inv_atom, BAD_MOVES rewrite_needs_field). Why the "
    "normalised matching and not tree matching: close checks by ring or "
    "field, which identify atoms up to their arguments' normal forms "
    "(§6.2), so a tree-only (a) would be evaded by writing exp(1^2) for "
    "exp 1, which is what S2's ftc actually produces. With (a) matching up "
    "to the same normal form, such an entry's left side survives in every "
    "value ring-equal to the goal's side unless it cancels out.",

    "(a2) With schema variables. E1 step 3 takes inst from the learner. "
    "The check has to find one, and for atan_odd E1 step 3 alone matches "
    "EVERY atan b (u := -b), which would refuse atan 2 and never "
    "terminate. So each schema entry in force has a stated reading, "
    "chosen so that the named move is available and makes progress: "
    "sqrt_sq (sqrt(u^2) == u @ u >= 0) counts at s = sqrt b when "
    "ring_nf(b) is c*c for some polynomial c over Q[atoms] every atom of "
    "which is closed (no free variable): sqrt 0, sqrt 1, sqrt 4, "
    "sqrt(1/4), sqrt(pi^2/4) (§18 Q21's own example, which P1.1-fallback "
    "s2 rewrites), sqrt((pi - 4)^2). The test is order-independent and "
    "decidable (square-free factorisation of ring_nf(b), or any "
    "polynomial square-root test). For a closed c one of c and -c is "
    ">= 0, and E1 step 3 accepts either (ring_nf(c^2) = ring_nf((-c)^2)), "
    "so a move whose hypothesis is true exists. Whether the tagger can "
    "close it is not E27's concern: for sqrt((pi - 4)^2), u := 4 - pi owes "
    "4 - pi >= 0, true but tagged none until discharge exists. When c has "
    "a free variable neither sign need satisfy u >= 0 and no abs entry is "
    "in force, so sqrt(y^2) does not count. "
    "atan_odd (atan(-u) == -atan u) counts at s = atan b when ring_nf(b) "
    "is nonzero and every one of its rational coefficients is negative: "
    "atan(-1/sqrt 3), atan(-1), atan(1 - 2), atan(-x). The move is "
    "u := -b, and its result -atan(-b) has every coefficient positive, so "
    "it cannot apply again. A structural reading, atan(Neg c), would miss "
    "atan(-1/sqrt 3), which parses as atan(Div(Neg 1, sqrt 3)) (GRAMMAR.md "
    "D9), P1.2's own case at s7. "
    "sqrt_sq_val ((sqrt a)^2 == a @ a >= 0) counts at s = Pow(sqrt b, n) "
    "with |n| >= 2: for n = 2 this is E1 step 3's tree case (L is not an "
    "application), and the entry is only ever used as a fact for field "
    "(§6.8 rev 7), whose fact reduction lowers every such power, negative "
    "ones included: (sqrt 2)^3 is 2*sqrt 2 and (sqrt 2)^(-2) is 1/2 by "
    "field with the fact. (Review fix: the reading was n >= 2, which "
    "accepted (sqrt 3)^(-2).) a := b, and its hypothesis b >= 0 is the "
    "domain condition the value's own sqrt b already owes (E26), so the "
    "move owes nothing new; a negative power also owes sqrt b # 0, which "
    "the value owes too (E6). "
    "A schema entry added later with no reading here is read "
    "structurally: L is matched against s as a tree pattern whose schema "
    "variables match any subterm (the same one at each occurrence), and "
    "E1 step 3 then accepts at that inst. An entry whose structural "
    "reading misses its normalised disguises, as atan_odd's would, or "
    "matches everything, must state its reading here when it is added.",

    "(a3) What (a) guarantees. Every (a) refusal names a move the learner "
    "can make at that subterm: a rewrite with the entry (for sqrt_sq_val, "
    "the fact in close's or ftc's field check), with no hypothesis, a "
    "closed true one (sqrt_sq), or one the value already owes "
    "(sqrt_sq_val). Every entry's own right side passes E27 (1, 0, "
    "e_const, pi/6, -atan u, u, a), so the entries do not undo each "
    "other. Adding an entry can only tighten (a). A reference proof that "
    "closed on a form a new entry evaluates is then refused, and item 7's "
    "re-run of the problem files is what finds it.",

    "(b) Literal arithmetic: definitions. A RATIONAL LITERAL is a tree of "
    "one of five shapes: Num n (n >= 0); Neg(Num n) with n >= 1; and "
    "Div(Num p, Num q), Neg(Div(Num p, Num q)) or Div(Neg(Num p), Num q), "
    "each with p >= 1, q >= 2 and gcd(p, q) = 1. These are lit(q)'s shapes "
    "(GRAMMAR.md §7) plus the parser's -p/q (D9 binds unary minus tighter "
    "than /). So 0, 2, -3, 1/2, -1/2 and -(1/2) are rational literals, and "
    "2/4, 4/2, 3/1, 0/5, -0 and -(-3) are not. A LITERAL TERM is a tree "
    "built from Num by Neg, Add, Mul, Div and Pow alone (Pow's integer "
    "exponent is a field of the node, not a subterm). RPow and App are "
    "never literal terms, whatever their arguments. SUM FLATTENING: "
    "summands(Add(a, b)) = summands(a) followed by summands(b); "
    "summands(Neg a) = summands(a) with every sign flipped; a rational "
    "literal, and any other node, is one summand. A sum node is an Add, "
    "or a Neg that is not a rational literal. A maximal sum is a sum node "
    "whose parent is not a sum node. PRODUCT FLATTENING: factors(Mul(a, "
    "b)) = factors(a) followed by factors(b); factors(Div(a, b)) = "
    "factors(a) followed by factors(b) with every side swapped; a rational "
    "literal, and any other node (a Neg included), is one factor, on the "
    "numerator or the denominator side. A product node is a Mul, or a Div "
    "that is not a rational literal. A maximal product is a product node "
    "whose parent is not a product node. A factor Pow(c, n) that is not a "
    "literal term has base c and, when n < 0, counts on the opposite side "
    "in EVERY test of b3, not only in (v): so in 1*pi^(-1) the 1 is the "
    "only numerator factor, as in 1/pi, and in pi*pi^(-1) the two pi "
    "factors are on opposite sides, as in pi/pi. Any other factor is its "
    "own base. Neither flattening reorders anything, and every test below "
    "is symmetric in the order of summands and of factors, so (b) never "
    "prefers one printed order.",

    "(b) Literal arithmetic: the tests. Each is arithmetic ring would do "
    "on literals, on coefficients or on exponents, within one sum, one "
    "product or one power. "
    "(b1) A maximal literal term (its parent is not a literal term) that "
    "is not a rational literal: 1 + 1, 2 - 0, 1^2, 2/4, 2*3, 0^2, "
    "1/2 + 1/3, 2^(-1). "
    "(b2) A maximal sum in which some summand's ring normal form is 0 "
    "(pi + 0, 2*1 - 2*(pi/2)*0), or in which the ring normal form of the "
    "whole sum has FEWER MONOMIALS than the ring normal forms of its "
    "summands have in total, so that ring would merge or cancel monomials "
    "across summands. The count is a property of normal forms, so it "
    "depends on no order. It covers two literals (pi + 1 + 1) and like "
    "terms, summands that are rational multiples of each other (pi + pi, "
    "pi/2 + pi/3, x - x, t - t + 2), and also summands that are sums "
    "once normalised and share a monomial with another summand: "
    "2*(pi + 1) - 2 (2*pi + 2 and -2: three monomials, and the sum has "
    "one), (e_const + 1)/2 - 1/2, 2*(pi + 1) - 2*pi, (pi + 1)/2 - pi/2, "
    "2*(e_const - 1) - 2*e_const, (pi + 1)^2 - 1. (Review fix: b2 was the "
    "zero test and the multiples test alone, which accepted these; the "
    "count subsumes the multiples test.) The zero test stays, because a "
    "zero summand adds no monomial to either count. Summands whose "
    "monomials stay distinct pass however they are factored: "
    "x*exp(x) - exp(x) (x*exp(x) and exp(x) are different monomials), "
    "(e_const - 1)/2 + pi. "
    "(b3) A maximal product with (i) a literal factor 0 (0*pi); (ii) a "
    "literal factor 1 or -1, unless it is the product's only numerator "
    "factor (1*pi, pi/1 and -1*pi are refused; 1/sqrt 3, -1/sqrt 3 and "
    "1/(3*sqrt 3) are not); (iii) two literal factors on one side "
    "(2*3*pi, pi/(2*3)); (iv) a denominator literal that is not Num n with "
    "n >= 2 (pi/(1/2), pi/(-2)), or a numerator literal a beside a "
    "denominator literal b where a is not an integer literal (Num or "
    "Neg(Num)) or gcd(|a|, b) is not 1 (2*pi/(4*sqrt 3), (1/2)*pi/3; "
    "2*pi/(3*sqrt 3) passes); or (v) two non-literal factors on one side "
    "whose bases have equal ring normal forms (pi*pi, pi*pi^2, "
    "sqrt 3*sqrt 3). Factors on opposite sides are never compared "
    "(pi/pi, x/x): cancelling them is field's work and owes a divisor "
    "(E3). "
    "(b4) A Pow(c, n) with n = 0 or n = 1 (pi^0, pi^1), or whose base c "
    "is a Pow or a Neg that is not a rational literal ((pi^2)^3, "
    "(-pi)^2); or a Neg directly over a Neg (-(-pi); pi - (-x), which is "
    "Add(pi, Neg(Neg x)), GRAMMAR.md D9). "
    "(b) never looks through a sum or a product into a power, or "
    "distributes a product over a sum, so factored forms pass: "
    "(e_const - 1)/2, (2*pi)^2, -(pi + 1).",

    "The reference answers pass. 2 and 1/2 are rational literals. "
    "(e_const - 1)/2: one product (factors e_const - 1 over 2), one sum "
    "(e_const and the literal -1, not multiples). (1/3)*ln 2 + "
    "pi/(3*sqrt 3): the sum's summands normalise to (1/3)*ln 2 and "
    "pi*inv(3*sqrt 3), not multiples; (1/3)*ln 2 has the one literal 1/3; "
    "pi/(3*sqrt 3) has one literal, 3, below; ln 2 and sqrt 3 match no "
    "entry (2 is not 1, 3 is not a rational square). "
    "(1/3)*ln 2 + pi*sqrt 3 / 9: the same, with pi*sqrt 3 / 9 one product "
    "whose only literal is the 9 below. b2's monomial count (review fix): "
    "e_const - 1, 1 + 1 monomials against 2 for the sum; both P1.2 forms, "
    "1 + 1 against 2; e_const/2 - 1/2, 1 + 1 against 2; so nothing merges.",

    "Reporting. E27 searches (a) over the whole value first, in pre-order "
    "(GRAMMAR.md §7's field order, terms.children), trying the entries in "
    "ENTRIES order at each node, and reports the first node where one "
    "counts. Only if there is none does it search (b), in pre-order, "
    "trying b1 to b4 at each node, and report the first node where one "
    "fires: for b1 the literal term, for b2 the maximal sum, for b3 the "
    "maximal product, for b4 the Pow or the outer Neg. (a) goes first "
    "because it names a move, and an entry's result often creates (b)'s "
    "literal arithmetic (2*sin(pi/2) becomes 2*1), so reporting (b) first "
    "would be premature. The refusal is Refusal('close-not-evaluated', "
    "message, residual), where residual is the offending subterm itself, "
    "a subtree of the value, and message is E27_MESSAGES[clause] with "
    "term := show(residual) and, for (a), entry := the entry's name. The "
    "script asserts the code, that parse_term(at) == residual as trees, "
    "and that the message equals the template so filled. It asserts the "
    "printer's output only through that template (PRINT_EXACT's "
    "convention); each case's 'message' is the filled string, written out "
    "for the reader.",

    "Known limitations: accepted, by design, not bugs. E27 refuses only "
    "what (a) and (b) name, so an unevaluated value they do not name is "
    "accepted. The ones worth knowing: ln 2 + ln 3 (ln 6 needs log_mul, "
    "which is not in force, and ln 2 and ln 3 are distinct atoms, so the "
    "sum is ring-irreducible); sqrt 8 (2*sqrt 2 needs a product law for "
    "sqrt, not in force); any builtin at a point with no "
    "entry in force (cos 0 was the example until cos_zero was pinned, "
    "E35: it moves to the refused cases, DISCHARGE_E27_CHANGES) ('evaluated' is relative to ENTRIES, and tightens as "
    "§6.8's enumeration lands); sqrt(y^2) with y free (see (a2)); pi/pi "
    "and x/x (field's cancellation, (b3)); (1 + sqrt 3)^2 (4 + 2*sqrt 3 "
    "needs expansion, then the fact); pi/(3*sqrt 3) + pi*sqrt 3 / 9 (the "
    "two summands are alike only through sqrt_sq_val, not in ring); "
    "atan(1 - pi) (atan_odd counts only when every coefficient is "
    "negative; the sign of a mixed sum is not decided); -(2*pi)*3 "
    "(product flattening stops at a Neg that is not a rational literal; "
    "-2*pi*3, the way D9 parses the usual spelling, is refused); and "
    "sqrt 3*sqrt 3, refused by b3 (v) with (b)'s message rather than "
    "naming sqrt_sq_val. EVALUATED_ACCEPTS pins the first nine (the "
    "first eight once cos 0 moves, E35), and "
    "(2*pi)^2 for (b)'s factored forms. "
    "Added in review (each a missing §6.8 entry or a form the stated tests "
    "do not reach, not a change to the rule): exp(ln 2), ln(exp 2) and "
    "ln(e_const^2), since no inverse-pair or log-power entry is in force; "
    "sin(pi), cos(pi), sin(pi/6), atan 0, atan 1, atan(sqrt 3) and cos 0 "
    "(cos 0 until cos_zero is pinned, E35), "
    "table values §6.8 enumerates but entries.py does not yet hold "
    "(atan 0 also shows that atan_odd needs a NONZERO argument: every "
    "coefficient of the zero polynomial is vacuously negative); "
    "atan(sqrt 3/3), whose argument normalises to (1/3)*sqrt 3 and not to "
    "inv(sqrt 3), so atan_one_sqrt3 does not match it, consistently with "
    "E1 (ring never identifies sqrt 3 * inv(sqrt 3) with 1); the RPow "
    "forms 4^(1/2) and (pi^2)^(1/2), since an RPow is an atom and never a "
    "literal term, and b4 reads only Pow; (1/sqrt 3)^2 and "
    "(pi*sqrt 3)^2, since sqrt_sq_val counts only at a power whose base "
    "IS sqrt b, and (b) never expands a power; (pi - 1)*(1 - pi), whose "
    "bases differ by sign and so do not have equal normal forms (b3 (v)); "
    "and pi*pi^(-1) and 1*pi^(-1), where the negative power counts on the "
    "denominator side, so these read as pi/pi and 1/pi (b3). "
    "EVALUATED_ACCEPTS pins atan 0 and pi*pi^(-1), the two branches no "
    "other case reached.",

    "Deliberate canonicalisation (the owner keeps it, review 2026-09-24). "
    "Two refusals are not evaluation but a choice of normal form for sign "
    "and division, within the decision that closed answers be in normal "
    "form: atan(-1/2) is refused (atan_odd) and must be written "
    "-atan(1/2), and pi*(1/sqrt 3) is refused (b3 (ii): the literal 1 is "
    "not the only numerator factor) and must be written pi/sqrt 3. Both "
    "values are right, and no table value is missing; E27 simply puts a "
    "negation outside atan and a divisor below the division line. They are "
    "deliberate, not bugs.",
)

# The two refusal messages. `term` is show(the offending subterm), `entry`
# the entry's name. Asserted by filling the template, never as a literal
# printout (EVALUATED_RULE, Reporting).
E27_MESSAGES = {
    "a": "{term} can still be evaluated ({entry})",
    "b": "{term} is unreduced literal arithmetic",
}

P1_1_GOAL ="Int[t = 0 .. pi/2] sin(sqrt(t^2))*(2*t) == ?A"
P1_1_F = "2*sin t - 2*t*cos t"
P1_1_AFTER_FTC = (
    "2*sin(pi/2) - 2*(pi/2)*cos(pi/2) - (2*sin 0 - 2*0*cos 0) == ?A")

P1_1_FALLBACK_GOAL = "Int[x = 0 .. pi^2/4] sin(sqrt x) == ?A"
P1_1_FALLBACK_F = "2*sin(sqrt x) - 2*sqrt x * cos(sqrt x)"

P1_2_GOAL = "Int[x = 0 .. 1] 1/(1 + x^3) == ?A"
P1_2_F = ("(1/3)*ln(1 + x) - (1/6)*ln(x^2 - x + 1)"
          " + (1/sqrt 3)*atan((2*x - 1)/sqrt 3)")
# F[x := 1] and F[x := 0], literally substituted. §18 Q21's point: none of
# ln(1 + 0), ln(1^2 - 1 + 1), atan((2*1 - 1)/sqrt 3) is syntactically a §6.8
# left-hand side.
P1_2_F1 = ("(1/3)*ln(1 + 1) - (1/6)*ln(1^2 - 1 + 1)"
           " + (1/sqrt 3)*atan((2*1 - 1)/sqrt 3)")
P1_2_F0 = ("(1/3)*ln(1 + 0) - (1/6)*ln(0^2 - 0 + 1)"
           " + (1/sqrt 3)*atan((2*0 - 1)/sqrt 3)")
P1_2_ANSWER = "(1/3)*ln 2 + pi/(3*sqrt 3)"
P1_2_ANSWER_ALT = "(1/3)*ln 2 + pi*sqrt 3 / 9"
P1_2_BEFORE_CLOSE = (
    "(1/3)*ln(1 + 1) - (1/6)*0 + (1/sqrt 3)*(pi/6)"
    " - ((1/3)*0 - (1/6)*0 + (1/sqrt 3)*(-(pi/6))) == ?A")

PROOFS = {
    # WHAT.md "The route": P1.1 starts from §11.1's substituted goal, and
    # int_subst waits for the next step. So what this proves is the t-form.
    # It does not prove the original Int[x = 0 .. pi^2/4] sin(sqrt x) until
    # int_subst exists. The fallback below proves that one directly.
    "P1.1": {
        "fallback": False,
        "goal": P1_1_GOAL,
        "steps": [
            {"id": "s1", "move": "rewrite",
             "args": {"entry": "sqrt_sq", "inst": {"u": "t"},
                      "at": "sqrt(t^2)"},
             "occurrences": 1,
             # The binder case: u := t names the variable bound by the
             # enclosing Int, and the hypothesis t >= 0 is emitted on the
             # range [0, pi/2] (E1 steps 6-8, §6.1: under Int the range
             # domain is enough).
             "goal_after": "Int[t = 0 .. pi/2] sin t * (2*t) == ?A"},
            {"id": "s2", "move": "ftc",
             "args": {"F": P1_1_F, "check": "ring", "facts": []},
             "goal_after": P1_1_AFTER_FTC},
            {"id": "s3", "move": "rewrite",
             "args": {"entry": "sin_pi_half", "inst": {}, "at": "sin(pi/2)"},
             "occurrences": 1,
             "goal_after":
                 "2*1 - 2*(pi/2)*cos(pi/2) - (2*sin 0 - 2*0*cos 0) == ?A"},
            {"id": "s4", "move": "rewrite",
             "args": {"entry": "cos_pi_half", "inst": {}, "at": "cos(pi/2)"},
             "occurrences": 1,
             "goal_after": "2*1 - 2*(pi/2)*0 - (2*sin 0 - 2*0*cos 0) == ?A"},
            {"id": "s5", "move": "rewrite",
             "args": {"entry": "sin_zero", "inst": {}, "at": "sin 0"},
             "occurrences": 1,
             "goal_after": "2*1 - 2*(pi/2)*0 - (2*0 - 2*0*cos 0) == ?A"},
            # ring: 2 - 0 - (0 - 0) == 2. The atom cos 0 is multiplied by 0,
            # so no cos_zero is needed (§11.1 rev 9). pi/2 is a coefficient
            # times the opaque pi, and ring emits nothing (§6.2).
            {"id": "s6", "move": "close",
             "args": {"value": "2", "check": "ring", "facts": []},
             "goal_after": None},
        ],
        "theorem": "Int[t = 0 .. pi/2] sin(sqrt(t^2))*(2*t) == 2",
    },

    # WHAT.md's fallback: direct on x. It never uses sqrt_sq on a bound
    # variable. Recorded, not the route.
    "P1.1-fallback": {
        "fallback": True,
        "goal": P1_1_FALLBACK_GOAL,
        "steps": [
            {"id": "s1", "move": "ftc",
             "args": {"F": P1_1_FALLBACK_F, "check": "field", "facts": []},
             "goal_after":
                 "2*sin(sqrt(pi^2/4)) - 2*sqrt(pi^2/4)*cos(sqrt(pi^2/4))"
                 " - (2*sin(sqrt 0) - 2*sqrt 0 * cos(sqrt 0)) == ?A"},
            # Q21's third example. ring_nf((pi/2)^2) = (1/4)*pi^2 =
            # ring_nf(pi^2/4). Not under a binder, so the hypothesis is the
            # closed pi/2 >= 0, which needs pi_pos (WHAT.md).
            {"id": "s2", "move": "rewrite",
             "args": {"entry": "sqrt_sq", "inst": {"u": "pi/2"},
                      "at": "sqrt(pi^2/4)"},
             "occurrences": 3,
             "goal_after":
                 "2*sin(pi/2) - 2*(pi/2)*cos(pi/2)"
                 " - (2*sin(sqrt 0) - 2*sqrt 0 * cos(sqrt 0)) == ?A"},
            # ring_nf(0^2) = 0 = ring_nf(0), and the hypothesis 0 >= 0 is
            # closed by norm_num. This is why no sqrt_zero entry is needed.
            # The key is not new: s1's goal already owed 0 >= 0 for its
            # sqrt 0 (E26).
            {"id": "s3", "move": "rewrite",
             "args": {"entry": "sqrt_sq", "inst": {"u": "0"}, "at": "sqrt 0"},
             "occurrences": 3,
             "goal_after": P1_1_AFTER_FTC},
            {"id": "s4", "move": "rewrite",
             "args": {"entry": "sin_pi_half", "inst": {}, "at": "sin(pi/2)"},
             "occurrences": 1,
             "goal_after":
                 "2*1 - 2*(pi/2)*cos(pi/2) - (2*sin 0 - 2*0*cos 0) == ?A"},
            {"id": "s5", "move": "rewrite",
             "args": {"entry": "cos_pi_half", "inst": {}, "at": "cos(pi/2)"},
             "occurrences": 1,
             "goal_after": "2*1 - 2*(pi/2)*0 - (2*sin 0 - 2*0*cos 0) == ?A"},
            {"id": "s6", "move": "rewrite",
             "args": {"entry": "sin_zero", "inst": {}, "at": "sin 0"},
             "occurrences": 1,
             "goal_after": "2*1 - 2*(pi/2)*0 - (2*0 - 2*0*cos 0) == ?A"},
            {"id": "s7", "move": "close",
             "args": {"value": "2", "check": "ring", "facts": []},
             "goal_after": None},
        ],
        "theorem": "Int[x = 0 .. pi^2/4] sin(sqrt x) == 2",
    },

    # §11.2 as revision 9 states it. The approx step is stage 2 and is out
    # (WHAT.md Scope).
    "P1.2": {
        "fallback": False,
        "goal": P1_2_GOAL,
        "steps": [
            {"id": "s1", "move": "fact",
             "args": {"entry": "sqrt_sq_val", "inst": {"a": "3"},
                      "bind": "h_sqrt3"},
             "conclusion": "(sqrt 3)^2 == 3 @ 3 >= 0",
             "goal_after": P1_2_GOAL},
            # WHAT.md: "the check field [sqrt_sq_val 3]". The fact goes into
            # field, not in front of it (§6.2, §11.2 rev 7).
            {"id": "s2", "move": "ftc",
             "args": {"F": P1_2_F, "check": "field",
                      "facts": [("handle", "h_sqrt3")]},
             "goal_after": P1_2_F1 + " - (" + P1_2_F0 + ") == ?A"},
            # ln_one fires at three different subterms. Each is its own step,
            # because each has its own target.
            {"id": "s3", "move": "rewrite",
             "args": {"entry": "ln_one", "inst": {},
                      "at": "ln(1^2 - 1 + 1)"},
             "occurrences": 1,
             "goal_after":
                 "(1/3)*ln(1 + 1) - (1/6)*0"
                 " + (1/sqrt 3)*atan((2*1 - 1)/sqrt 3) - (" + P1_2_F0 + ") == ?A"},
            {"id": "s4", "move": "rewrite",
             "args": {"entry": "ln_one", "inst": {}, "at": "ln(1 + 0)"},
             "occurrences": 1,
             "goal_after":
                 "(1/3)*ln(1 + 1) - (1/6)*0"
                 " + (1/sqrt 3)*atan((2*1 - 1)/sqrt 3)"
                 " - ((1/3)*0 - (1/6)*ln(0^2 - 0 + 1)"
                 " + (1/sqrt 3)*atan((2*0 - 1)/sqrt 3)) == ?A"},
            {"id": "s5", "move": "rewrite",
             "args": {"entry": "ln_one", "inst": {},
                      "at": "ln(0^2 - 0 + 1)"},
             "occurrences": 1,
             "goal_after":
                 "(1/3)*ln(1 + 1) - (1/6)*0"
                 " + (1/sqrt 3)*atan((2*1 - 1)/sqrt 3)"
                 " - ((1/3)*0 - (1/6)*0"
                 " + (1/sqrt 3)*atan((2*0 - 1)/sqrt 3)) == ?A"},
            # ring_nf((2*1 - 1)/sqrt 3) = 1 * inv(sqrt 3) = ring_nf(1/sqrt 3)
            # (E3).
            {"id": "s6", "move": "rewrite",
             "args": {"entry": "atan_one_sqrt3", "inst": {},
                      "at": "atan((2*1 - 1)/sqrt 3)"},
             "occurrences": 1,
             "goal_after":
                 "(1/3)*ln(1 + 1) - (1/6)*0 + (1/sqrt 3)*(pi/6)"
                 " - ((1/3)*0 - (1/6)*0"
                 " + (1/sqrt 3)*atan((2*0 - 1)/sqrt 3)) == ?A"},
            # ring_nf((2*0 - 1)/sqrt 3) = -1 * inv(sqrt 3) =
            # ring_nf(-(1/sqrt 3)). u := 1/sqrt 3 is chosen so that the
            # result is literally atan_one_sqrt3's left-hand side.
            {"id": "s7", "move": "rewrite",
             "args": {"entry": "atan_odd", "inst": {"u": "1/sqrt 3"},
                      "at": "atan((2*0 - 1)/sqrt 3)"},
             "occurrences": 1,
             "goal_after":
                 "(1/3)*ln(1 + 1) - (1/6)*0 + (1/sqrt 3)*(pi/6)"
                 " - ((1/3)*0 - (1/6)*0"
                 " + (1/sqrt 3)*(-atan(1/sqrt 3))) == ?A"},
            {"id": "s8", "move": "rewrite",
             "args": {"entry": "atan_one_sqrt3", "inst": {},
                      "at": "atan(1/sqrt 3)"},
             "occurrences": 1,
             "goal_after": P1_2_BEFORE_CLOSE},
            # field over Q(ln(1 + 1), pi, sqrt 3): (1/3)L + pi/(6s) + pi/(6s)
            # - (1/3)L - pi/(3s) = 0, with no fact needed. ln(1 + 1) and
            # ln 2 are one atom (§6.2, atoms up to normalised arguments),
            # but their domain keys are two trees, 1 + 1 > 0 (s2) and the
            # value's 2 > 0, both literal and discharged (E26, E7).
            {"id": "s9", "move": "close",
             "args": {"value": P1_2_ANSWER, "check": "field", "facts": []},
             "goal_after": None},
        ],
        "theorem": "Int[x = 0 .. 1] 1/(1 + x^3) == " + P1_2_ANSWER,
    },
}

# The accepted alternative (WHAT.md Done-when item 1): the same steps through
# s8, then a close that needs the fact. With sqrt 3 opaque,
# lhs - value = pi*(3 - s^2)/(9*s), which is zero only modulo s^2 = 3 (§8.7).
# So it closes by `field [sqrt_sq_val 3]`, reusing the handle from s1. It owes
# no 3*sqrt 3 # 0, since that divisor is not in its input. Its new divisor 9
# is a literal, the fact's 3 >= 0 is already discharged, and the value's
# ln 2 and sqrt 3 owe the literal 2 > 0 and 3 >= 0 (E26), as P1.2's value
# does. So its N is one less than P1.2's.
PROOFS["P1.2-alt"] = {
    "fallback": False,
    "goal": P1_2_GOAL,
    "steps": PROOFS["P1.2"]["steps"][:-1] + [
        {"id": "s9", "move": "close",
         "args": {"value": P1_2_ANSWER_ALT, "check": "field",
                  "facts": [("handle", "h_sqrt3")]},
         "goal_after": None},
    ],
    "theorem": "Int[x = 0 .. 1] 1/(1 + x^3) == " + P1_2_ANSWER_ALT,
}

ROUTE = {"P1.1": "P1.1", "P1.2": "P1.2"}  # which entry of PROOFS is the route
FALLBACKS = ("P1.1-fallback",)

# ---------------------------------------------------------------------------
# 4. deriv, rule by rule (§6.3), for every F the proofs and wrong answers use
#
# E12. deriv applies §6.3's output forms literally, with no tidying of 0*u or
# u*1, and walks the term top-down:
#   * d_const is tried first on any subterm with x not free in it, whatever
#     its former (rev 7), so -1, 1/3, 1/sqrt 3 and 2 are d_const. d_inv never
#     fires on a closed denominator (spike/ring README, finding 2). The one
#     exception is an x-free subterm that holds an Integral or Deriv node
#     anywhere: deriv refuses the step 'Int-or-D-not-normalisable' there
#     instead of firing d_const. Giving it derivative 0 would treat it as an
#     atom whose existence nothing can state, the reading E26 (b) forbids
#     (Int[t = 0 .. oo] 1 - Int[t = 0 .. oo] 1 is undefined, not constant).
#     The test sits inside the d_const branch, not in front of the walk: a
#     Deriv or Integral with x free still matches no rule and refuses
#     'deriv-no-rule' (below; BAD_MOVES ftc_F_contains_D). BAD_MOVES
#     ftc_F_holds_x_free_Int and ftc_F_holds_x_free_D pin the refusal.
#   * -u, with x free, is routed as (-1)*u by ring (no obligation), then d_mul.
#   * u/v, with x free and u not the literal 1, is routed as u*(1/v) by
#     field, owing v # 0, then d_mul. 1/v with x free in v is d_inv.
#   * d_pow_int's n - 1 is folded to an integer literal (u^(n-1) with n = 2
#     is x^1), and n != 0 is checked on the literal.
#   * a Deriv subterm D[y] e with x free in it (GRAMMAR.md D10: always so
#     when y is x) matches no §6.3 rule, and deriv refuses with
#     'deriv-no-rule'. d_const does not apply, because x is free. Reading D
#     as a binder would let d_const fire on D[x] x^2 and give 0, but D[x] x^2
#     is 2*x, whose derivative is 2 (checked with SymPy).
# Each entry is (rule, subterm it fires on, obligations it emits). The script
# asserts the multiset of (rule, subterm) pairs as trees. The order given is
# the top-down walk and is informative only.
# `output` is deriv(F) exactly as those forms build it: the lhs `check` sees.

DERIV = {
    "P1.1": {
        "var": "t",
        "F": P1_1_F,
        "trace": [
            ("d_add", "2*sin t - 2*t*cos t", ()),
            ("d_mul", "2*sin t", ()),
            ("d_const", "2", ()),
            ("d_sin", "sin t", ()),
            ("d_var", "t", ()),
            ("route_neg", "-(2*t*cos t)", ()),
            ("d_mul", "-1*(2*t*cos t)", ()),
            ("d_const", "-1", ()),
            ("d_mul", "2*t*cos t", ()),
            ("d_mul", "2*t", ()),
            ("d_const", "2", ()),
            ("d_var", "t", ()),
            ("d_cos", "cos t", ()),
            ("d_var", "t", ()),
        ],
        "output": ("0*sin t + 2*(cos t * 1)"
                   " + (0*(2*t*cos t) + (-1)*((0*t + 2*1)*cos t"
                   " + 2*t*(-sin t * 1)))"),
        "emits": (),
    },
    "P1.1-fallback": {
        "var": "x",
        "F": P1_1_FALLBACK_F,
        "trace": [
            ("d_add", P1_1_FALLBACK_F, ()),
            ("d_mul", "2*sin(sqrt x)", ()),
            ("d_const", "2", ()),
            ("d_sin", "sin(sqrt x)", ()),
            ("d_sqrt", "sqrt x", ("x > 0 @ (0, pi^2/4)",)),
            ("d_var", "x", ()),
            ("route_neg", "-(2*sqrt x * cos(sqrt x))", ()),
            ("d_mul", "-1*(2*sqrt x * cos(sqrt x))", ()),
            ("d_const", "-1", ()),
            ("d_mul", "2*sqrt x * cos(sqrt x)", ()),
            ("d_mul", "2*sqrt x", ()),
            ("d_const", "2", ()),
            ("d_sqrt", "sqrt x", ("x > 0 @ (0, pi^2/4)",)),
            ("d_var", "x", ()),
            ("d_cos", "cos(sqrt x)", ()),
            ("d_sqrt", "sqrt x", ("x > 0 @ (0, pi^2/4)",)),
            ("d_var", "x", ()),
        ],
        "output": ("0*sin(sqrt x) + 2*(cos(sqrt x)*(1/(2*sqrt x)))"
                   " + (0*(2*sqrt x * cos(sqrt x))"
                   " + (-1)*((0*sqrt x + 2*(1/(2*sqrt x)))*cos(sqrt x)"
                   " + 2*sqrt x * (-sin(sqrt x)*(1/(2*sqrt x)))))"),
        "emits": ("x > 0 @ (0, pi^2/4)",),
    },
    "P1.2": {
        "var": "x",
        "F": P1_2_F,
        "trace": [
            ("d_add", P1_2_F, ()),
            ("d_add", "(1/3)*ln(1 + x) - (1/6)*ln(x^2 - x + 1)", ()),
            ("d_mul", "(1/3)*ln(1 + x)", ()),
            ("d_const", "1/3", ()),
            ("d_ln", "ln(1 + x)", ("1 + x > 0 @ (0, 1)",)),
            ("d_add", "1 + x", ()),
            ("d_const", "1", ()),
            ("d_var", "x", ()),
            ("route_neg", "-((1/6)*ln(x^2 - x + 1))", ()),
            ("d_mul", "-1*((1/6)*ln(x^2 - x + 1))", ()),
            ("d_const", "-1", ()),
            ("d_mul", "(1/6)*ln(x^2 - x + 1)", ()),
            ("d_const", "1/6", ()),
            ("d_ln", "ln(x^2 - x + 1)", ("x^2 - x + 1 > 0 @ (0, 1)",)),
            ("d_add", "x^2 - x + 1", ()),
            ("d_add", "x^2 - x", ()),
            ("d_pow_int", "x^2", ()),
            ("d_var", "x", ()),
            ("route_neg", "-x", ()),
            ("d_mul", "-1*x", ()),
            ("d_const", "-1", ()),
            ("d_var", "x", ()),
            ("d_const", "1", ()),
            ("d_mul", "(1/sqrt 3)*atan((2*x - 1)/sqrt 3)", ()),
            ("d_const", "1/sqrt 3", ()),
            # d_atan has no side condition in §6.3. Its output divides by
            # 1 + u^2, and field charges that divisor.
            ("d_atan", "atan((2*x - 1)/sqrt 3)", ()),
            ("route_div", "(2*x - 1)/sqrt 3", ("sqrt 3 # 0",)),
            ("d_mul", "(2*x - 1)*(1/sqrt 3)", ()),
            ("d_add", "2*x - 1", ()),
            ("d_mul", "2*x", ()),
            ("d_const", "2", ()),
            ("d_var", "x", ()),
            ("d_const", "-1", ()),
            ("d_const", "1/sqrt 3", ()),
        ],
        "output": (
            "0*ln(1 + x) + (1/3)*((0 + 1)/(1 + x))"
            " + (0*((1/6)*ln(x^2 - x + 1))"
            " + (-1)*(0*ln(x^2 - x + 1)"
            " + (1/6)*((2*x^1*1 + (0*x + (-1)*1) + 0)/(x^2 - x + 1))))"
            " + (0*atan((2*x - 1)/sqrt 3)"
            " + (1/sqrt 3)*(((0*x + 2*1 + 0)*(1/sqrt 3) + (2*x - 1)*0)"
            "/(1 + ((2*x - 1)/sqrt 3)^2)))"),
        "emits": ("1 + x > 0 @ (0, 1)", "x^2 - x + 1 > 0 @ (0, 1)",
                  "sqrt 3 # 0"),
    },
    # WRONG_ANSWERS W1. The same shape as P1.1's F without the factor 2.
    "W1": {
        "var": "t",
        "F": "sin t - t*cos t",
        "trace": [
            ("d_add", "sin t - t*cos t", ()),
            ("d_sin", "sin t", ()),
            ("d_var", "t", ()),
            ("route_neg", "-(t*cos t)", ()),
            ("d_mul", "-1*(t*cos t)", ()),
            ("d_const", "-1", ()),
            ("d_mul", "t*cos t", ()),
            ("d_var", "t", ()),
            ("d_cos", "cos t", ()),
            ("d_var", "t", ()),
        ],
        "output": ("cos t * 1 + (0*(t*cos t)"
                   " + (-1)*(1*cos t + t*(-sin t * 1)))"),
        "emits": (),
    },
}

# ---------------------------------------------------------------------------
# 5. Expected obligations, step by step
#
# Each obligation is (prop, dom, sources, status, tag, new):
#   prop     the proposition in GRAMMAR.md syntax (a regularity judgement
#            carries its own domain);
#   dom      the domain string, "true" for ⊤;
#   sources  the SOURCES codes, as the kernel reports them, of the rules in
#            this step that emitted it (E8); compared as a set;
#   status   DISCHARGED or ADMITTED. An admitted one has reason
#            ADMISSION_REASON;
#   tag      (method, cites): for an admission, what is expected to close
#            it; for a discharged one, what closed it;
#   new      True if the key was not in the tracker before this step.
#
# "goal" is the state's creation: parsing and installing the goal emits its
# formers (E6, E26).
#
# E6. §5.1 says '/' carries a nonvanishing obligation but not when it is
# charged. It is charged when a term enters the proof: the goal at creation,
# ftc's F (on [a, b]) and the goal ftc produces, a rewrite's right-hand side,
# close's value, and a fact's inst values at the step that uses it (E10).
# The position's domain applies, and E5 gives domain true
# when the divisor is closed. §11.2 says the same of F: "writing F at all
# requires it". A goal integrand's formers are charged on the range interval
# E4 builds (DOMAIN_RULES), infinite ends included, so goal installation
# follows the same rule as rewrite and ftc. Negative powers and RPow bases
# are charged the same way, but P1 has none. E26 adds the partial builtins,
# charged at the same moments and at the same position domains.
#
# E26, definedness formers (user decision 2026-09-24, option (a) of
# PROOF_OF_LIFE.md's first question; interprets §5.1, §6.2, §6.9 and §14).
# (a) Each partial builtin is a former, charged exactly like E6's '/': when
#     a term enters the proof, at the occurrence's position domain, keyed
#     structurally (E8), then E5, E7 and E24 as for any obligation, with
#     source `former`. Each owes its natural domain, the set on which §6.9
#     makes it C^0:
#         ln u      u > 0
#         sqrt u    u >= 0
#         tan u     cos u # 0
#         asin u    u >= -1  and  u <= 1
#         acos u    u >= -1  and  u <= 1
#         acosh u   u >= 1
#         atanh u   u > -1   and  u < 1
#     sin, cos, atan, exp, abs, sinh, cosh, tanh and asinh are total and owe
#     nothing. The shapes, and why:
#       * One atomic judgement per bound, so a two-sided domain is two keys.
#         GRAMMAR.md D12 has no chains (a < x < b is refused), and a single
#         bound is a linear order item that Fourier–Motzkin reads directly
#         whenever u is linear on the domain (§5.3 methods 2 and 3).
#       * Each is written u REL c, the orientation of §6.3's d_ln and d_sqrt
#         (u > 0), so one table states every condition. KEYING mints each
#         rule's obligation in its own statement's orientation, and this
#         table is E26's statement.
#       * Not abs u <= 1 or abs u < 1, §6.3's d_asin form: abs u is an opaque
#         atom to §5.3 methods 2 to 5, and no §6.8 entry concludes it, so it
#         could only ever be tagged none. Not 1 - u^2 >= 0 either: method 5
#         never closes a non-strict goal (TAG_RULES), and the polynomial
#         hides the two linear bounds. The pairs are the same sets as §6.9's
#         |u| <= 1 and |u| < 1, written in the fragment discharge reads.
#       * Closed where the function is defined at the end (sqrt at 0, asin
#         and acos at 1 and -1, acosh at 1), open where it is not (ln at 0,
#         tan where cos u = 0, atanh at 1 and -1). That is E11 (a)'s
#         classification of natural domains, and §6.9's C^0 domains.
#     A literal argument's condition is decided by norm_num at once (E7).
#     ln 2 owes 2 > 0, ln 1 owes 1 > 0 and sqrt 3 owes 3 >= 0, all
#     DISCHARGED. A false one refuses the step 'obligation-refuted': ln(-1)
#     owes -1 > 0, acos 2 owes 2 <= 1, atanh 1 owes 1 < 1 (BAD_MOVES). A goal
#     is refused at installation this way, since installation is a charge.
#     tan's cos u # 0 is a domain, not a divisor, so E25 does not test it:
#     cos u is a single ring atom and never the zero polynomial. It is never
#     literal either, so it is always admitted, and the false cos(pi/2) # 0
#     is tagged none (DEFINEDNESS_CASES tan_pi_half). So is every cos u # 0
#     whose goal domain does not state it, true ones included: hyp fires
#     only when Γ contains it or an order item it follows from; no other
#     method sees more than an opaque atom; no pinned entry concludes it;
#     §6.8's cos_nonzero_on is not in this milestone (DEFINEDNESS_CASES
#     tan_zero_true).
#     field is unchanged. It emits d # 0 for its divisors (§6.2) and nothing
#     for the partial builtins in its input. Every atom of its input came
#     from a term charged where it entered, on a domain that contains the
#     check's (ftc's F on [a, b] against the check on (a, b); close's goal
#     and value at G), or is new in deriv's output and is defined wherever
#     that rule's side condition holds. Either the condition implies the
#     atom's domain (d_sqrt's u > 0 covers sqrt u, d_asin's abs u < 1
#     covers sqrt(1 - u^2), d_acosh's u > 1 covers sqrt(u^2 - 1),
#     d_pow_real's u > 0 covers ln u), or the atom's domain holds wherever
#     u is defined and needs no condition (d_asinh's sqrt(u^2 + 1), since
#     u^2 + 1 >= 1). Of these rules only d_sqrt is in this milestone
#     (deriv.APP_RULES; d_pow_real is not in it either). The general statement is the check a new §6.3 entry must
#     pass when it is added: every partial atom its output introduces must
#     be defined on the rule's side-condition set. Keeping field to divisors also keeps
#     d_ln's (0, 1) keys d_ln's alone, which PLANTED_BUGS d_ln_emits_nothing
#     needs: F's own ln formers are on [0, 1], a different key (E8).
#     Reason: under the partial reading that REWRITE_RULE step 5 and E11 rely
#     on, ring's identity a = b holds only where every atom of a and b is
#     defined. Before E26 only '/', negative powers and RPow bases carried
#     their domain, so ring cancelled undefined atoms freely: 0*ln(-1) == ?A
#     and tan(pi/2) - tan(pi/2) == ?A closed by ring as 'Proved.' with
#     nothing owed. §14 says the total and partial readings coincide
#     "because those rules carry their definedness conditions on the source
#     side", which needs every partial former to carry its condition. §11.1
#     and §11.2 already list three of these obligations (t^2 >= 0,
#     1 + x > 0 @ [0,1], x^2 - x + 1 > 0), which is evidence the design meant
#     them (see DESIGN_DEFECTS).
# (b) Int and D have no definedness condition the kernel can state until
#     regularity and `diverges` exist (§5.2, §6.4, §6.9): Int[x = 0 .. oo] 1
#     diverges, and D[x](abs x) does not exist at 0. So no normaliser treats
#     an Int or Deriv node as an atom. ring and field refuse, with
#     'Int-or-D-not-normalisable', any side they would normalise that holds
#     an Int or Deriv node anywhere, atom arguments included. That covers
#     rewrite's match (REWRITE_RULE steps 3 and 4), E25's charge-time
#     ring_nf(d), field's divisor test and fact reduction, and the checks of
#     ftc and close. deriv's d_const refuses the same way on an x-free
#     subterm holding an Int or Deriv node (E12), since d_const's 0 would
#     read that subterm as an atom. So an Int or D in ftc's F is refused in
#     step (iv) (E9): by that guard when x is not free in it, by
#     'deriv-no-rule' when it is. F's regularity admissions and the ftc_D
#     premise are never minted for such an F (BAD_MOVES
#     ftc_F_holds_x_free_Int, ftc_F_holds_x_free_D, ftc_F_contains_D).
#     norm_num refuses the same way: an obligation reaching
#     E7 with an Int or Deriv node in its proposition or its domain refuses
#     the step with that code, and is neither decided nor admitted. This
#     holds whether or not its other terms are literal and whether or not it
#     is closed. ln(D[x] x^2) owes D[x] x^2 > 0 with x free, and is refused
#     the same way (BAD_MOVES norm_num_refuses_D; norm_num_refuses_open_Int
#     for an Int; norm_num_refuses_Int_in_domain and
#     norm_num_refuses_D_in_domain for the domain half). E7 is
#     not run on a regularity judgement (tagged reg by its shape, E24) or on
#     ftc's derivative premise (discharged in the step, E9), so F and f
#     themselves never reach it; an Int or D in F reaches E7 only inside a
#     former's condition, as ln(Int[...] ...)'s would. BAD_MOVES
#     ftc_F_contains_D, whose F is D[x] x^2 and owes no former, keeps
#     'deriv-no-rule'.
#     No P1 step is affected, and that was checked step by step. ftc
#     consumes the goal's top-level Int, and decides its derivative premise
#     on deriv's output, which holds no Int or D. No P1 F holds one, so
#     d_const's guard never fires in P1 (DERIV's d_const subterms are -1,
#     1/3, 1/sqrt 3, 2 and the like). Every other ring, field
#     and norm_num input in P1 (rewrite arguments, E25's divisors, the
#     closes, every emitted proposition) holds none either.
#     Reason: ring would otherwise prove
#     (Int[x = 0 .. oo] 1) - (Int[x = 0 .. oo] 1) == 0, whose left side is
#     undefined, and norm_num would decide a judgement after cancelling the
#     same atoms. A refusal, not an admission, because an obligation about an
#     Int's or a D's value presupposes that it exists, which is the one
#     thing nothing can state yet. One rule, that no procedure normalises,
#     decides or differentiates as a constant an Int or D node, is also
#     easier to audit than a split one.
#
# E7. norm_num decides every obligation whose terms are rational literals
# only (no variable, constant or atom) at the moment it is emitted: true
# gives DISCHARGED, false refuses the step ('obligation-refuted'). WHAT.md
# names literal divisors. The fact hypothesis 3 >= 0 and sqrt_sq's 0 >= 0
# are the same kind of goal, and §6.2's norm_num "closes goals over rational
# literals exactly". So is a partial builtin's condition on a literal
# argument (E26): 2 > 0 from ln 2, 3 >= 0 from sqrt 3 and 1^2 - 1 + 1 > 0
# from ln(1^2 - 1 + 1) are DISCHARGED, and -1 > 0 from ln(-1) refuses the
# step. A literal divisor that is 0, as in 1/0, never reaches E7: E25
# refuses it first. An Int or D node is never a literal, but E7 does not
# leave an obligation holding one admitted. Any obligation reaching E7
# (every emitted one except a regularity judgement and ftc's derivative
# premise) that holds an Int or Deriv node in its proposition or its domain
# is refused 'Int-or-D-not-normalisable'. This holds whether or not the
# obligation is literal or closed (E26 (b)).
#
# E25, zero divisors (interprets §6.2 field's "a divisor that normalises to
# zero is refused", and its "coincide exactly with what §5.1's / former
# already charges").
#   * Every divisor charged as `d # 0` is checked before it is emitted. That
#     is a '/' or negative-power former at E6, deriv's route_div, and
#     field's field_div. tan's cos u # 0 (E26) is a domain, not a divisor,
#     and is not tested. A divisor holding an Int or D node is refused
#     'Int-or-D-not-normalisable' by the test's own ring_nf (E26 (b)).
#   * At charge time (E6, route_div) the step is refused
#     'divisor-normalises-to-zero' if ring_nf(d) is the zero polynomial.
#     E3 already computes ring_nf(d) as the key of inv(d), so the test costs
#     nothing extra. Goal installation is a charge (E6), so a goal is refused
#     at installation the same way.
#   * Inside `field`, every divisor of its input is also tested, before
#     lhs - rhs is normalised: the step is refused if the numerator of d's
#     field normal form is zero. This is §6.2's own wording, and it catches
#     divisors like x/x - 1, whose ring_nf x*inv(x) - 1 is nonzero. The
#     test comes first, so such a step is never reported as
#     'ftc-check-failed' or 'close-check-failed'.
#   * A refused step emits nothing (E13).
#   Reason: §6.2 mandates the refusal for field, and says field's divisors
#   are exactly the ones the former already charges, so the former charge is
#   where a zero divisor first enters the proof. Refusing it there, rather
#   than admitting a false `d # 0` whose tag cannot close it, keeps E6 and
#   field consistent. The charge-time test is ring_nf only, so a divisor such
#   as x/x - 1 is still admitted at installation (and E24 tags that false
#   admission none) and is refused only when field sees it. BAD_MOVES
#   install_zero_divisor and field_zero_divisor pin both tests.

OB_FIELDS = ("prop", "dom", "sources", "status", "tag", "new")

EXPECTED_OBLIGATIONS = {
    "P1.1": {
        "goal": [
            # pi/2 in the Int's upper limit, outside t's scope, so at the
            # goal's domain
            ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
            # sqrt(t^2) in the integrand owes its domain on the range (E26).
            # §11.1 lists it as "t^2 ≥ 0 by sign", the sub-obligation of
            # sin(sqrt(t^2)) ∈ C⁰. Range cannot close it, since t^2 is an
            # opaque monomial to Fourier–Motzkin; sign can, by E20 (an even
            # power, constant 0, on a non-strict goal).
            ("t^2 >= 0", "[0, pi/2]", (S_FORMER,), ADMITTED, T_SIGN, True),
            # That key uses the range, so the orientation is owed here, at
            # installation, and not first at s1 (E4)
            ("0 <= pi/2", "true", (S_ORIENT,), ADMITTED, T_LINEAR_PI, True),
        ],
        "s1": [
            # §11.1's "0 ≤ t by range, pi_pos", split in two. The hypothesis
            # itself is on the range [0, pi/2] (by range). What needs pi_pos is
            # that [0, pi/2] is the range at all (E4), already owed since the
            # goal was installed. R = t has no former.
            ("t >= 0", "[0, pi/2]", (S_SQRT_SQ,), ADMITTED, T_RANGE, True),
            ("0 <= pi/2", "true", (S_ORIENT,), ADMITTED, T_LINEAR_PI, False),
        ],
        "s2": [
            ("0 <= pi/2", "true", (S_ORIENT,), ADMITTED, T_LINEAR_PI, False),
            ("2*sin t - 2*t*cos t in C^0([0, pi/2])", "[0, pi/2]",
             (S_FTC_C0F,), ADMITTED, T_REG, True),
            ("2*sin t - 2*t*cos t in C^1((0, pi/2))", "(0, pi/2)",
             (S_FTC_C1F,), ADMITTED, T_REG, True),
            # deriv emits nothing on this F (DERIV["P1.1"]). ring emits
            # nothing at all (§6.2).
            ("D[t](2*sin t - 2*t*cos t) == sin t * (2*t)", "(0, pi/2)",
             (S_FTC_D,), DISCHARGED, T_DERIV_RING, True),
            ("sin t * (2*t) in C^0([0, pi/2])", "[0, pi/2]",
             (S_FTC_C0f,), ADMITTED, T_REG, True),
            # the new goal contains pi/2 (F at b). F and the new goal hold
            # only sin and cos, which are total (E26), so nothing else.
            ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False),
        ],
        "s3": [],  # right-hand side 1: no formers, no hypotheses
        "s4": [],
        "s5": [],
        "s6": [],  # ring emits nothing, and the value 2 has no divisor
    },

    "P1.1-fallback": {
        "goal": [
            # pi^2/4 in the Int's upper limit, at the goal's domain
            ("4 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
            # sqrt x in the integrand owes its domain on the range (E26):
            # x < 0 against the range's 0 <= x is infeasible, so range, and
            # pi's sign fact is not used
            ("x >= 0", "[0, pi^2/4]", (S_FORMER,), ADMITTED, T_RANGE, True),
            # pi^2 is not linear in pi, so the orientation closes by a sign
            # certificate on the goal as written. E20: §5.3 method 4 states
            # only strict forms, a positive rational plus even powers, or a
            # negative discriminant. For a non-strict `>= 0` goal it is read
            # as also accepting a non-negative rational constant, zero
            # included: a non-negative combination of even powers is `>= 0`.
            # Here (1/4)*pi^2 has constant 0 and discriminant 0 (SymPy), so
            # only this reading closes it. It is owed at installation because
            # the key above uses the range (E4).
            ("0 <= pi^2/4", "true", (S_ORIENT,), ADMITTED, T_SIGN, True),
        ],
        "s1": [
            ("0 <= pi^2/4", "true", (S_ORIENT,), ADMITTED, T_SIGN, False),
            # F's three sqrt x on [a, b]: the installation's key again
            ("x >= 0", "[0, pi^2/4]", (S_FORMER,), ADMITTED, T_RANGE, False),
            ("2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^0([0, pi^2/4])",
             "[0, pi^2/4]", (S_FTC_C0F,), ADMITTED, T_REG, True),
            ("2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^1((0, pi^2/4))",
             "(0, pi^2/4)", (S_FTC_C1F,), ADMITTED, T_REG, True),
            ("D[x](2*sin(sqrt x) - 2*sqrt x * cos(sqrt x)) == sin(sqrt x)",
             "(0, pi^2/4)", (S_FTC_D,), DISCHARGED, T_DERIV_FIELD, True),
            ("sin(sqrt x) in C^0([0, pi^2/4])", "[0, pi^2/4]",
             (S_FTC_C0f,), ADMITTED, T_REG, True),
            # d_sqrt fires three times on the same u = x: one key
            ("x > 0", "(0, pi^2/4)", (S_D_SQRT,), ADMITTED, T_RANGE, True),
            # d_sqrt's output divides by 2 * sqrt u. The divisor is the term
            # 2*sqrt x, as WHAT.md states it. field does not split it. The
            # tag relies on E18: method 5 splitting off the content 2.
            ("2*sqrt x # 0", "(0, pi^2/4)", (S_FIELD,), ADMITTED,
             T_PRODUCT_SQRT, True),
            # The new goal, F(pi^2/4) - F(0), at the goal's domain: its three
            # pi^2/4 owe 4 # 0 (E6), its three sqrt(pi^2/4) owe
            # pi^2/4 >= 0, and its three sqrt 0 owe 0 >= 0 (E26, both
            # closed, so domain true by E5). pi^2/4 >= 0 is tagged sign as
            # 0 <= pi^2/4 is (E20; range sees pi^2 as opaque). 0 >= 0 is
            # literal (E7).
            ("4 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False),
            ("pi^2/4 >= 0", "true", (S_FORMER,), ADMITTED, T_SIGN, True),
            ("0 >= 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
        ],
        "s2": [
            ("pi/2 >= 0", "true", (S_SQRT_SQ,), ADMITTED, T_LINEAR_PI, True),
            ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
        ],
        "s3": [
            ("0 >= 0", "true", (S_SQRT_SQ,), DISCHARGED, T_NORM_NUM, False),
        ],
        "s4": [],
        "s5": [],
        "s6": [],
        "s7": [],
    },

    "P1.2": {
        "goal": [
            # The integrand's divisor on the range. The range is literal, so
            # norm_num orients it and no orientation obligation is recorded
            # (E4). This is §11.2's "1 + x^3 # 0 @ [0,1] by product (lines
            # 1–2; ring)". The factorisation is (1 + x)*(x^2 - x + 1), with
            # 1 + x > 0 on [0, 1] by range and x^2 - x + 1 > 0 by the
            # certificate (x - 1/2)^2 + 3/4.
            ("1 + x^3 # 0", "[0, 1]", (S_FORMER,), ADMITTED, T_PRODUCT, True),
        ],
        "s1": [],  # `fact` emits nothing; the hypothesis stays in the theorem
        "s2": [
            ("3 # 0", "true", (S_FORMER, S_FIELD), DISCHARGED, T_NORM_NUM,
             True),
            ("6 # 0", "true", (S_FORMER, S_FIELD), DISCHARGED, T_NORM_NUM,
             True),
            # F's 1/sqrt 3 and (2*x - 1)/sqrt 3; deriv's u/v routing; field's
            # divisors, including the one inside atan's argument; and the new
            # goal's F(1), F(0). All closed, so one key (E5).
            ("sqrt 3 # 0", "true", (S_FORMER, S_ROUTE_DIV, S_FIELD),
             ADMITTED, T_SQRT_POS, True),
            # F's sqrt 3, twice, and the new goal's, owe 3 >= 0 (E26); the
            # handle h_sqrt3 brings the same key as its hypothesis (WHAT.md:
            # 3 >= 0 from sqrt_sq_val 3). Literal, so norm_num (E7).
            ("3 >= 0", "true", (S_FORMER, S_FACT), DISCHARGED, T_NORM_NUM,
             True),
            # F's two ln on [a, b] = [0, 1] (E26). §11.2 lists these two as
            # "1 + x > 0 @ [0,1] by domain (linear)" and "x^2 - x + 1 > 0 by
            # sign". They are also §6.9's sub-obligations of F in C^0([0, 1])
            # (REGULARITY_LISTING). Different keys from d_ln's on (0, 1)
            # (E8). The first is range (x >= 0 from dom closes 1 + x <= 0);
            # the second is sign, the certificate (x - 1/2)^2 + 3/4, since
            # range sees x^2 as opaque.
            ("1 + x > 0", "[0, 1]", (S_FORMER,), ADMITTED, T_RANGE, True),
            ("x^2 - x + 1 > 0", "[0, 1]", (S_FORMER,), ADMITTED, T_SIGN,
             True),
            (P1_2_F + " in C^0([0, 1])", "[0, 1]", (S_FTC_C0F,), ADMITTED,
             T_REG, True),
            (P1_2_F + " in C^1((0, 1))", "(0, 1)", (S_FTC_C1F,), ADMITTED,
             T_REG, True),
            ("D[x](" + P1_2_F + ") == 1/(1 + x^3)", "(0, 1)", (S_FTC_D,),
             DISCHARGED, T_DERIV_FIELD_FACT, True),
            ("1/(1 + x^3) in C^0([0, 1])", "[0, 1]", (S_FTC_C0f,), ADMITTED,
             T_REG, True),
            # deriv's d_ln, on the open interval. The closed-interval keys
            # above are ln's formers, not d_ln's.
            ("1 + x > 0", "(0, 1)", (S_D_LN,), ADMITTED, T_RANGE, True),
            # certificate (x - 1/2)^2 + 3/4 (§11.2, §5.3 method 4)
            ("x^2 - x + 1 > 0", "(0, 1)", (S_D_LN,), ADMITTED, T_SIGN, True),
            # field's divisors from d_ln's outputs D[x]u / u
            ("1 + x # 0", "(0, 1)", (S_FIELD,), ADMITTED, T_RANGE, True),
            ("x^2 - x + 1 # 0", "(0, 1)", (S_FIELD,), ADMITTED, T_SIGN, True),
            # d_atan's denominator. The sign certificate reads it as written:
            # 1 plus an even power (§5.3 method 4, rev 7).
            ("1 + ((2*x - 1)/sqrt 3)^2 # 0", "(0, 1)", (S_FIELD,), ADMITTED,
             T_SIGN, True),
            # the integrand, as field's input, on the open interval. A
            # different key from the goal's former on [0, 1] (E8).
            ("1 + x^3 # 0", "(0, 1)", (S_FIELD,), ADMITTED, T_PRODUCT, True),
            # The new goal F(1) - F(0) holds four ln with literal arguments.
            # Each owes its argument > 0 as a tree (E8), so 1 + 1 > 0 and not
            # 2 > 0, and each is literal and true (E26, E7).
            ("1 + 1 > 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
            ("1^2 - 1 + 1 > 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
             True),
            ("1 + 0 > 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
            ("0^2 - 0 + 1 > 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
             True),
        ],
        "s3": [],  # ln_one: right-hand side 0, no hypotheses
        "s4": [],
        "s5": [],
        "s6": [
            ("6 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False),
        ],
        "s7": [
            # the right-hand side -atan(1/sqrt 3) carries the divisor sqrt 3,
            # and its sqrt 3 owes 3 >= 0 (E26)
            ("sqrt 3 # 0", "true", (S_FORMER,), ADMITTED, T_SQRT_POS, False),
            ("3 >= 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False),
        ],
        "s8": [
            ("6 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False),
        ],
        "s9": [
            ("3 # 0", "true", (S_FORMER, S_FIELD), DISCHARGED, T_NORM_NUM,
             False),
            ("6 # 0", "true", (S_FIELD,), DISCHARGED, T_NORM_NUM, False),
            ("sqrt 3 # 0", "true", (S_FIELD,), ADMITTED, T_SQRT_POS, False),
            # §11.2: "close ... by field, obl 3*sqrt 3 # 0 by product
            # (sqrt_pos)". It is both the value's former and field's divisor.
            # The tag relies on E18: method 5 splitting off the content 3.
            ("3*sqrt 3 # 0", "true", (S_FORMER, S_FIELD), ADMITTED,
             T_PRODUCT_SQRT, True),
            # the value's ln 2 and sqrt 3 (E26): 2 > 0 is a new key, not
            # s2's 1 + 1 > 0; 3 >= 0 is s2's
            ("2 > 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
            ("3 >= 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False),
        ],
    },
}
_alt = dict(EXPECTED_OBLIGATIONS["P1.2"])
_alt["s9"] = [
    ("3 # 0", "true", (S_FORMER, S_FIELD), DISCHARGED, T_NORM_NUM, False),
    ("6 # 0", "true", (S_FIELD,), DISCHARGED, T_NORM_NUM, False),
    ("9 # 0", "true", (S_FORMER, S_FIELD), DISCHARGED, T_NORM_NUM, True),
    ("sqrt 3 # 0", "true", (S_FIELD,), ADMITTED, T_SQRT_POS, False),
    # the value's sqrt 3 (E26) and the fact's hypothesis, one key
    ("3 >= 0", "true", (S_FORMER, S_FACT), DISCHARGED, T_NORM_NUM, False),
    ("2 > 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),  # ln 2
]
EXPECTED_OBLIGATIONS["P1.2-alt"] = _alt
del _alt

# The tracker at the end of each proof: every key once, with its final
# status. Written out by hand. It is not computed from the per-step lists,
# so the two act as a cross-check on each other.
FINAL_TRACKER = {
    "P1.1": [
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("t^2 >= 0", "[0, pi/2]", ADMITTED, T_SIGN),
        ("t >= 0", "[0, pi/2]", ADMITTED, T_RANGE),
        ("0 <= pi/2", "true", ADMITTED, T_LINEAR_PI),
        ("2*sin t - 2*t*cos t in C^0([0, pi/2])", "[0, pi/2]", ADMITTED, T_REG),
        ("2*sin t - 2*t*cos t in C^1((0, pi/2))", "(0, pi/2)", ADMITTED, T_REG),
        ("D[t](2*sin t - 2*t*cos t) == sin t * (2*t)", "(0, pi/2)",
         DISCHARGED, T_DERIV_RING),
        ("sin t * (2*t) in C^0([0, pi/2])", "[0, pi/2]", ADMITTED, T_REG),
    ],
    "P1.1-fallback": [
        ("4 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("x >= 0", "[0, pi^2/4]", ADMITTED, T_RANGE),
        ("0 <= pi^2/4", "true", ADMITTED, T_SIGN),
        ("2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^0([0, pi^2/4])",
         "[0, pi^2/4]", ADMITTED, T_REG),
        ("2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^1((0, pi^2/4))",
         "(0, pi^2/4)", ADMITTED, T_REG),
        ("D[x](2*sin(sqrt x) - 2*sqrt x * cos(sqrt x)) == sin(sqrt x)",
         "(0, pi^2/4)", DISCHARGED, T_DERIV_FIELD),
        ("sin(sqrt x) in C^0([0, pi^2/4])", "[0, pi^2/4]", ADMITTED, T_REG),
        ("x > 0", "(0, pi^2/4)", ADMITTED, T_RANGE),
        ("2*sqrt x # 0", "(0, pi^2/4)", ADMITTED, T_PRODUCT_SQRT),
        ("pi^2/4 >= 0", "true", ADMITTED, T_SIGN),
        ("0 >= 0", "true", DISCHARGED, T_NORM_NUM),
        ("pi/2 >= 0", "true", ADMITTED, T_LINEAR_PI),
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
    ],
    "P1.2": [
        ("1 + x^3 # 0", "[0, 1]", ADMITTED, T_PRODUCT),
        ("3 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("6 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("sqrt 3 # 0", "true", ADMITTED, T_SQRT_POS),
        ("3 >= 0", "true", DISCHARGED, T_NORM_NUM),
        ("1 + x > 0", "[0, 1]", ADMITTED, T_RANGE),
        ("x^2 - x + 1 > 0", "[0, 1]", ADMITTED, T_SIGN),
        (P1_2_F + " in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
        (P1_2_F + " in C^1((0, 1))", "(0, 1)", ADMITTED, T_REG),
        ("D[x](" + P1_2_F + ") == 1/(1 + x^3)", "(0, 1)", DISCHARGED,
         T_DERIV_FIELD_FACT),
        ("1/(1 + x^3) in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
        ("1 + x > 0", "(0, 1)", ADMITTED, T_RANGE),
        ("x^2 - x + 1 > 0", "(0, 1)", ADMITTED, T_SIGN),
        ("1 + x # 0", "(0, 1)", ADMITTED, T_RANGE),
        ("x^2 - x + 1 # 0", "(0, 1)", ADMITTED, T_SIGN),
        ("1 + ((2*x - 1)/sqrt 3)^2 # 0", "(0, 1)", ADMITTED, T_SIGN),
        ("1 + x^3 # 0", "(0, 1)", ADMITTED, T_PRODUCT),
        ("1 + 1 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("1^2 - 1 + 1 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("1 + 0 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("0^2 - 0 + 1 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("3*sqrt 3 # 0", "true", ADMITTED, T_PRODUCT_SQRT),
        ("2 > 0", "true", DISCHARGED, T_NORM_NUM),
    ],
}
# The same tracker without s9's 3*sqrt 3 # 0 and with its 9 # 0. Its 2 > 0,
# from ln 2, is in both values.
FINAL_TRACKER["P1.2-alt"] = (
    [ob for ob in FINAL_TRACKER["P1.2"] if ob[0] != "3*sqrt 3 # 0"]
    + [("9 # 0", "true", DISCHARGED, T_NORM_NUM)])

# N, the admission count in "Proved modulo N admissions". E26 (user decision
# 2026-09-24) added t^2 >= 0 to P1.1, x >= 0 @ [0, pi^2/4] and pi^2/4 >= 0 to
# the fallback, and F's two ln domains on [0, 1] to P1.2 and P1.2-alt. Every
# other domain it charges in P1 is literal, and norm_num discharges it.
ADMISSIONS = {
    "P1.1": 6,           # t^2 >= 0, t >= 0, 0 <= pi/2, three regularity
    "P1.1-fallback": 9,  # x >= 0, orientation, x > 0, 2*sqrt x # 0,
                         # pi^2/4 >= 0, pi/2 >= 0, three regularity
    "P1.2": 14,          # 1 + x^3 # 0 twice, sqrt 3 # 0, 1 + x > 0 and
                         # x^2 - x + 1 > 0 on [0, 1] and on (0, 1), 1 + x # 0,
                         # x^2 - x + 1 # 0, the atan denominator,
                         # 3*sqrt 3 # 0, three regularity
    "P1.2-alt": 13,      # no 3*sqrt 3 # 0
}

# What §6.9's closure rules would ask for under each admitted regularity
# premise, once reg exists. This is listed only, never asserted: regularity
# is "listing it" in this milestone (WHAT.md Out). It is recorded because
# §11.2's closed-interval lines come from here (see DESIGN_DEFECTS), and
# because it shows why §6.4's split matters for the fallback. Since E26 the
# kernel also emits those closed-interval conditions itself, as the partial
# builtins' formers when F enters on [a, b]: 1 + x > 0 and x^2 - x + 1 > 0
# @ [0, 1] for P1.2's ln, and x >= 0 @ [0, pi^2/4] for the fallback's sqrt.
# They coincide because E26 charges each builtin's C^0 domain (§6.9).
# sqrt is C^0 on u >= 0 but C^1 only on u > 0, so the C^1 premise on the closed
# [0, pi^2/4] would be unreachable by §6.9's rules, and the open (0, pi^2/4)
# is what makes it reachable.
REGULARITY_LISTING = {
    "P1.1": {
        "2*sin t - 2*t*cos t in C^0([0, pi/2])": (),   # sin, cos everywhere
        "2*sin t - 2*t*cos t in C^1((0, pi/2))": (),
        "sin t * (2*t) in C^0([0, pi/2])": (),
    },
    "P1.1-fallback": {
        "2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^0([0, pi^2/4])":
            ("x >= 0 @ [0, pi^2/4]",),
        "2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^1((0, pi^2/4))":
            ("x > 0 @ (0, pi^2/4)",),
        "sin(sqrt x) in C^0([0, pi^2/4])": ("x >= 0 @ [0, pi^2/4]",),
    },
    # The quotient conditions (3 # 0, 6 # 0, sqrt 3 # 0) and sqrt's own
    # condition on its argument 3 (>= 0 for C^0, > 0 for C^1, §6.9) are
    # listed even though they are literals, so that P1.2 applies §6.9 the
    # same way as the P1.1-fallback. None of them changes ADMISSIONS, because
    # the listing is never asserted.
    "P1.2": {
        P1_2_F + " in C^0([0, 1])":
            ("3 # 0", "6 # 0", "sqrt 3 # 0", "3 >= 0",
             "1 + x > 0 @ [0, 1]", "x^2 - x + 1 > 0 @ [0, 1]"),
        P1_2_F + " in C^1((0, 1))":
            ("3 # 0", "6 # 0", "sqrt 3 # 0", "3 > 0",
             "1 + x > 0 @ (0, 1)", "x^2 - x + 1 > 0 @ (0, 1)"),
        "1/(1 + x^3) in C^0([0, 1])": ("1 + x^3 # 0 @ [0, 1]",),
    },
}

# ---------------------------------------------------------------------------
# 6. Answers

ANSWERS = {
    "P1.1": "2",
    "P1.1-fallback": "2",
    "P1.2": P1_2_ANSWER,
    "P1.2-alt": P1_2_ANSWER_ALT,
}
# For the script's own numeric sanity check (math module only). These are not
# terms, and decimals are not in the grammar (GRAMMAR.md D1).
NUMERIC = {
    "P1.1": 2.0,
    "P1.2": 0.83564884826472105,  # the integral of 1/(1 + x^3) over [0, 1]
}
VERDICTS = {name: VERDICT.format(n=n) for name, n in ADMISSIONS.items()}

# ---------------------------------------------------------------------------
# 7. Wrong answers (Done-when item 4)
#
# Each is refused. The refusal carries the residual lhs - rhs of the equation
# that failed to close: deriv(F) - f for ftc (§8.7: "D[t] F − integrand"),
# and goal lhs - value for close. The state is unchanged and nothing is
# emitted (E13).
#
# E14. The residual is compared by equality in the named procedure, never as
# a string: the script asserts that `compare` proves
# reported_residual == expected. For W3 and W4 the comparison runs WITHOUT
# the sqrt_sq_val fact. With the fact both residuals are 0, and the
# comparison would pass vacuously. The script also asserts the reported
# residual is not zero under `compare`. The divisors a comparison would owe
# are irrelevant to the assertion and are not tracked.
#
# Every residual below was computed with SymPy, treating sqrt 3 as a free
# symbol s where the case says the fact is absent.

WRONG_ANSWERS = [
    {
        "id": "W1",
        "what": "P1.1 with F := sin t - t*cos t (the factor 2 missing, §11.1, "
                "§8.7)",
        "state": ("P1.1", "s1"),  # the state after step s1 of P1.1
        "move": ("ftc", {"F": "sin t - t*cos t", "check": "ring",
                         "facts": []}),
        "refusal": "ftc-check-failed",
        "residual": "-t*sin t",
        "compare": ("ring", ()),
    },
    {
        "id": "W2",
        "what": "P1.2 with ln coefficient 1/3 in place of 1/6",
        "state": ("P1.2", "s1"),  # h_sqrt3 is bound
        "move": ("ftc", {"F": "(1/3)*ln(1 + x) - (1/3)*ln(x^2 - x + 1)"
                              " + (1/sqrt 3)*atan((2*x - 1)/sqrt 3)",
                         "check": "field",
                         "facts": [("handle", "h_sqrt3")]}),
        "refusal": "ftc-check-failed",
        # Run with the fact, so the coefficient is the only error. The
        # reported numerator is reduced modulo s^2 = 3, but its denominator
        # can still hold sqrt 3, so the comparison uses the fact too.
        "residual": "-(2*x - 1)/(6*(x^2 - x + 1))",
        "compare": ("field", ("h_sqrt3",)),
    },
    {
        "id": "W3",
        "what": "P1.2 without the sqrt_sq_val fact (§11.2, §6.8)",
        "state": ("P1.2", "s1"),
        "move": ("ftc", {"F": P1_2_F, "check": "field", "facts": []}),
        "refusal": "ftc-check-failed",
        # §11.2's form, (3/2 − s²/2)/(s²x² − s²x + s² + 4x⁴ − 8x³ + 9x² −
        # 5x + 1) with s = sqrt 3 opaque. Confirmed equal to deriv(F) - f
        # with s free.
        "residual": ("(3/2 - (sqrt 3)^2/2)/((sqrt 3)^2*x^2 - (sqrt 3)^2*x"
                     " + (sqrt 3)^2 + 4*x^4 - 8*x^3 + 9*x^2 - 5*x + 1)"),
        # the same rational function in factored form
        "residual_factored": ("-((sqrt 3)^2 - 3)/(2*(x^2 - x + 1)"
                              "*((sqrt 3)^2 + 4*x^2 - 4*x + 1))"),
        "compare": ("field", ()),
    },
    # Added (not in WHAT.md's three): §8.7's surd case, which is the reason
    # the alternative close needs the fact.
    {
        "id": "W4",
        "added": True,
        "what": "P1.2-alt's close without the fact (§8.7)",
        "state": ("P1.2", "s8"),
        "move": ("close", {"value": P1_2_ANSWER_ALT, "check": "field",
                           "facts": []}),
        "refusal": "close-check-failed",
        "residual": "pi*(3 - (sqrt 3)^2)/(9*sqrt 3)",  # (3π − s²π)/(9s)
        "compare": ("field", ()),
    },
]

# ---------------------------------------------------------------------------
# 8. Bad moves (Done-when item 5)
#
# (goal, move, args, expected refusal). The goal is installed fresh, and any
# handles named come from running the listed steps first. An entry with a
# "state" (proof, step id) instead starts from the state after that step of
# that proof, as WRONG_ANSWERS do; its "goal" is that proof's original goal.
# An entry whose move is ("install", {}) expects the refusal from installing
# the goal itself (parse_goal, then creating the proof state, which charges
# the goal's formers, E6); no step is called. Refusal codes are the stable
# thing to assert. The message wording is the kernel's.

REFUSAL_CODES = {
    "rewrite-under-D-needs-open-domain": "§6.1 rev 9 (E1 step 9)",
    "rewrite-lhs-mismatch": "§18 Q21 (E1 steps 3-4)",
    "rewrite-target-not-found": "E1 step 2",
    "rewrite-scope": "E1 step 6",
    "close-scope-bound-variable": "§9, §5.1; GRAMMAR.md D11",
    "close-schema-not-closed": "§9, the closed whitelist (E23: a node "
                               "outside it)",
    "divisor-normalises-to-zero": "§6.2 field: a divisor that normalises to "
                                  "zero is refused; extended to every "
                                  "charged divisor by E25",
    # Decision: the earlier 'field-fact-not-a-handle' is folded into this
    # code. A raw Judgement is one more kind of object that is not a minted
    # handle, and one code for every fact position (field, ftc and close
    # alike) keeps the kernel from having to classify what a non-handle is.
    "fact-not-minted-handle": "§15.3, E17: not the object the kernel minted "
                              "(any fact position: ftc, field, close)",
    "fact-foreign-state-handle": "§15.3, E17: minted in another proof state",
    "deriv-no-rule": "§6.3: no rule applies, e.g. a Deriv subterm with x "
                     "free (E12)",
    "subst-under-D": "GRAMMAR.md §5, substitution into D[x] e; unreachable "
                     "in P1 (E9)",
    "ftc-check-failed": "§6.4, §8.7 (carries a residual)",
    "ftc-infinite-endpoint": "§5.1, §6.4 (E9)",
    "range-same-infinity": "E4: Int[v = oo .. oo] or Int[v = -oo .. -oo] "
                           "has an empty range; unreachable in P1",
    "rpow-literal-exponent": "GRAMMAR.md §7 D17: an RPow constructed with a "
                             "Num or Neg(Num) exponent, by substitution or "
                             "instantiation; unreachable in P1 (no RPow)",
    "close-check-failed": "§9 (carries a residual)",
    # Added by user decision 2026-09-24 (evaluated answers), E27.
    "close-not-evaluated": "§9, §6.8, E27: the value was proved equal to "
                           "the goal's left side but is not fully "
                           "evaluated, (a) an entry in force still applies "
                           "to a subterm or (b) it holds unreduced literal "
                           "arithmetic. Untrusted (schema.py), run last in "
                           "close, so every other refusal wins. Carries the "
                           "offending subterm as its residual",
    "obligation-refuted": "E7: norm_num decides a literal obligation false, "
                          "a partial builtin's domain on a literal included "
                          "(E26: ln(-1) owes -1 > 0). A literal zero divisor "
                          "(1/0) is not this code: E25 refuses it first with "
                          "divisor-normalises-to-zero",
    # Added by user decision 2026-09-24 (E26 (b)).
    "Int-or-D-not-normalisable": "E26 (b), §5.2, §6.2, §14: ring, field or "
                                 "norm_num met an Int or D node in a side it "
                                 "must normalise or decide, or deriv's "
                                 "d_const met one in an x-free subterm it "
                                 "would differentiate to 0 (E12). Neither has a "
                                 "definedness condition the kernel can "
                                 "state until regularity and diverges "
                                 "exist, so neither may be an atom",
}

BAD_MOVES = [
    {
        "id": "rewrite_under_D",
        "goal": "D[x](sqrt(x^2)) == ?A",
        "setup": [],
        "move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "x"},
                             "at": "sqrt(x^2)"}),
        "refusal": "rewrite-under-D-needs-open-domain",
        "why": "sqrt_sq holds @ x >= 0, which is not open, and the position "
               "is under D[x]. Accepted, it would give D[x] sqrt(x^2) == 1 "
               "@ x >= 0, which is false at 0 (§6.1 rev 9).",
    },
    {
        # WHAT.md's own phrasing of the same must-refuse, with no ?A
        "id": "rewrite_under_D_stated",
        "goal": "D[x](sqrt(x^2)) == 1 @ x >= 0",
        "setup": [],
        "move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "x"},
                             "at": "sqrt(x^2)"}),
        "refusal": "rewrite-under-D-needs-open-domain",
        "why": "as above. The goal's own domain x >= 0 does not help, "
               "because the equation's domain is what must be open.",
    },
    {
        "id": "close_bound_variable",
        "goal": P1_1_GOAL,
        "setup": [],
        "move": ("close", {"value": "t", "check": "ring", "facts": []}),
        "refusal": "close-scope-bound-variable",
        "why": "t is bound by the goal's Int, and ?A may not mention it (§9).",
    },
    {
        "id": "close_bound_variable_after_ftc",
        "goal": P1_1_GOAL,
        "state": ("P1.1", "s2"),
        "move": ("close", {"value": "t", "check": "ring", "facts": []}),
        "refusal": "close-scope-bound-variable",
        "why": "ftc removed the Int, but the reported theorem is the original "
               "goal, where t is bound (§9, D11, E19). The refusal must come "
               "from the scope check, not from ring failing.",
    },
    {
        "id": "close_bound_variable_ring_true",
        "goal": P1_1_GOAL,
        "state": ("P1.1", "s5"),
        "move": ("close", {"value": "t - t + 2", "check": "ring",
                           "facts": []}),
        "refusal": "close-scope-bound-variable",
        "why": "ring proves 2*1 - 2*(pi/2)*0 - (2*0 - 2*0*cos 0) == t - t + 2 "
               "(checked with SymPy, pi and cos 0 opaque). A scope check "
               "against the current goal would accept this and report "
               "'Int[t = 0 .. pi/2] ... == t - t + 2', which violates D11 "
               "(E19).",
    },
    {
        "id": "close_not_closed_form",
        "goal": P1_2_GOAL,
        "setup": [],
        "move": ("close", {"value": "Int[x = 0 .. 1] 1/(1 + x^3)",
                           "check": "ring", "facts": []}),
        "refusal": "close-schema-not-closed",
        "why": "Int is not on the closed whitelist. Without the whitelist "
               "refl would close this and the goal would say nothing (§9). "
               "The scope check passes, because the value has no free "
               "variable and its x is its own binder. So the refusal must "
               "come from the whitelist.",
    },
    {
        "id": "field_raw_fact",
        "goal": P1_2_GOAL,
        "setup": [],
        # ("raw", s): the script passes parse_judgement(s), a Judgement
        # object and not a handle.
        "move": ("ftc", {"F": P1_2_F, "check": "field",
                         "facts": [("raw", "(sqrt 3)^2 == 3")]}),
        "refusal": "fact-not-minted-handle",
        "why": "a fact must be a theorem handle (§6.2: soundness needs only "
               "that each fact is a theorem, passed as a handle, §15.3).",
    },
    # Added: two matcher refusals that pin Q21's "ring, never field".
    {
        "id": "rewrite_lhs_mismatch",
        "added": True,
        "goal": PROOFS["P1.2"]["steps"][1]["goal_after"],
        "setup": [],
        "move": ("rewrite", {"entry": "atan_one_sqrt3", "inst": {},
                             "at": "atan((2*0 - 1)/sqrt 3)"}),
        "refusal": "rewrite-lhs-mismatch",
        "why": "ring_nf of the argument is -inv(sqrt 3), not inv(sqrt 3). "
               "atan_odd is needed first.",
    },
    {
        "id": "rewrite_needs_field",
        "added": True,
        "goal": "Int[x = 1 .. 2] ln(x/x) == ?A",
        "setup": [],
        "move": ("rewrite", {"entry": "ln_one", "inst": {}, "at": "ln(x/x)"}),
        "refusal": "rewrite-lhs-mismatch",
        "why": "x/x is 1 only in field, owing x # 0. ring reads it as "
               "x*inv(x) (E3), and Q21 never field-normalises.",
    },
    # Added: D10's consequence for deriv (E12, E9).
    {
        "id": "ftc_F_contains_D",
        "added": True,
        "goal": P1_2_GOAL,
        "setup": [],
        "move": ("ftc", {"F": "D[x] x^2", "check": "ring", "facts": []}),
        "refusal": "deriv-no-rule",
        "why": "x is free in D[x] x^2 (GRAMMAR.md D10), so d_const does not "
               "apply and no §6.3 rule does. The step is refused before any "
               "substitution F[x := b], so subst-under-D is never reached. "
               "Read as a binder, d_const would give 0 where the derivative "
               "of 2*x is 2.",
    },
    # Added: E9's infinite-endpoint refusal (DOMAIN_RULES E4, §5.1).
    {
        "id": "ftc_infinite_endpoint",
        "added": True,
        "goal": "Int[x = 0 .. oo] exp(-x) == ?A",
        "setup": [],
        "move": ("ftc", {"F": "-exp(-x)", "check": "ring", "facts": []}),
        "refusal": "ftc-infinite-endpoint",
        "why": "the derivative check itself would pass (SymPy: "
               "d/dx(-exp(-x)) = exp(-x)), so the refusal must come from "
               "the endpoint check and not from ftc-check-failed. Accepted, "
               "it would put oo inside F[x := oo] - F[x := 0], which §5.1 "
               "forbids.",
    },
    # Added: REWRITE_RULE step 2's "encloses" (GRAMMAR.md §5).
    {
        "id": "rewrite_in_own_endpoint",
        "added": True,
        "goal": "Int[t = 0 .. sqrt(1)] t == ?A",
        "setup": [],
        "move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "t - t + 1"},
                             "at": "sqrt(1)"}),
        "refusal": "rewrite-scope",
        "why": "the match passes (ring_nf((t - t + 1)^2) = 1 = ring_nf(1), "
               "SymPy), but the occurrence is in Int[t = ..]'s own hi, "
               "outside t's scope, so the inst value's t is not in scope "
               "(step 6). Read with 'enclosing' as tree ancestor, it would "
               "be accepted, emitting t - t + 1 >= 0 @ [0, sqrt 1] and the "
               "orientation 0 <= sqrt 1, for a t that is not bound where "
               "the rewrite acts.",
    },
    # Added: D11 and E19 accept a goal with D[x] (GRAMMAR.md §5 bv).
    {
        "id": "close_D_goal_scope_passes",
        "added": True,
        "goal": "D[x] x^2 == ?A",
        "setup": [],
        "move": ("close", {"value": "2*x", "check": "ring", "facts": []}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "a regression for D10/D11/E19. The goal installs (D's x is in "
               "fv, not bv, so D11 holds) and the scope check passes (x is "
               "not in bv of the original goal). ring then refuses to "
               "normalise the side D[x] x^2 (E26 (b)); before E26 it read "
               "it as an opaque atom and the check failed with "
               "close-check-failed. Either way the refusal comes after the "
               "scope check and the whitelist, so it must never be "
               "close-scope-bound-variable or a D11 refusal at goal "
               "installation. It also depends on Var being on the closed "
               "whitelist (E23); otherwise the refusal would be "
               "close-schema-not-closed.",
    },
    # Added: REWRITE_RULE step 9 (b), an Int range mentioning x below D[x].
    {
        "id": "rewrite_under_D_through_Int",
        "added": True,
        "goal": "D[x](Int[t = 0 .. x] sqrt(t^2)) == ?A",
        "setup": [],
        "move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "t"},
                             "at": "sqrt(t^2)"}),
        "refusal": "rewrite-under-D-needs-open-domain",
        "why": "the match and the scope check pass (t is bound by the Int "
               "whose body holds the occurrence), and H = [t >= 0] does not "
               "mention x, so test (a) of step 9 passes. But the occurrence "
               "is under Int[t = 0 .. x] below D[x]. Its hypothesis would be "
               "emitted on the closed [0, x] with the orientation 0 <= x "
               "(E4), so the equation's domain in x is x >= 0, which is not "
               "open (§6.1 rev 9). Test (b) refuses it. (SymPy: the "
               "integral is x*|x|/2 before and x^2/2 after, which differ "
               "for x < 0.)",
    },
    # Added (user decision 2026-09-24, review fix): REWRITE_RULE step 9 (a)
    # applied to step 10's charges from R, not only to H. Each case's H is
    # empty, so (a) on H and (b) are vacuous, and each was accepted while
    # (a) read H alone.
    {
        "id": "rewrite_under_D_R_closed_former",
        "added": True,
        "goal": "D[x](atan(-x)) == ?A @ x >= 0",
        "setup": [],
        "move": ("rewrite", {"entry": "atan_odd",
                             "inst": {"u": "x + (sqrt x - sqrt x)"},
                             "at": "atan(-x)"}),
        "refusal": "rewrite-under-D-needs-open-domain",
        "why": "installation owes nothing (atan is total). The match passes: "
               "ring_nf(-(x + (sqrt x - sqrt x))) = -x (SymPy), the two sqrt "
               "x atoms cancelling, and x is free, so step 6 passes. Step 10 "
               "would charge R = -atan(x + (sqrt x - sqrt x)) with sqrt's "
               "x >= 0, which mentions x and is not strict, so step 9 (a) "
               "refuses it. Accepted, the new left side is undefined for "
               "x < 0, so its derivative does not exist at 0, while "
               "D[x] atan(-x) is -1 there (SymPy). The goal's own x >= 0 "
               "would tag the charge hyp: a well-tagged charge is still "
               "refused, because the domain below D is what must be open.",
    },
    {
        "id": "rewrite_under_D_R_divisor",
        "added": True,
        "goal": "D[x](atan(-x)) == ?A @ x >= 0",
        "setup": [],
        "move": ("rewrite", {"entry": "atan_odd",
                             "inst": {"u": "x + (1/(sqrt x + 1)"
                                           " - 1/(sqrt x + 1))"},
                             "at": "atan(-x)"}),
        "refusal": "rewrite-under-D-needs-open-domain",
        "why": "the same through a divisor, the gap as it stood before E26: "
               "the inv(sqrt x + 1) atoms cancel in the match (SymPy, with "
               "the atom a free symbol), and step 10 charges "
               "sqrt x + 1 # 0, strict but with an x-mentioning sqrt "
               "subterm, and sqrt x's x >= 0. Either fails step 9 (a). "
               "Before E26 only the divisor was charged, and step 9 (a) did "
               "not look at it, so the step was accepted.",
    },
    # Added (user decision 2026-09-24, review fix): REWRITE_RULE step 9 (b)
    # applied to step 10's charges from R, not only to H.
    {
        "id": "rewrite_under_D_through_Int_R_former",
        "added": True,
        "goal": "D[x](Int[t = 1 .. x] atan(-t)) == ?A",
        "setup": [],
        "move": ("rewrite", {"entry": "atan_odd",
                             "inst": {"u": "t + (sqrt t - sqrt t)"},
                             "at": "atan(-t)"}),
        "refusal": "rewrite-under-D-needs-open-domain",
        "why": "installation owes nothing (atan is total). The match passes: "
               "ring_nf(-(t + (sqrt t - sqrt t))) = -t (SymPy), and t is "
               "bound by the enclosing Int (step 6). atan_odd's H is empty, "
               "and step 10's only charge, sqrt t's t >= 0, does not mention "
               "x, so step 9 (a) passes. But that charge is emitted at P, "
               "which holds the closed range [1, x] with the orientation "
               "1 <= x (step 7, E4), so the equation's domain in x is closed "
               "and step 9 (b) refuses it. Accepted, the rewritten integral "
               "is defined only for x >= 0, so its derivative does not exist "
               "for x <= 0, while D[x] of the original is -atan(x) "
               "everywhere (SymPy).",
    },
    {
        "id": "rewrite_under_D_through_Int_R_former_ln",
        "added": True,
        "goal": "D[x](Int[t = 1 .. x] atan(-t)) == ?A",
        "setup": [],
        "move": ("rewrite", {"entry": "atan_odd",
                             "inst": {"u": "t + (ln t - ln t)"},
                             "at": "atan(-t)"}),
        "refusal": "rewrite-under-D-needs-open-domain",
        "why": "the ln twin of rewrite_under_D_through_Int_R_former. ln has "
               "an open natural domain, so step 10's charge t > 0 is strict "
               "and has no closed-domain subterm, and it does not mention x: "
               "step 9 (a) passes on any reading. The charge is emitted at "
               "P, which holds the closed [1, x] and 1 <= x (step 7, E4), so "
               "step 9 (b) refuses it. ring_nf(-(t + (ln t - ln t))) = -t "
               "(SymPy). Accepted, the rewritten integral is defined only "
               "for x > 0, while D[x] of the original is -atan(x) "
               "everywhere (SymPy).",
    },
    # Added: E25, a divisor that ring-normalises to zero, at installation.
    {
        "id": "install_zero_divisor",
        "added": True,
        "goal": "Int[x = 0 .. 1] 1/(x - x) == ?A",
        "setup": [],
        "move": ("install", {}),
        "refusal": "divisor-normalises-to-zero",
        "why": "E6 charges the integrand's divisor x - x at installation, "
               "and ring_nf(x - x) = 0, so E25 refuses the goal before any "
               "x - x # 0 @ [0, 1] is admitted.",
    },
    # Added: E25, field's own test, on a divisor ring does not see as zero.
    {
        "id": "field_zero_divisor",
        "added": True,
        "goal": "Int[x = 1 .. 2] 1/(x/x - 1) == ?A",
        # Installation passes, because ring_nf(x/x - 1) = x*inv(x) - 1 is
        # nonzero. It admits x # 0 @ [1, 2] (range) and the false
        # x/x - 1 # 0 @ [1, 2] (tagged none by E24; outside the no-none
        # assertion, since this is a BAD_MOVES run).
        "setup": [],
        "move": ("ftc", {"F": "x", "check": "field", "facts": []}),
        "refusal": "divisor-normalises-to-zero",
        "why": "deriv gives 1 (d_var). field's input 1 == 1/(x/x - 1) "
               "carries the divisor x/x - 1, whose field normal form has "
               "numerator 0 (SymPy: cancel(x/x - 1) = 0). field tests its "
               "divisors before normalising, so the refusal is "
               "divisor-normalises-to-zero, never ftc-check-failed (E25).",
    },

    # Added by user decision 2026-09-24: E26 (a), a partial builtin whose
    # literal argument lies outside its domain. Each goal is refused when it
    # is installed, since installation charges the goal's formers (E6, E26)
    # and E7 refuses a false literal. Before E26 each installed, and ring
    # closed it with ?A := 0 as 'Proved.' with nothing owed. The close is now
    # never reached. One case per bound of each builtin, so that dropping any
    # single condition is caught (DEFINEDNESS_MUTATIONS); the open ends
    # (ln at 0, atanh at 1 and -1) are pinned here, and the closed ends by
    # DEFINEDNESS_CASES.
    {
        "id": "ln_negative_literal", "added": True,
        "goal": "0*ln(-1) == ?A", "setup": [], "move": ("install", {}),
        "refusal": "obligation-refuted",
        "why": "ln(-1) owes -1 > 0, which is literal and false (E26, E7). "
               "SymPy: ln(-1) = I*pi, not a real.",
    },
    {
        "id": "ln_zero_literal", "added": True,
        "goal": "0*ln 0 == ?A", "setup": [], "move": ("install", {}),
        "refusal": "obligation-refuted",
        "why": "ln 0 owes 0 > 0, false: ln's domain is open at 0. A former "
               "written u >= 0 would install it.",
    },
    {
        "id": "sqrt_negative_literal", "added": True,
        "goal": "0*sqrt(-1) == ?A", "setup": [], "move": ("install", {}),
        "refusal": "obligation-refuted",
        "why": "sqrt(-1) owes -1 >= 0, false (E26, E7). SymPy: sqrt(-1) = I.",
    },
    {
        "id": "asin_above_literal", "added": True,
        "goal": "0*asin 2 == ?A", "setup": [], "move": ("install", {}),
        "refusal": "obligation-refuted",
        "why": "asin 2 owes 2 >= -1, true and discharged, and 2 <= 1, false. "
               "SymPy: asin(2) is not real.",
    },
    {
        "id": "asin_below_literal", "added": True,
        "goal": "0*asin(-2) == ?A", "setup": [], "move": ("install", {}),
        "refusal": "obligation-refuted",
        "why": "asin(-2) owes -2 >= -1, false, and -2 <= 1. The lower "
               "bound's own case: a former that dropped it would install "
               "this goal.",
    },
    {
        "id": "acos_above_literal", "added": True,
        "goal": "0*acos 2 == ?A", "setup": [], "move": ("install", {}),
        "refusal": "obligation-refuted",
        "why": "acos 2 owes 2 >= -1 and 2 <= 1, the second false (E26, E7). "
               "SymPy: acos(2) is not real.",
    },
    {
        "id": "acos_below_literal", "added": True,
        "goal": "0*acos(-2) == ?A", "setup": [], "move": ("install", {}),
        "refusal": "obligation-refuted",
        "why": "acos(-2) owes -2 >= -1, false.",
    },
    {
        "id": "acosh_below_literal", "added": True,
        "goal": "0*acosh 0 == ?A", "setup": [], "move": ("install", {}),
        "refusal": "obligation-refuted",
        "why": "acosh 0 owes 0 >= 1, false (E26, E7). SymPy: acosh(0) = "
               "I*pi/2.",
    },
    {
        "id": "atanh_upper_end", "added": True,
        "goal": "0*atanh 1 == ?A", "setup": [], "move": ("install", {}),
        "refusal": "obligation-refuted",
        "why": "atanh 1 owes 1 > -1, true, and 1 < 1, false: atanh's domain "
               "is open at 1 (SymPy: atanh(1) = oo). A closed former would "
               "install it.",
    },
    {
        "id": "atanh_lower_end", "added": True,
        "goal": "0*atanh(-1) == ?A", "setup": [], "move": ("install", {}),
        "refusal": "obligation-refuted",
        "why": "atanh(-1) owes -1 > -1, false (SymPy: atanh(-1) = -oo).",
    },
    # E26 (a) at the two other places a term enters, a rewrite's R and
    # close's value (E6's list; installation is covered above, and ftc's F
    # by P1.2's ln formers).
    {
        "id": "rewrite_R_owes_domain", "added": True,
        "goal": "atan(-y) == ?A", "setup": [],
        "move": ("rewrite", {"entry": "atan_odd",
                             "inst": {"u": "y + (ln(-1) - ln(-1))"},
                             "at": "atan(-y)"}),
        "refusal": "obligation-refuted",
        "why": "the match passes, since ring_nf(-(y + (ln(-1) - ln(-1)))) = "
               "-y, the two ln(-1) atoms cancelling (REWRITE_RULE step 5). "
               "Step 10 then charges R = -atan(y + (ln(-1) - ln(-1))), whose "
               "ln(-1) owes -1 > 0, and E7 refutes it. Before E26 the step "
               "was accepted and carried an undefined term into the goal "
               "owing nothing. The partial-builtin twin of step 5's "
               "atan_odd u := x/x - x/x example.",
    },
    {
        "id": "close_value_owes_domain", "added": True,
        "goal": "0 == ?A", "setup": [],
        "move": ("close", {"value": "0*ln(-1)", "check": "ring",
                           "facts": []}),
        "refusal": "obligation-refuted",
        "why": "the scope check and the whitelist pass (ln is on it, E23), "
               "and close then charges the value's formers at G: -1 > 0, "
               "false. Before E26 ring proved 0 == 0*ln(-1) and the report "
               "was 'Proved.' for the theorem 0 == 0*ln(-1).",
    },

    # Added by user decision 2026-09-24: E26 (b), Int and D refused by every
    # normaliser. The cases cover every normaliser and node pair (ring, field
    # and norm_num, each on Int and on D) and every call site E26 (b) names on
    # both nodes: close's check, ftc's check, E25's charge-time ring_nf(d),
    # rewrite's match, deriv's d_const (E12), and both halves of E7's test, the
    # proposition and the domain. field's fact reduction has no case of its
    # own. A fact's inst values are charged by the step that uses it (E10, E6),
    # so an Int or D in them meets E25's ring_nf or E7 there and is refused;
    # and any Int or D the reduction would meet is in field's own input, which
    # field's normaliser refuses (field_refuses_Int, field_refuses_D). So no
    # verdict can come through the fact path. field's divisor test has no case
    # of its own either. Every divisor in field's input was charged where it
    # entered: goal installation, a rewrite's right-hand side, and ftc's F and
    # new goal. There E25's ring_nf already refused one holding an Int or D
    # (divisor_test_refuses_Int, divisor_test_refuses_D). close's value holds
    # no Int or D, since E23's whitelist refuses them. A divisor new in deriv's
    # output was charged by route_div, and deriv's output holds none (E12's
    # d_const guard, E26 (b)). A fact's inst values are charged where the fact
    # is used (E10), so their divisors also pass E25 there, and field's normal
    # form refuses the same term with the same code. Int[x = 0 .. oo] 1
    # diverges and D[x](abs x) does not exist at 0, so each left side below is
    # undefined, and each case was 'Proved.' (or, for a divisor, a different
    # refusal, or for an obligation, an admission) while ring and norm_num read
    # them as atoms. The cases marked review fix were added after E26 was first
    # written, to complete the pairs (DATA_CHANGES).
    {
        "id": "ring_refuses_Int", "added": True,
        "goal": "(Int[x = 0 .. oo] 1) - (Int[x = 0 .. oo] 1) == ?A",
        "setup": [],
        "move": ("close", {"value": "0", "check": "ring", "facts": []}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "installation owes nothing (the integrand 1 has no former, "
               "and an infinite end brings no orientation, E4). close's "
               "scope check and whitelist pass on the value 0, and ring "
               "refuses the side holding the Ints. Before E26 the two Int "
               "atoms cancelled and the report was 'Proved.' (SymPy: the "
               "integral is oo).",
    },
    {
        "id": "ring_refuses_D", "added": True,
        "goal": "D[x](abs x) - D[x](abs x) == ?A", "setup": [],
        "move": ("close", {"value": "0", "check": "ring", "facts": []}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "abs is total, so installation owes nothing, and ring refuses "
               "the side holding the D nodes. Before E26 they cancelled and "
               "the report was 'Proved.' for a theorem @ true whose left "
               "side is undefined at x = 0, where D[x](abs x) does not exist "
               "(SymPy: the one-sided difference quotients tend to -1 and "
               "1).",
    },
    {
        "id": "field_refuses_D", "added": True,
        "goal": "D[x](abs x) - D[x](abs x) == ?A", "setup": [],
        "move": ("close", {"value": "0", "check": "field", "facts": []}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "the same, by field: its normal form refuses the side "
               "holding the D nodes (E26 (b)). The input has no divisor, so "
               "this does not exercise field's divisor test; the block "
               "comment above says why that test needs no case of its own.",
    },
    {
        "id": "field_refuses_Int", "added": True,  # review fix
        "goal": "(Int[x = 0 .. oo] 1) - (Int[x = 0 .. oo] 1) == ?A",
        "setup": [],
        "move": ("close", {"value": "0", "check": "field", "facts": []}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "the same as ring_refuses_Int, by field. Installation owes "
               "nothing, and field's normal form refuses the side holding "
               "the Ints (E26 (b)). The input has no divisor, so this does "
               "not exercise field's divisor test; the block comment above "
               "says why that test needs no case of its own. Before E26 "
               "this was a plain 'Proved.'.",
    },
    {
        "id": "norm_num_refuses_Int", "added": True,
        "goal": "sqrt((Int[x = 0 .. oo] 1) - (Int[x = 0 .. oo] 1)) == ?A",
        "setup": [], "move": ("install", {}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "sqrt's former owes (Int[x = 0 .. oo] 1) - (Int[x = 0 .. oo] "
               "1) >= 0, closed, so domain true (E5). It reaches E7, and "
               "norm_num refuses it rather than cancel the Ints to 0 >= 0 "
               "or leave it admitted (E26 (b)).",
    },
    {
        "id": "norm_num_refuses_D", "added": True,  # review fix
        "goal": "ln(D[x] x^2) == ?A",
        "setup": [], "move": ("install", {}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "ln's former owes D[x] x^2 > 0 @ true. It is not closed (x is "
               "free, GRAMMAR.md D10) and not literal, so it pins that the "
               "refusal covers D nodes and non-closed obligations, not only "
               "the closed Int of norm_num_refuses_Int. It is refused rather "
               "than admitted (E26 (b), E7). Before E26 nothing was owed; "
               "read as 2*x > 0 it would be false for x <= 0 (SymPy).",
    },
    {
        "id": "norm_num_refuses_open_Int", "added": True,  # review fix
        "goal": "sqrt(Int[t = 0 .. x] t) == ?A",
        "setup": [], "move": ("install", {}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "the non-closed Int twin: sqrt's former owes "
               "(Int[t = 0 .. x] t) >= 0 @ true with x free. The Int's body "
               "t owes nothing, so no key uses its range and no orientation "
               "0 <= x is owed (E4); nothing else is emitted. The "
               "proposition happens to be true (the integral is x^2/2, "
               "SymPy), and it is refused all the same: an obligation about "
               "an Int's value presupposes that the Int exists (E26 (b)).",
    },
    {
        "id": "norm_num_refuses_Int_in_domain", "added": True,  # review fix
        "goal": "ln x * 0 == ?A @ x > (Int[t = 0 .. oo] 1)"
                " - (Int[t = 0 .. oo] 1)",
        "setup": [], "move": ("install", {}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "the domain half of E7's refusal. ln x owes x > 0 @ Γ (E26), "
               "and its proposition holds no Int, but its domain, the "
               "goal's own hypothesis, holds two. It reaches E7 and is "
               "refused rather than admitted (E26 (b)). Accepted, it would "
               "be admitted with a tag computed from a domain whose Ints "
               "cancel, and close 0 by ring (the side ln x * 0 holds no "
               "Int) would report 'Proved modulo 1 admissions' for a "
               "theorem whose hypothesis compares x with a difference of "
               "divergent integrals (SymPy: Int[t = 0 .. oo] 1 = oo). A "
               "kernel that checks only the proposition passes every other "
               "case.",
    },
    {
        "id": "norm_num_refuses_D_in_domain", "added": True,  # review fix
        "goal": "ln x * 0 == ?A @ x > D[y] y^2",
        "setup": [], "move": ("install", {}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "norm_num_refuses_Int_in_domain with a D node: ln x owes "
               "x > 0 @ x > D[y] y^2, whose domain holds the D node (y is "
               "free in it by GRAMMAR.md D10, so the goal is stated in x "
               "and y). It is refused at E7 rather than admitted (E26 (b)). "
               "Read as 2*y, the hypothesis would be x > 2*y (SymPy), and "
               "close 0 by ring would report 'Proved modulo 1 admissions'.",
    },
    {
        "id": "divisor_test_refuses_Int", "added": True,
        "goal": "1/((Int[x = 0 .. oo] 1) - (Int[x = 0 .. oo] 1)) == ?A",
        "setup": [], "move": ("install", {}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "E25's charge-time test computes ring_nf of the divisor, and "
               "ring refuses the Ints in it. Before E26 they cancelled and "
               "the refusal was divisor-normalises-to-zero, which claimed a "
               "value, 0, for a difference of two divergent integrals.",
    },
    {
        "id": "divisor_test_refuses_D", "added": True,  # review fix
        "goal": "1/(D[x](abs x) - D[x](abs x)) == ?A",
        "setup": [], "move": ("install", {}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "divisor_test_refuses_Int with D nodes: E25's ring_nf of the "
               "divisor refuses them. Before E26 they cancelled and the "
               "refusal was divisor-normalises-to-zero.",
    },
    {
        "id": "match_refuses_Int", "added": True,
        "goal": "atan((Int[x = 0 .. oo] 1) - (Int[x = 0 .. oo] 1)) == ?A",
        "setup": [],
        "move": ("rewrite", {"entry": "atan_odd", "inst": {"u": "0"},
                             "at": "atan((Int[x = 0 .. oo] 1)"
                                   " - (Int[x = 0 .. oo] 1))"}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "atan is total, so installation owes nothing. REWRITE_RULE "
               "step 3 compares ring_nf(-0) with ring_nf of the target's "
               "argument, and ring refuses the Ints there. Before E26 both "
               "were 0, the match passed, and the goal became "
               "-atan 0 == ?A.",
    },
    {
        "id": "match_refuses_D", "added": True,  # review fix
        "goal": "atan(D[x](abs x) - D[x](abs x)) == ?A",
        "setup": [],
        "move": ("rewrite", {"entry": "atan_odd", "inst": {"u": "0"},
                             "at": "atan(D[x](abs x) - D[x](abs x))"}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "match_refuses_Int with D nodes. atan and abs are total, so "
               "installation owes nothing, and step 3's ring_nf of the "
               "target's argument refuses the D nodes.",
    },
    {
        "id": "ftc_check_refuses_Int", "added": True,  # review fix
        "goal": "Int[x = 0 .. 1] (1 + ((Int[t = 0 .. oo] 1)"
                " - (Int[t = 0 .. oo] 1))) == ?A",
        "setup": [],
        "move": ("ftc", {"F": "x", "check": "ring", "facts": []}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "installation owes nothing: the integrand has no former, "
               "the outer range is literal (E4, no orientation) and the "
               "inner ranges are infinite. ftc's endpoints 0 and 1 are "
               "finite, F := x owes no former, and deriv gives 1 (d_var). "
               "ftc's check then refuses the side f, which holds the Ints. "
               "Before E26 the check passed (the Ints cancel), and close 1 "
               "gave 'Proved modulo 3 admissions', one of them f in "
               "C^0([0, 1]) for an f that is undefined (SymPy: the inner "
               "integral is oo). ftc consumes only its own top-level Int "
               "(E9); an Int nested in f reaches the check like any other "
               "term.",
    },
    {
        "id": "ftc_check_refuses_D", "added": True,  # review fix
        "goal": "Int[x = -1 .. 1] (1 + (D[x](abs x) - D[x](abs x))) == ?A",
        "setup": [],
        "move": ("ftc", {"F": "x", "check": "ring", "facts": []}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "ftc_check_refuses_Int with D nodes. abs is total and the "
               "range is literal, so installation owes nothing (E4, no "
               "orientation). D is not a binder for the no-shadowing rule "
               "(GRAMMAR.md D10), so D[x] under Int[x] is legal. ftc's "
               "endpoints are finite, F := x owes no former, and deriv gives "
               "1 (d_var). ftc's check then refuses the side f, which holds "
               "the D nodes. Before E26 the check passed (the D nodes "
               "cancel), and close 2 gave 'Proved modulo 3 admissions' for "
               "an integrand undefined at x = 0, where D[x](abs x) does not "
               "exist (SymPy: the one-sided difference quotients tend to -1 "
               "and 1). E7 never sees f: f in C^0 is reg, and the derivative "
               "premise is decided in the step.",
    },
    {
        "id": "ftc_F_holds_x_free_Int", "added": True,  # review fix
        "goal": "Int[x = 0 .. 1] 1 == ?A",
        "setup": [],
        "move": ("ftc", {"F": "x + ((Int[t = 0 .. oo] 1)"
                              " - (Int[t = 0 .. oo] 1))",
                         "check": "ring", "facts": []}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "E12's d_const guard. The range [0, 1] is literal (E4, no "
               "orientation), and F's formers are none: the Ints' body 1 "
               "owes nothing and their ends are infinite. deriv applies "
               "d_add, then d_var on x, then meets the x-free subterm "
               "holding the Ints, where d_const would give 0; it refuses "
               "instead (E26 (b)). Without the guard deriv gives 1 + 0, "
               "ring's sides 1 + 0 and 1 hold no Int, the check passes, and "
               "D[x](x + (I - I)) == 1 @ (0, 1) is recorded DISCHARGED "
               "(deriv+ring) with two reg admissions on an F that is "
               "undefined (SymPy: Int[t = 0 .. oo] 1 = oo). No verdict "
               "follows from that, since the new goal still holds the Ints "
               "and every later ring or field close refuses them, but a "
               "false premise is recorded as discharged. The refused step "
               "emits nothing (E13).",
    },
    {
        "id": "ftc_F_holds_x_free_D", "added": True,  # review fix
        "goal": "Int[x = 0 .. 1] 1 == ?A",
        "setup": [],
        "move": ("ftc", {"F": "x + (D[y](abs y) - D[y](abs y))",
                         "check": "ring", "facts": []}),
        "refusal": "Int-or-D-not-normalisable",
        "why": "ftc_F_holds_x_free_Int with D nodes. x is not free in "
               "D[y](abs y) (GRAMMAR.md D10 puts y, not x, in its free "
               "variables), so the subterm is x-free and d_const's guard "
               "refuses it; abs is total, so F owes no former. Contrast "
               "ftc_F_contains_D, whose D[x] x^2 has x free and gets "
               "'deriv-no-rule'. D[y](abs y) does not exist at y = 0 "
               "(SymPy: the one-sided difference quotients tend to -1 and "
               "1).",
    },

    # Added by user decision 2026-09-24 (evaluated answers): E27's refusals
    # (EVALUATED_RULE). Every one is a close whose check PASSES, so the only
    # refusal left is E27's: most are refl on a fresh goal `V == ?A` with
    # value V, and two start from a P1.1 state with the goal's own left side.
    # 'e27' holds what the script asserts beyond the code: the clause ('a',
    # or 'b1' to 'b4'), `at`, the offending subterm, compared with the
    # refusal's residual as a tree, the entry for (a), and the message,
    # asserted as E27_MESSAGES[clause[0]] filled with show(residual) and the
    # entry. 'evaluated' is the fully evaluated form the named moves reach;
    # it is not run, and SymPy confirms it equals the value (VERIFIED), so
    # each refusal is about form, not truth. The last case pins the order:
    # a wrong AND unevaluated value is refused by the check, not by E27.
    {
        "id": "e27_exp_zero_pow_argument", "added": True,
        "goal": "exp(0^2) == ?A", "setup": [],
        "move": ("close", {"value": "exp(0^2)", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "exp(0^2)", "entry": "exp_zero",
                "message": "exp(0^2) can still be evaluated (exp_zero)"},
        "evaluated": "1",
        "why": "(a1): ring_nf(0^2) = 0 = ring_nf(0), E1 step 3's match, as "
               "S2's rewrite of exp(0^2) uses. (a) is searched before (b), "
               "so the literal 0^2 inside is not the one reported.",
    },
    {
        "id": "e27_exp_zero_sum_argument", "added": True,
        "goal": "exp(1 - 1) == ?A", "setup": [],
        "move": ("close", {"value": "exp(1 - 1)", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "exp(1 - 1)", "entry": "exp_zero",
                "message": "exp(1 - 1) can still be evaluated (exp_zero)"},
        "evaluated": "1",
        "why": "(a1): ring_nf(1 - 1) = 0.",
    },
    {
        "id": "e27_exp_zero_variable_argument", "added": True,
        "goal": "exp(x - x) == ?A", "setup": [],
        "move": ("close", {"value": "exp(x - x)", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "exp(x - x)", "entry": "exp_zero",
                "message": "exp(x - x) can still be evaluated (exp_zero)"},
        "evaluated": "1",
        "why": "(a1) with a free variable: ring_nf(x - x) = 0, and E23 "
               "admits Var, so a value in a goal's free variables is "
               "checked the same way.",
    },
    {
        "id": "e27_sqrt_sq_val", "added": True,
        "goal": "(sqrt 3)^2 == ?A", "setup": [],
        "move": ("close", {"value": "(sqrt 3)^2", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "(sqrt 3)^2", "entry": "sqrt_sq_val",
                "message": "(sqrt 3)^2 can still be evaluated "
                           "(sqrt_sq_val)"},
        "evaluated": "3",
        "why": "(a2): Pow(sqrt 3, 2), a := 3. The move is the fact in a "
               "field check (§6.8: never a rewrite), and its 3 >= 0 is the "
               "value's own sqrt domain (E26). ring proves the refl, since "
               "(sqrt 3)^2 is s^2 on both sides.",
    },
    {
        "id": "e27_sin_pi_half_in_answer", "added": True,
        "goal": "2*sin(pi/2) == ?A", "setup": [],
        "move": ("close", {"value": "2*sin(pi/2)", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "sin(pi/2)", "entry": "sin_pi_half",
                "message": "sin(pi/2) can still be evaluated (sin_pi_half)"},
        "evaluated": "2",
        "why": "(a1) below the root: the pre-order walk reaches sin(pi/2) "
               "inside the product, and the residual is that subterm, not "
               "the value.",
    },
    {
        "id": "e27_atan_odd", "added": True,
        "goal": "atan(-1/sqrt 3) == ?A", "setup": [],
        "move": ("close", {"value": "atan(-1/sqrt 3)", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "atan(-1/sqrt 3)", "entry": "atan_odd",
                "message": "atan(-1/sqrt 3) can still be evaluated "
                           "(atan_odd)"},
        "evaluated": "-(pi/6)",
        "why": "(a2): ring_nf(-1/sqrt 3) = -inv(sqrt 3), every coefficient "
               "negative. atan_one_sqrt3 does not count (its argument "
               "normalises to +inv(sqrt 3), BAD_MOVES rewrite_lhs_mismatch), "
               "and atan_odd comes after it in ENTRIES, so the order is not "
               "what picks atan_odd. The moves are P1.2's s7 then s8.",
    },
    {
        "id": "e27_atan_one_sqrt3", "added": True,
        "goal": "atan(1/sqrt 3) == ?A", "setup": [],
        "move": ("close", {"value": "atan(1/sqrt 3)", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "atan(1/sqrt 3)",
                "entry": "atan_one_sqrt3",
                "message": "atan(1/sqrt 3) can still be evaluated "
                           "(atan_one_sqrt3)"},
        "evaluated": "pi/6",
        "why": "(a1); atan_odd does not count, since inv(sqrt 3)'s "
               "coefficient is positive.",
    },
    {
        "id": "e27_sqrt_sq_literal", "added": True,
        "goal": "sqrt 4 == ?A", "setup": [],
        "move": ("close", {"value": "sqrt 4", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "sqrt 4", "entry": "sqrt_sq",
                "message": "sqrt 4 can still be evaluated (sqrt_sq)"},
        "evaluated": "2",
        "why": "(a2): ring_nf(4) = 2*2 with 2 closed. The move is sqrt_sq "
               "with u := 2, which E1 step 3 accepts (ring_nf(2^2) = 4) "
               "and whose 2 >= 0 norm_num closes. A structural reading "
               "(sqrt(Pow(c, 2)) only) would accept this.",
    },
    {
        "id": "e27_sqrt_sq_normalised", "added": True,
        "goal": "sqrt(pi^2/4) == ?A", "setup": [],
        "move": ("close", {"value": "sqrt(pi^2/4)", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "sqrt(pi^2/4)", "entry": "sqrt_sq",
                "message": "sqrt(pi^2/4) can still be evaluated (sqrt_sq)"},
        "evaluated": "pi/2",
        "why": "(a2): ring_nf(pi^2/4) = (pi/2)*(pi/2), §18 Q21's example, "
               "which P1.1-fallback s2 rewrites with u := pi/2.",
    },
    {
        "id": "e27_entry_before_arithmetic", "added": True,
        "goal": "ln(1 + 0) == ?A", "setup": [],
        "move": ("close", {"value": "ln(1 + 0)", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "ln(1 + 0)", "entry": "ln_one",
                "message": "ln(1 + 0) can still be evaluated (ln_one)"},
        "evaluated": "0",
        "why": "both clauses apply: ln_one at ln(1 + 0) (P1.2 s4's target) "
               "and b1 at 1 + 0. (a) is searched first over the whole "
               "value, so ln_one is named (EVALUATED_RULE, Reporting). "
               "The value owes 1 + 0 > 0, discharged (E26, E7).",
    },
    {
        "id": "e27_goal_lhs_after_ftc", "added": True,
        "goal": P1_1_GOAL, "state": ("P1.1", "s2"),
        "move": ("close", {"value": "2*sin(pi/2) - 2*(pi/2)*cos(pi/2)"
                                    " - (2*sin 0 - 2*0*cos 0)",
                           "check": "ring", "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "sin(pi/2)", "entry": "sin_pi_half",
                "message": "sin(pi/2) can still be evaluated (sin_pi_half)"},
        "evaluated": "2",
        "why": "§9's vacuity one step after ftc: the value is the current "
               "goal's own left side, P1_1_AFTER_FTC's, so ring proves it "
               "and E19 passes (no t). Before E27 this closed, and the "
               "theorem said only what ftc had. (a)'s first node in "
               "pre-order is s3's target; (b) would fire at the root "
               "(2*0*cos 0 is a zero summand) but is searched second.",
    },
    {
        "id": "e27_one_plus_one", "added": True,
        "goal": "1 + 1 == ?A", "setup": [],
        "move": ("close", {"value": "1 + 1", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b1", "at": "1 + 1", "entry": None,
                "message": "1 + 1 is unreduced literal arithmetic"},
        "evaluated": "2",
        "why": "b1, a literal term that is not a rational literal (b2's "
               "two literal summands also fire; b1 is tried first).",
    },
    {
        "id": "e27_two_minus_zero", "added": True,
        "goal": "2 - 0 == ?A", "setup": [],
        "move": ("close", {"value": "2 - 0", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b1", "at": "2 - 0", "entry": None,
                "message": "2 - 0 is unreduced literal arithmetic"},
        "evaluated": "2",
        "why": "b1: Add(2, Neg 0), and -0 is not a rational literal.",
    },
    {
        "id": "e27_zero_times_pi", "added": True,
        "goal": "0*pi == ?A", "setup": [],
        "move": ("close", {"value": "0*pi", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b3", "at": "0*pi", "entry": None,
                "message": "0*pi is unreduced literal arithmetic"},
        "evaluated": "0",
        "why": "b3 (i). Not b1: pi makes it no literal term, which is why "
               "(b) needs more than b1.",
    },
    {
        "id": "e27_one_squared", "added": True,
        "goal": "1^2 == ?A", "setup": [],
        "move": ("close", {"value": "1^2", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b1", "at": "1^2", "entry": None,
                "message": "1^2 is unreduced literal arithmetic"},
        "evaluated": "1",
        "why": "b1: Pow(Num 1, 2) is a literal term.",
    },
    {
        "id": "e27_two_fourths", "added": True,
        "goal": "2/4 == ?A", "setup": [],
        "move": ("close", {"value": "2/4", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b1", "at": "2/4", "entry": None,
                "message": "2/4 is unreduced literal arithmetic"},
        "evaluated": "1/2",
        "why": "b1: gcd(2, 4) = 2, so Div(2, 4) is no rational literal. "
               "The divisor 4 # 0 is discharged at installation (E6, E7).",
    },
    {
        "id": "e27_like_terms", "added": True,
        "goal": "pi + pi == ?A", "setup": [],
        "move": ("close", {"value": "pi + pi", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b2", "at": "pi + pi", "entry": None,
                "message": "pi + pi is unreduced literal arithmetic"},
        "evaluated": "2*pi",
        "why": "b2: summands with equal ring normal forms, so ring would "
               "add their coefficients 1 + 1.",
    },
    {
        "id": "e27_like_terms_coefficients", "added": True,
        "goal": "pi/2 + pi/3 == ?A", "setup": [],
        "move": ("close", {"value": "pi/2 + pi/3", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b2", "at": "pi/2 + pi/3", "entry": None,
                "message": "pi/2 + pi/3 is unreduced literal arithmetic"},
        "evaluated": "5*pi/6",
        "why": "b2: (1/2)*pi and (1/3)*pi are rational multiples.",
    },
    {
        "id": "e27_like_terms_variable", "added": True,
        "goal": "x - x == ?A", "setup": [],
        "move": ("close", {"value": "x - x", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b2", "at": "x - x", "entry": None,
                "message": "x - x is unreduced literal arithmetic"},
        "evaluated": "0",
        "why": "b2 with a free variable (E23 admits Var); x is free in the "
               "goal, so E19 passes.",
    },
    {
        "id": "e27_two_literal_factors", "added": True,
        "goal": "2*3*pi == ?A", "setup": [],
        "move": ("close", {"value": "2*3*pi", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b3", "at": "2*3*pi", "entry": None,
                "message": "2*3*pi is unreduced literal arithmetic"},
        "evaluated": "6*pi",
        "why": "b3 (iii) at the maximal product, which pre-order reaches "
               "before the literal term 2*3 inside it (b1).",
    },
    {
        "id": "e27_fraction_not_lowest", "added": True,
        "goal": "2*pi/(4*sqrt 3) == ?A", "setup": [],
        "move": ("close", {"value": "2*pi/(4*sqrt 3)", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b3", "at": "2*pi/(4*sqrt 3)", "entry": None,
                "message": "2*pi/(4*sqrt 3) is unreduced literal "
                           "arithmetic"},
        "evaluated": "pi/(2*sqrt 3)",
        "why": "b3 (iv): the literals 2 above and 4 below have gcd 2. "
               "EVALUATED_ACCEPTS e27_split_fraction_lowest is its "
               "contrast.",
    },
    {
        "id": "e27_rational_beside_denominator", "added": True,
        "goal": "(1/2)*pi/3 == ?A", "setup": [],
        "move": ("close", {"value": "(1/2)*pi/3", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b3", "at": "(1/2)*pi/3", "entry": None,
                "message": "(1/2)*pi/3 is unreduced literal arithmetic"},
        "evaluated": "pi/6",
        "why": "b3 (iv): the numerator literal 1/2 beside the denominator "
               "literal 3 is not an integer literal.",
    },
    {
        "id": "e27_unit_factor", "added": True,
        "goal": "1*pi == ?A", "setup": [],
        "move": ("close", {"value": "1*pi", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b3", "at": "1*pi", "entry": None,
                "message": "1*pi is unreduced literal arithmetic"},
        "evaluated": "pi",
        "why": "b3 (ii): 1 is not the only numerator factor.",
    },
    {
        "id": "e27_like_factors", "added": True,
        "goal": "pi*pi == ?A", "setup": [],
        "move": ("close", {"value": "pi*pi", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b3", "at": "pi*pi", "entry": None,
                "message": "pi*pi is unreduced literal arithmetic"},
        "evaluated": "pi^2",
        "why": "b3 (v): two factors on one side with one base, so ring "
               "would add their exponents 1 + 1.",
    },
    {
        "id": "e27_power_one", "added": True,
        "goal": "pi^1 == ?A", "setup": [],
        "move": ("close", {"value": "pi^1", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b4", "at": "pi^1", "entry": None,
                "message": "pi^1 is unreduced literal arithmetic"},
        "evaluated": "pi",
        "why": "b4: exponent 1.",
    },
    {
        "id": "e27_power_of_power", "added": True,
        "goal": "(pi^2)^3 == ?A", "setup": [],
        "move": ("close", {"value": "(pi^2)^3", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b4", "at": "(pi^2)^3", "entry": None,
                "message": "(pi^2)^3 is unreduced literal arithmetic"},
        "evaluated": "pi^6",
        "why": "b4: a Pow whose base is a Pow; the exponents multiply.",
    },
    {
        "id": "e27_double_negation", "added": True,
        "goal": "-(-pi) == ?A", "setup": [],
        "move": ("close", {"value": "-(-pi)", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b4", "at": "-(-pi)", "entry": None,
                "message": "-(-pi) is unreduced literal arithmetic"},
        "evaluated": "pi",
        "why": "b4: a Neg over a Neg. b2 passes first (the maximal sum "
               "has the one summand pi).",
    },
    # Its expected clause changes to (a) at cos 0, naming cos_zero, when
    # cos_zero is pinned: DISCHARGE_E27_CHANGES, E35.
    {
        "id": "e27_goal_lhs_before_close", "added": True,
        "goal": P1_1_GOAL, "state": ("P1.1", "s5"),
        "move": ("close", {"value": "2*1 - 2*(pi/2)*0 - (2*0 - 2*0*cos 0)",
                           "check": "ring", "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b2",
                "at": "2*1 - 2*(pi/2)*0 - (2*0 - 2*0*cos 0)", "entry": None,
                "message": "2*1 - 2*(pi/2)*0 - (2*0 - 2*0*cos 0) is "
                           "unreduced literal arithmetic"},
        "evaluated": "2",
        "why": "P1.1's own route after its last rewrite: the goal's left "
               "side as the value. No entry in force applies (cos 0 has "
               "none since §11.1 rev 9 dropped cos_zero), so (a) finds "
               "nothing, and b2 fires at the root, where 2*(pi/2)*0 is a "
               "zero summand. The reference close writes 2.",
    },
    # Review fix (user decision 2026-09-24, evaluated answers): b2's
    # monomial count (D2), sqrt_sq_val's |n| >= 2 (D3), and two branches no
    # case reached (sqrt_sq_val at n = 3, b4 at n = 0).
    {
        "id": "e27_sum_merges_after_normalising", "added": True,
        "goal": "2*(pi + 1) - 2 == ?A", "setup": [],
        "move": ("close", {"value": "2*(pi + 1) - 2", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b2", "at": "2*(pi + 1) - 2", "entry": None,
                "message": "2*(pi + 1) - 2 is unreduced literal arithmetic"},
        "evaluated": "2*pi",
        "why": "b2's count: the summands normalise to 2*pi + 2 and -2, "
               "three monomials, and the sum to 2*pi, one. Neither summand "
               "is a rational multiple of the other, so the old test "
               "accepted it.",
    },
    {
        "id": "e27_sum_merges_constant_over_two", "added": True,
        "goal": "(e_const + 1)/2 - 1/2 == ?A", "setup": [],
        "move": ("close", {"value": "(e_const + 1)/2 - 1/2",
                           "check": "ring", "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b2", "at": "(e_const + 1)/2 - 1/2",
                "entry": None,
                "message": "(e_const + 1)/2 - 1/2 is unreduced literal "
                           "arithmetic"},
        "evaluated": "e_const/2",
        "why": "b2's count: 2 + 1 monomials against 1. Contrast "
               "(e_const - 1)/2, one product, accepted.",
    },
    {
        "id": "e27_sum_merges_atom_term", "added": True,
        "goal": "2*(pi + 1) - 2*pi == ?A", "setup": [],
        "move": ("close", {"value": "2*(pi + 1) - 2*pi", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b2", "at": "2*(pi + 1) - 2*pi", "entry": None,
                "message": "2*(pi + 1) - 2*pi is unreduced literal "
                           "arithmetic"},
        "evaluated": "2",
        "why": "b2's count: 2 + 1 monomials against 1 (the pi terms "
               "cancel).",
    },
    {
        "id": "e27_sum_merges_halves", "added": True,
        "goal": "(pi + 1)/2 - pi/2 == ?A", "setup": [],
        "move": ("close", {"value": "(pi + 1)/2 - pi/2", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b2", "at": "(pi + 1)/2 - pi/2", "entry": None,
                "message": "(pi + 1)/2 - pi/2 is unreduced literal "
                           "arithmetic"},
        "evaluated": "1/2",
        "why": "b2's count: 2 + 1 monomials against 1.",
    },
    {
        "id": "e27_sum_merges_constant_cancels", "added": True,
        "goal": "2*(e_const - 1) - 2*e_const == ?A", "setup": [],
        "move": ("close", {"value": "2*(e_const - 1) - 2*e_const",
                           "check": "ring", "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b2", "at": "2*(e_const - 1) - 2*e_const",
                "entry": None,
                "message": "2*(e_const - 1) - 2*e_const is unreduced "
                           "literal arithmetic"},
        "evaluated": "-2",
        "why": "b2's count: 2 + 1 monomials against 1 (the e_const terms "
               "cancel).",
    },
    {
        "id": "e27_sum_merges_power", "added": True,
        "goal": "(pi + 1)^2 - 1 == ?A", "setup": [],
        "move": ("close", {"value": "(pi + 1)^2 - 1", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b2", "at": "(pi + 1)^2 - 1", "entry": None,
                "message": "(pi + 1)^2 - 1 is unreduced literal arithmetic"},
        "evaluated": "pi^2 + 2*pi",
        "why": "b2's count through a power: (pi + 1)^2 normalises to "
               "pi^2 + 2*pi + 1, so 3 + 1 monomials against 2. (b) still "
               "never expands a power for its own sake: (pi + 1)^2 alone, "
               "or (2*pi)^2, passes.",
    },
    {
        "id": "e27_sqrt_sq_val_negative_power", "added": True,
        "goal": "(sqrt 2)^(-2) == ?A", "setup": [],
        "move": ("close", {"value": "(sqrt 2)^(-2)", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "(sqrt 2)^(-2)",
                "entry": "sqrt_sq_val",
                "message": "(sqrt 2)^(-2) can still be evaluated "
                           "(sqrt_sq_val)"},
        "evaluated": "1/2",
        "why": "(a2) with |n| >= 2: field with sqrt_sq_val 2 lowers the "
               "power to 1/2. The value owes sqrt 2 # 0 (E6) and 2 >= 0 "
               "(E26), and ring proves the refl.",
    },
    {
        "id": "e27_sqrt_sq_val_negative_power_3", "added": True,
        "goal": "(sqrt 3)^(-2) == ?A", "setup": [],
        "move": ("close", {"value": "(sqrt 3)^(-2)", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "(sqrt 3)^(-2)",
                "entry": "sqrt_sq_val",
                "message": "(sqrt 3)^(-2) can still be evaluated "
                           "(sqrt_sq_val)"},
        "evaluated": "1/3",
        "why": "as e27_sqrt_sq_val_negative_power, with P1.2's own "
               "fact sqrt_sq_val 3.",
    },
    {
        "id": "e27_sqrt_sq_val_cube", "added": True,
        "goal": "(sqrt 2)^3 == ?A", "setup": [],
        "move": ("close", {"value": "(sqrt 2)^3", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "a", "at": "(sqrt 2)^3", "entry": "sqrt_sq_val",
                "message": "(sqrt 2)^3 can still be evaluated "
                           "(sqrt_sq_val)"},
        "evaluated": "2*sqrt 2",
        "why": "(a2) at n = 3, where E1 step 3's tree case (n = 2 only) "
               "would not match; field's fact reduction does.",
    },
    {
        "id": "e27_power_zero", "added": True,
        "goal": "pi^0 == ?A", "setup": [],
        "move": ("close", {"value": "pi^0", "check": "ring",
                           "facts": []}),
        "refusal": "close-not-evaluated",
        "e27": {"clause": "b4", "at": "pi^0", "entry": None,
                "message": "pi^0 is unreduced literal arithmetic"},
        "evaluated": "1",
        "why": "b4: exponent 0 (e27_power_one covers 1).",
    },
    {
        "id": "e27_check_failed_wins", "added": True,
        "goal": "2 == ?A", "setup": [],
        "move": ("close", {"value": "1 + 1 + 1", "check": "ring",
                           "facts": []}),
        "refusal": "close-check-failed",
        "why": "the order (EVALUATED_RULE, Order in close): the value is "
               "wrong (3, not 2) and unevaluated (b1). The check runs "
               "before E27, so the refusal is close-check-failed with the "
               "residual 2 - (1 + 1 + 1), not close-not-evaluated. With E27 "
               "first the learner would be told to tidy a wrong answer.",
    },
]

# Added by user decision 2026-09-24 (evaluated answers): closes E27 must
# ACCEPT. Each is refl on a fresh goal `V == ?A` with value V: the check
# passes, every earlier refusal passes, and the step is accepted with goal
# None and theorem `V == V` (asserted as a tree). The verdict is not asserted,
# since some values owe admissions (sqrt(y^2)'s y^2 >= 0, pi/pi's pi # 0)
# that are no part of E27. The current reference answers are also accepted
# in their own runs, unchanged (PROOFS, and problems/stage0's S1-S3):
# E27 changes no expected verdict there. 'kind' is 'answer' for a current
# reference answer, 'accept' for one E27 is meant to accept, and
# 'limitation' for an unevaluated value E27 accepts by design
# (EVALUATED_RULE, Known limitations), with 'evaluated' the form it does
# not demand.
EVALUATED_ACCEPTS = [
    {"id": "e27_answer_P1_1", "kind": "answer", "value": "2"},
    {"id": "e27_answer_P1_2", "kind": "answer", "value": P1_2_ANSWER},
    {"id": "e27_answer_P1_2_alt", "kind": "answer",
     "value": P1_2_ANSWER_ALT},
    {"id": "e27_answer_S2", "kind": "answer", "value": "(e_const - 1)/2"},
    {"id": "e27_answer_S3", "kind": "answer", "value": "1/2"},
    {"id": "e27_negative_fraction", "kind": "accept", "value": "-1/2"},
    {"id": "e27_negated_fraction", "kind": "accept", "value": "-(1/2)"},
    {"id": "e27_power_over_literal", "kind": "accept", "value": "pi^2/4"},
    {"id": "e27_surd", "kind": "accept", "value": "sqrt 2"},
    {"id": "e27_variable_coefficient", "kind": "accept", "value": "2*x"},
    {"id": "e27_S2_expanded", "kind": "accept", "value": "e_const/2 - 1/2"},
    {"id": "e27_split_fraction_lowest", "kind": "accept",
     "value": "2*pi/(3*sqrt 3)"},
    {"id": "e27_reciprocal", "kind": "accept", "value": "1/sqrt 3"},
    {"id": "e27_atan_positive", "kind": "accept", "value": "atan 2"},
    {"id": "e27_atan_odd_result", "kind": "accept", "value": "-atan 1"},
    {"id": "e27_negated_quotient", "kind": "accept", "value": "-(pi/6)"},
    # Review fix: the contrast for b2's monomial count, whose summands
    # share the atom exp(x) but no monomial.
    {"id": "e27_distinct_monomials", "kind": "accept",
     "value": "x*exp(x) - exp(x)"},
    {"id": "e27_log_sum", "kind": "limitation", "value": "ln 2 + ln 3",
     "evaluated": "ln 6",
     "why": "matches no entry's left side and is ring-irreducible (ln 2 "
            "and ln 3 are distinct atoms). ln 6 needs log_mul, not in "
            "force. Accepted under (a) and (b): a known limitation, not a "
            "bug."},
    {"id": "e27_surd_not_simplified", "kind": "limitation",
     "value": "sqrt 8", "evaluated": "2*sqrt 2",
     "why": "8 is not a rational square, and no sqrt product law is in "
            "force."},
    # Moves to the refused cases (BAD_MOVES e27_cos_zero) when cos_zero is
    # pinned: DISCHARGE_E27_CHANGES, E35 (discharge spec 2026-09-24, owner
    # answers). Asserted as accepted until then, since E27 reads ENTRIES.
    {"id": "e27_no_entry_in_force", "kind": "limitation", "value": "cos 0",
     "evaluated": "1",
     "why": "no cos_zero in ENTRIES: 'evaluated' is relative to the entries "
            "in force."},
    {"id": "e27_open_square", "kind": "limitation", "value": "sqrt(y^2)",
     "evaluated": "abs y",
     "why": "(a2): y is free, so neither sign of the root need satisfy "
            "u >= 0, and no abs entry is in force."},
    {"id": "e27_cancel_is_field", "kind": "limitation", "value": "pi/pi",
     "evaluated": "1",
     "why": "b3 compares factors on one side only; cancelling across the "
            "division is field's and owes pi # 0 (E3)."},
    {"id": "e27_power_of_sum", "kind": "limitation",
     "value": "(1 + sqrt 3)^2", "evaluated": "4 + 2*sqrt 3",
     "why": "(b) never expands a power; sqrt_sq_val (a2) counts only at "
            "Pow(sqrt b, n)."},
    {"id": "e27_factored_power", "kind": "limitation",
     "value": "(2*pi)^2", "evaluated": "4*pi^2",
     "why": "factored forms pass, which is what lets (e_const - 1)/2 "
            "pass."},
    {"id": "e27_alike_through_fact", "kind": "limitation",
     "value": "pi/(3*sqrt 3) + pi*sqrt 3 / 9",
     "evaluated": "2*pi*sqrt 3 / 9",
     "why": "the summands normalise to pi*inv(3*sqrt 3) and "
            "(1/9)*pi*sqrt 3, not rational multiples in ring; they are "
            "alike only through sqrt_sq_val."},
    {"id": "e27_atan_mixed_sign", "kind": "limitation",
     "value": "atan(1 - pi)", "evaluated": "-atan(pi - 1)",
     "why": "(a2): atan_odd counts only when every coefficient is "
            "negative."},
    {"id": "e27_product_through_neg", "kind": "limitation",
     "value": "-(2*pi)*3", "evaluated": "-6*pi",
     "why": "product flattening stops at a Neg that is not a rational "
            "literal, so 2 and 3 are in different products. -2*pi*3, the "
            "way D9 parses the usual spelling, is refused by b3 (iii)."},
    # Review fix: two branches no case reached.
    {"id": "e27_atan_zero", "kind": "limitation", "value": "atan 0",
     "evaluated": "0",
     "why": "no atan_zero in ENTRIES, and atan_odd needs a nonzero "
            "argument: the zero polynomial's coefficients are vacuously "
            "all negative, so without that clause atan 0 would be refused "
            "naming a move that changes nothing."},
    {"id": "e27_negative_power_other_side", "kind": "limitation",
     "value": "pi*pi^(-1)", "evaluated": "1",
     "why": "pi^(-1) counts on the denominator side (b3), so the two pi "
            "factors are on opposite sides and not compared, as in pi/pi."},
]
for _c in EVALUATED_ACCEPTS:  # the refl shape the header describes
    _c["goal"] = _c["value"] + " == ?A"
    _c["move"] = ("close", {"value": _c["value"], "check": "ring",
                            "facts": []})
    _c["theorem"] = _c["value"] + " == " + _c["value"]
del _c

# Handle forgeries (§15.3, §17's bank). The script implements each one.
# E21: every fact-slot forgery (a case passed at FORGERY_STATE, below) must
# fail in one of two ways. (i) Forging raises: an exception while the forged
# object is being built, before step() is called. This is accepted only
# where the case's 'accept' lists "raise_at_forge". (ii) step() returns the
# case's refusal code, written "refusal:<code>" in 'accept'. For every case,
# fact-slot or not, an exception escaping step() is never a pass: it is a
# crash, not a refusal (WHAT.md Done-when item 5: "are refused").
# Amendment to E21 (§15.3, WHAT.md Done-when item 5): three cases are not
# passed at the slot (direct_tracker_write, print_proved_with_admissions,
# json_roundtrip_state). Each carries its own 'accept', whose outcome names
# it defines, and its own 'post'. The script checks 'post' whichever
# accepted outcome occurred, and any outcome not in 'accept' fails the case.
# In every case the verdict and the tracker are unchanged. They are listed
# by name because they are code, not data. The handle model they test is
# E17 (module docstring).
#
# The discriminating slot. Every fact forgery is passed at the same place:
# the state after P1.2 s8, with P1.2-alt's close, whose only need for a fact
# is sqrt_sq_val 3. There, the three possible outcomes are told apart:
#   accepted  the goal closes (the forgery worked: a failure of the case);
#   ignored   close-check-failed with W4's residual
#             pi*(3 - (sqrt 3)^2)/(9*sqrt 3) (the kernel dropped the fact
#             silently: also a failure of the case);
#   refused   the case's refusal code (the only pass at the slot);
#   raised    step() raised instead of returning a refusal: a failure of the
#             case.
FORGERY_STATE = ("P1.2", "s8")
FORGERY_MOVE = ("close", {"value": P1_2_ANSWER_ALT, "check": "field",
                          "facts": ["FORGED"]})  # "FORGED" is replaced by
                                                 # the forged object
# After every forgery the script asserts two things. First, the state's
# obligation list still equals TRACKER_AT_FORGERY_STATE, which is P1.2's
# final tracker without the two keys s9 mints (3*sqrt 3 # 0, and 2 > 0 from
# the value's ln 2, E26, are s9's only new keys). Second, the same close with
# the genuine h_sqrt3 then succeeds and the report is VERDICTS["P1.2-alt"]
# ('Proved modulo 13 admissions'). No forgery mutates h_sqrt3. A forgery that
# needs a real handle to alter mints its own, as fabricated_handle_id (a)
# does.
TRACKER_AT_FORGERY_STATE = [ob for ob in FINAL_TRACKER["P1.2"]
                            if ob[0] not in ("3*sqrt 3 # 0", "2 > 0")]

FORGERIES = [
    {"id": "construct_theorem_directly",
     "does": "instantiate the kernel's internal theorem or judgement class by "
             "any route, private names included, with conclusion "
             "(sqrt 3)^2 == 3, and pass it at the slot",
     # Either outcome passes. No public constructor may exist, and §15.3
     # says Python cannot guarantee that no private route does. What it can
     # guarantee is that no such object is the one the kernel minted.
     "accept": ("raise_at_forge", "refusal:fact-not-minted-handle")},
    {"id": "object_new_theorem",
     "does": "object.__new__ on the handle class, fill its fields with "
             "h_sqrt3's (id included), pass it at the slot",
     # filling the fields may raise if the class uses __slots__ or is frozen
     "accept": ("raise_at_forge", "refusal:fact-not-minted-handle")},
    {"id": "copy_handle",
     "does": "copy.copy(h_sqrt3) and copy.deepcopy(h_sqrt3), each passed at "
             "the slot",
     # both; E17 guarantees copy and deepcopy succeed, so only the refusal
     # passes
     "accept": ("refusal:fact-not-minted-handle",),
     "then": "the same close with the original h_sqrt3 succeeds"},
    {"id": "pickle_roundtrip_handle",
     "does": "pickle.loads(pickle.dumps(h_sqrt3)) passed at the slot",
     # E17: the lineage is a picklable token and the class is at module
     # level, so the round trip succeeds and the identity check refuses it
     "accept": ("refusal:fact-not-minted-handle",)},
    {"id": "fabricated_handle_id",
     "does": "three forgeries. (a) From FORGERY_STATE, run a second real "
             "step `fact sqrt_sq_val 3` and bind it 'h_victim'. By E10 this "
             "step emits nothing, so the new state's obligations still "
             "equal TRACKER_AT_FORGERY_STATE. Change h_victim's id (through "
             "object.__setattr__ if need be) to h_victim.id + 1, an id no "
             "`fact` step in this run has minted, and pass it at the slot "
             "from that post-fact state. Under E17 the refusal does not "
             "depend on whether that id is in the map. (b) Pass that same "
             "id as a bare int at the slot. (c) Pass h_sqrt3.id as a bare "
             "int at the slot: a genuine id from the same lineage. Reading "
             "the id does not change h_sqrt3, so the post-check above still "
             "holds with the genuine handle",
     # (a) catches a kernel that trusts the handle's own fields without a
     # registry lookup. (b) catches one that accepts any int. (c) is the
     # only case that catches a kernel that resolves ints through its
     # registry before the identity check; (a), (b), copy_handle and
     # pickle_roundtrip_handle all miss it. E17 does not promise sequential
     # ids, so no case assumes them. All three keep the refusal
     # fact-not-minted-handle (E17: an altered id, and a bare int).
     "accept": ("refusal:fact-not-minted-handle",)},
    {"id": "direct_tracker_write",
     "state": ("P1.1", "s6"),  # finished P1.1, N = 6
     "does": "public API only: take the object returned by the state's "
             "public obligations or tracker accessor, delete the admission "
             "t >= 0 @ [0, pi/2] from it, and mark 0 <= pi/2 discharged",
     # raise_at_mutation: the delete or the mark-discharged operation on the
     #   accessor's returned object raises. That raise is outside step() and
     #   is a pass.
     # no_effect: both operations complete, and 'post' holds.
     "accept": ("raise_at_mutation", "no_effect"),
     "post": "the accessor again returns FINAL_TRACKER['P1.1'], and the "
             "report is VERDICTS['P1.1'] ('Proved modulo 6 admissions')",
     "expect": "Mutation through private attributes is out of scope: §15.3 "
               "says Python cannot prevent it"},
    # The honest report of each proof is asserted through VERDICTS (§5.4,
    # §15.6). This case covers only the forgery: §15.3's "there is no result
    # object to build by mistake", and §17's "a tactic that attempts to
    # manufacture a proved result".
    {"id": "print_proved_with_admissions",
     "state": ("P1.1", "s6"),
     "does": "on a finished P1.1 state (N = 6), try to obtain 'Proved.' "
             "through every public report path: (a) construct whatever the "
             "report or verdict is, or its class, from outside the kernel, "
             "directly and via object.__new__, with n = 0 or a 'Proved.' "
             "string, then pass it to the printer or report function; (b) "
             "call the report function with any caller-supplied count or "
             "status argument set to 0 or 'Proved.', if such a parameter "
             "exists; (c) ask for the report again after the "
             "direct_tracker_write attempt; (d) have a script-side 'tactic' "
             "return a result object claiming the goal closed, without a "
             "kernel step, then ask for the report",
     # For each sub-attempt (a)-(d), one of:
     #   raise_at_forge     building the verdict object, or calling
     #                      object.__new__ on its class, raises;
     #   raise_at_call      the printer or report function raises TypeError
     #                      or ValueError on a foreign object or an extra
     #                      argument;
     #   refused            the kernel returns a refusal;
     #   no_such_parameter  (b) only: the report function has no count or
     #                      status parameter to set.
     #   honest_report      (c) only: the direct_tracker_write attempt ends
     #                      in one of that case's accepted outcomes, and
     #                      report(state) then returns VERDICTS['P1.1'].
     # For (c) and (d), an exception escaping step() is a crash, as in E21.
     "accept": ("raise_at_forge", "raise_at_call", "refused",
                "no_such_parameter", "honest_report"),
     "post": "every report string the kernel produces for the state equals "
             "VERDICTS['P1.1'], and 'Proved.' is not a substring of any "
             "captured stdout or report output",
     "expect": "the case fails if any public report function accepts a "
               "caller-supplied count or status and uses it, or if the "
               "caller can build a verdict object the printer accepts "
               "(§15.3: 'there is no result object to build by mistake'; "
               "§15.6: admit never yields Proved)"},
    # Added: the other two cases §15.3 names for §17's bank.
    {"id": "json_roundtrip_state", "added": True,
     "state": FORGERY_STATE,
     "does": "serialise the proof state to JSON and load it back as a state",
     # dump_raises: json.dumps(state), or the kernel's own serialiser if it
     #   has one, raises TypeError.
     # no_loader: the kernel's public API (the names without a leading
     #   underscore that the kernel module and the state class export) has
     #   no function that returns a proof state when given a str, bytes or
     #   dict. The script checks this against the names the kernel
     #   documents, not by scanning every name.
     # loaded_holds_no_theorem: a loader exists, and the loaded state's
     #   report is never 'Proved.', and never VERDICTS['P1.2'] without the
     #   steps being replayed. Every handle-like object taken from it is
     #   refused at FORGERY_STATE with fact-not-minted-handle or
     #   fact-foreign-state-handle.
     "accept": ("dump_raises", "no_loader", "loaded_holds_no_theorem"),
     "post": "the original run's tracker still equals "
             "TRACKER_AT_FORGERY_STATE",
     "expect": "§15.3: nothing reconstructs a judgement from storage"},
    {"id": "foreign_state_handle", "added": True,
     "does": "mint h_sqrt3 in a second, fresh P1.2 run (its own s1) and pass "
             "that handle at the slot of the first run",
     "accept": ("refusal:fact-foreign-state-handle",)},
]

# Planted bugs (Done-when item 3). What each changes against the lists above,
# so the script can check that its own assertions would catch it.
#
# The script runs every proof in PROOFS under each mutation and collects all
# mismatches rather than stopping at the first. It requires that each
# location in the bug's 'caught_by' appears among them, and it treats any
# exception other than the suite's own mismatch type as a failure of the
# planted-bug test, not as a catch. 'admissions' gives N for every proof
# under the bug. 'caught_by' entries have these shapes:
#   (proof, step, prop, dom)   the expected key (prop, dom) of that step's
#                              list is absent from what the kernel emitted;
#   (proof, step, prop, "new") the key is present but its `new` flag
#                              differs;
#   (proof, step, prop, "tag") the key is present but its tag differs from
#                              the expected one;
#   ("FINAL_TRACKER", proof, (prop, dom))  the key is absent from the final
#                              tracker;
#   ("N", proof)               the admission count differs from ADMISSIONS.
PLANTED_BUGS = {
    "d_ln_emits_nothing": {
        "mutation": "d_ln returns its derivative and emits no side "
                    "condition; field's 1 + x # 0 and x^2 - x + 1 # 0 are "
                    "unaffected, and so are F's own ln formers on [0, 1] "
                    "(E26), which are different keys (E8) and do not mask "
                    "the missing (0, 1) ones",
        "missing": {"P1.2": ["1 + x > 0 @ (0, 1)", "x^2 - x + 1 > 0 @ (0, 1)"],
                    "P1.2-alt": ["1 + x > 0 @ (0, 1)",
                                 "x^2 - x + 1 > 0 @ (0, 1)"]},
        "admissions": {"P1.1": 6, "P1.1-fallback": 9, "P1.2": 12,
                       "P1.2-alt": 11},
        "caught_by": [("P1.2", "s2", "1 + x > 0", "(0, 1)"),
                      ("P1.2", "s2", "x^2 - x + 1 > 0", "(0, 1)"),
                      ("P1.2-alt", "s2", "1 + x > 0", "(0, 1)"),
                      ("P1.2-alt", "s2", "x^2 - x + 1 > 0", "(0, 1)")],
        "note": "P1.1 and its fallback have no ln and do not see it",
    },
    "ftc_derivative_premise_on_closed": {
        # WHAT.md Done-when 3 says only that the derivative premise moves to
        # the closed interval. The counts below depend on this reading, in
        # which deriv and check run at the premise's domain. If only the
        # premise's own domain moved, P1.2 would stay at 14.
        "mutation": "ftc attaches the derivative premise D[x] F == f to "
                    "[a, b], and deriv, field and check run at that domain, "
                    "so every obligation they emit is on [a, b]. In P1.2 "
                    "field's 1 + x^3 # 0 then merges with the goal's former "
                    "on [0, 1], and d_ln's 1 + x > 0 and x^2 - x + 1 > 0 "
                    "merge with F's ln formers there (E26): three merges. "
                    "In the fallback d_sqrt's x > 0 moves to [0, pi^2/4] "
                    "beside sqrt's x >= 0 there, a different key",
        "affects": ("P1.1", "P1.1-fallback", "P1.2", "P1.2-alt"),
        "admissions": {"P1.1": 6, "P1.1-fallback": 9, "P1.2": 11,
                       "P1.2-alt": 10},
        # Under this bug the fallback's x > 0 and 2*sqrt x # 0 on
        # [0, pi^2/4] are false at 0, and E24 would tag both none (for
        # x > 0 the set {x <= 0, 0 <= x} is feasible at x = 0; sqrt_pos's
        # hypothesis x > 0 @ [0, pi^2/4] is itself none). That is why their
        # tags are not asserted: the no-none assertion does not cover
        # planted-bug runs, and these keys are not in the expected lists.
        # Only the domain mismatch is asserted.
        "caught_by": [
            ("P1.1", "s2", "D[t](2*sin t - 2*t*cos t) == sin t * (2*t)",
             "(0, pi/2)"),
            ("P1.1-fallback", "s1",
             "D[x](2*sin(sqrt x) - 2*sqrt x * cos(sqrt x)) == sin(sqrt x)",
             "(0, pi^2/4)"),
            ("P1.1-fallback", "s1", "x > 0", "(0, pi^2/4)"),
            ("P1.1-fallback", "s1", "2*sqrt x # 0", "(0, pi^2/4)"),
            ("P1.2", "s2", "D[x](" + P1_2_F + ") == 1/(1 + x^3)", "(0, 1)"),
            ("P1.2-alt", "s2", "D[x](" + P1_2_F + ") == 1/(1 + x^3)",
             "(0, 1)"),
        ],
    },
    # WHAT.md Done-when item 3 says only "dropping one obligation". The
    # mutation is named by key, never as "the first new admitted key",
    # because order inside a step is unspecified (steps are compared as
    # sets, KEYING). Each key below is an admission that, in every proof
    # that emits it, is minted once (new = True) and never re-emitted
    # (checked against EXPECTED_OBLIGATIONS), so N drops by exactly one in
    # each such proof. Dropping a discharged key would leave N unchanged, and
    # a re-emitted key could be re-added by the later emission; that case is
    # the second variant below.
    "tracker_drops_one": {
        "mutation": "Tracker.add silently discards any emission whose key "
                    "is one of `drop_keys`, in every proof run",
        # A flat tuple of keys, not keyed by proof: the mutation is
        # proof-agnostic, and every proof's tracker discards any emission
        # whose (predicate, domain) key is here. P1.2-alt shares P1.2's
        # goal-creation key and loses it too. P1.1-fallback emits neither
        # key, so its N stays 9; neither proof family emits the other's key.
        # E26 adds no second emission of either: P1.1's installation owes
        # t^2 >= 0, not t >= 0, and F's formers in P1.2 hold no 1 + x^3.
        "drop_keys": (
            ("t >= 0", "[0, pi/2]"),     # P1.1: emitted at s1 only
            # P1.2 and P1.2-alt (shared s1-s8): emitted at goal creation
            # only. field's (0, 1) key in s2 is a different key (E8), and
            # P1.2-alt's s9 does not emit it.
            ("1 + x^3 # 0", "[0, 1]"),
        ),
        "missing_from_final_tracker": {
            "P1.1": [("t >= 0", "[0, pi/2]")],
            "P1.2": [("1 + x^3 # 0", "[0, 1]")],
            "P1.2-alt": [("1 + x^3 # 0", "[0, 1]")],
        },
        "admissions": {"P1.1": 5, "P1.1-fallback": 9, "P1.2": 13,
                       "P1.2-alt": 12},
        # FINAL_TRACKER (key absent) and ADMISSIONS/VERDICTS (N one lower)
        "caught_by": [("FINAL_TRACKER", "P1.1", ("t >= 0", "[0, pi/2]")),
                      ("FINAL_TRACKER", "P1.2", ("1 + x^3 # 0", "[0, 1]")),
                      ("FINAL_TRACKER", "P1.2-alt",
                       ("1 + x^3 # 0", "[0, 1]")),
                      ("N", "P1.1"), ("N", "P1.2"), ("N", "P1.2-alt")],
        # The per-step emission lists are unchanged by this bug. They report
        # what the rules emitted, and this mutation changes nothing a rule
        # emitted; `new` is read from the tracker before the step, and the
        # key was absent then either way. So the step lists do not catch it;
        # the tracker-side assertions do.
        "step_lists_changed": False,
    },
    "tracker_drops_reemitted": {
        "mutation": "Tracker.add discards ('0 <= pi/2', 'true') only the "
                    "first time it is inserted, when P1.1's goal is "
                    "installed (sqrt's former in the integrand uses the "
                    "range, so the orientation is owed there, E26)",
        # s1 re-emits it, so FINAL_TRACKER and N are unchanged. The key is
        # P1.1's only, so the other proofs are unaffected.
        "admissions": {"P1.1": 6, "P1.1-fallback": 9, "P1.2": 14,
                       "P1.2-alt": 13},
        # P1.1 s1: the `new` flag of 0 <= pi/2 is True, expected False
        "caught_by": [("P1.1", "s1", "0 <= pi/2", "new")],
        # This shows the `new` flag is itself an assertion that does work.
        # It depends on the script reading `new` from the tracker's state
        # before each step, not from the rule.
    },
    # E24's tag check does work: the revision 9 gap, planted in the tagger.
    "pi_pos_not_in_constraint_set": {
        "mutation": "the tagger's Fourier–Motzkin set omits the named "
                    "constants' sign facts (pi_pos, e_gt_one); everything "
                    "else in E24 is unchanged",
        # Without pi > 0 the set {pi/2 < 0} is feasible, pi/2 is no
        # sign-certificate form, sign product does not close >= or <=, and
        # cite's pi > 0 does not syntactically give pi/2 >= 0 (E24). So
        # those two keys become ('none', ()). Unaffected: t >= 0 @ [0, pi/2]
        # stays T_RANGE, because dom's own lower end 0 <= t closes it with no
        # sign fact; x > 0 @ (0, pi^2/4) and x >= 0 @ [0, pi^2/4] stay
        # T_RANGE the same way; 0 <= pi^2/4, pi^2/4 >= 0 and t^2 >= 0 @
        # [0, pi/2] stay T_SIGN, since method 4 uses no sign fact (E20);
        # P1.2 has no pi.
        "retagged": {
            "P1.1": [("0 <= pi/2", "true", T_NONE)],
            "P1.1-fallback": [("pi/2 >= 0", "true", T_NONE)],
        },
        # A tag change moves no obligation and no status, so N is unchanged.
        "admissions": {"P1.1": 6, "P1.1-fallback": 9, "P1.2": 14,
                       "P1.2-alt": 13},
        # 0 <= pi/2 is emitted three times in P1.1: at installation (E26),
        # at s1 and at s2
        "caught_by": [("P1.1", "goal", "0 <= pi/2", "tag"),
                      ("P1.1", "s1", "0 <= pi/2", "tag"),
                      ("P1.1", "s2", "0 <= pi/2", "tag"),
                      ("P1.1-fallback", "s2", "pi/2 >= 0", "tag")],
        # So the tag assertion, and with it the no-none check WHAT.md
        # relies on, is not empty: a tagger that drops the rev 9 sign facts
        # is caught.
    },
}

# ---------------------------------------------------------------------------
# 8b. Definedness (E26, user decision 2026-09-24)
#
# The goals that install and close, beside BAD_MOVES' E26 refusals. Each is
# installed fresh and closed with `move`. `goal_emits` is the installation's
# list and `emits` the close's, in EXPECTED_OBLIGATIONS' shape, with new
# read against the tracker before the step. `final` is the tracker at the
# end, in FINAL_TRACKER's shape, `report` is report(state) exactly, and
# `theorem` is the reported theorem. `was` is what the kernel reported
# before E26, for the record; it is not asserted.
#
# The first four are the point: an undefined or maybe-undefined term that
# ring cancels now leaves its domain behind as a visible admission. The two
# false ones are tagged none, and are outside the no-none assertion, which
# covers PROOFS runs only. ln_false_on_goal_domain, contrasted with
# ln_true_by_hyp, is its positive test for definedness, as OCCURRENCE_CASE's
# t >= 0 @ [-1, 0] is for a rewrite hypothesis. tan_pi_half pins only that
# tan is charged, since E24 tags cos u # 0 none whenever Γ does not state
# it; tan_zero_true records
# that limitation as a pinned fact, a true condition tagged none. The rest
# pin each closed end, where the builtin is defined, as discharged by
# norm_num, and atanh's interior, so that a former that is too strict, or
# that drops a bound, fails a case (DEFINEDNESS_MUTATIONS).
DEFINEDNESS_CASES = [
    {"id": "tan_pi_half",
     "goal": "tan(pi/2) - tan(pi/2) == ?A",
     # tan's domain at pi/2 is cos(pi/2) # 0. It is closed, so domain true
     # (E5), and not literal, so admitted. It is false (cos(pi/2) = 0), and
     # E24 tags it none: both senses of FM are feasible with cos(pi/2) an
     # opaque variable, even with pi_pos; it is no sign-certificate form;
     # sign product has no content (c = 1) and nothing of lower degree; and
     # no NAMED_ENTRIES entry concludes it (§6.8's cos_nonzero_on is not
     # pinned in this milestone, and cos_pi_half concludes cos(pi/2) == 0).
     # The same holds for every cos u # 0, true or false, when Γ is empty:
     # E24 then tags the tan former none (hyp would fire if the goal's domain
     # stated cos u # 0, or cos u > 0 or cos u < 0), so this case pins that
     # tan is charged, not that
     # the tagger tells a true condition from a false one (tan_zero_true is
     # the true contrast, tagged none as well).
     # The divisor 2 of pi/2 is charged once, as part of tan(pi/2) (KEYING).
     "goal_emits": [
         ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("cos(pi/2) # 0", "true", (S_FORMER,), ADMITTED, T_NONE, True)],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "emits": [],  # the value 0 has no former, and ring emits nothing
     "final": [("2 # 0", "true", DISCHARGED, T_NORM_NUM),
               ("cos(pi/2) # 0", "true", ADMITTED, T_NONE)],
     "report": VERDICT.format(n=1),
     "theorem": "tan(pi/2) - tan(pi/2) == 0",
     "was": PROVED},
    {"id": "tan_zero_true",
     "goal": "0*tan 0 == ?A",
     # the true contrast to tan_pi_half, and the record of its limitation.
     # tan 0 owes cos 0 # 0, closed, so domain true (E5), and not literal
     # (cos 0 is an atom), so admitted. It is TRUE (cos 0 = 1), and E24 still
     # tags it none, by the same trace as tan_pi_half: Γ is empty; FM's two
     # senses are feasible with cos 0 an opaque variable; cos 0 is no
     # sign-certificate form; its ring normal form is 1*cos 0, so sign
     # product has no content and nothing of lower degree; and no
     # NAMED_ENTRIES entry concludes cos 0 > 0 or cos 0 # 0. Until §6.8's
     # cos_nonzero_on is pinned, every tan former whose goal domain does not
     # state its condition is tagged none, true or false. So a PROOFS run
     # containing tan on such a goal cannot pass the no-none check.
     # A tagger that fitted this tag to the truth of the condition fails.
     "goal_emits": [
         ("cos 0 # 0", "true", (S_FORMER,), ADMITTED, T_NONE, True)],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "emits": [],
     "final": [("cos 0 # 0", "true", ADMITTED, T_NONE)],
     "report": VERDICT.format(n=1),
     "theorem": "0*tan 0 == 0",
     "was": PROVED},
    {"id": "ln_false_on_goal_domain",
     "goal": "ln x * 0 == ?A @ x < 0",
     # ln x owes x > 0 at the goal's own domain, which is Γ. False everywhere
     # on it. E24: hyp fails (x > 0 does not follow from x < 0), FM's
     # {x <= 0, x < 0} is feasible at x = -1, x is no certificate form, sign
     # product has neither content nor factors, and no entry concludes x > 0.
     "goal_emits": [
         ("x > 0", "x < 0", (S_FORMER,), ADMITTED, T_NONE, True)],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "emits": [],
     "final": [("x > 0", "x < 0", ADMITTED, T_NONE)],
     "report": VERDICT.format(n=1),
     "theorem": "ln x * 0 == 0 @ x < 0",
     "was": PROVED},
    {"id": "ln_true_by_hyp",
     "goal": "ln x * 0 == ?A @ x > 0",
     # the contrast: the same key on a domain that makes it true is tagged
     # hyp, the one E24 method P1 never reaches (every P1 goal's domain is
     # true). So none above comes from falsity, not from the case's shape.
     "goal_emits": [
         ("x > 0", "x > 0", (S_FORMER,), ADMITTED, T_HYP, True)],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "emits": [],
     "final": [("x > 0", "x > 0", ADMITTED, T_HYP)],
     "report": VERDICT.format(n=1),
     "theorem": "ln x * 0 == 0 @ x > 0",
     "was": PROVED},
    {"id": "sqrt_closed_end",
     "goal": "0*sqrt 0 == ?A",
     # sqrt is defined at 0: 0 >= 0, literal and true (E7). A former written
     # u > 0 would refuse this goal.
     "goal_emits": [
         ("0 >= 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True)],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "emits": [],
     "final": [("0 >= 0", "true", DISCHARGED, T_NORM_NUM)],
     "report": PROVED,
     "theorem": "0*sqrt 0 == 0",
     "was": PROVED},
    {"id": "asin_closed_ends",
     "goal": "0*(asin 1 + asin(-1)) == ?A",
     # asin is defined at both ends: four literal bounds, all true
     "goal_emits": [
         ("1 >= -1", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("1 <= 1", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("-1 >= -1", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("-1 <= 1", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True)],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "emits": [],
     "final": [("1 >= -1", "true", DISCHARGED, T_NORM_NUM),
               ("1 <= 1", "true", DISCHARGED, T_NORM_NUM),
               ("-1 >= -1", "true", DISCHARGED, T_NORM_NUM),
               ("-1 <= 1", "true", DISCHARGED, T_NORM_NUM)],
     "report": PROVED,
     "theorem": "0*(asin 1 + asin(-1)) == 0",
     "was": PROVED},
    {"id": "acos_closed_ends",
     "goal": "0*(acos 1 + acos(-1)) == ?A",
     # the same four keys as asin's: one table row each, the same domain
     "goal_emits": [
         ("1 >= -1", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("1 <= 1", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("-1 >= -1", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("-1 <= 1", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True)],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "emits": [],
     "final": [("1 >= -1", "true", DISCHARGED, T_NORM_NUM),
               ("1 <= 1", "true", DISCHARGED, T_NORM_NUM),
               ("-1 >= -1", "true", DISCHARGED, T_NORM_NUM),
               ("-1 <= 1", "true", DISCHARGED, T_NORM_NUM)],
     "report": PROVED,
     "theorem": "0*(acos 1 + acos(-1)) == 0",
     "was": PROVED},
    {"id": "acosh_closed_end",
     "goal": "0*acosh 1 == ?A",
     # acosh is defined at 1: 1 >= 1. A former written u > 1 would refuse it
     "goal_emits": [
         ("1 >= 1", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True)],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "emits": [],
     "final": [("1 >= 1", "true", DISCHARGED, T_NORM_NUM)],
     "report": PROVED,
     "theorem": "0*acosh 1 == 0",
     "was": PROVED},
    {"id": "atanh_interior",
     "goal": "0*atanh 0 == ?A",
     # atanh's two strict bounds at an interior point, both true. With
     # BAD_MOVES atanh_upper_end and atanh_lower_end this pins the exact
     # keys: a closed former would mint 0 >= -1 and 0 <= 1 instead.
     "goal_emits": [
         ("0 > -1", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("0 < 1", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True)],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "emits": [],
     "final": [("0 > -1", "true", DISCHARGED, T_NORM_NUM),
               ("0 < 1", "true", DISCHARGED, T_NORM_NUM)],
     "report": PROVED,
     "theorem": "0*atanh 0 == 0",
     "was": PROVED},
]

# What each part of E26 guards, as mutations the suite must catch (a
# data-review choice made to carry out E26 (a), the owner's decision of
# 2026-09-24: removing any single partial former must be caught).
# Each is a change to E26 (a)'s table, to its clause (b), or (the last
# three) to where E26 (a)'s formers are charged. 'caught_by' lists
# locations that must all show a failure under it, in PLANTED_BUGS' shapes
# (a refused proof step is (proof, step, "refused"), and a sources mismatch
# (proof, step, prop, "sources")), plus three shapes for cases:
# ("BAD_MOVES", id), ("DEFINEDNESS_CASES", id) and ("MATCH_ACCEPTS", id),
# each meaning that case fails, whether by a refusal that no longer happens
# or by a list, tracker or report that differs. 'admissions' is N for every
# proof in PROOFS under the mutation, given only where every PROOFS run still
# completes. Every location was traced by hand against the lists above. The
# script may plant each one in a child process, as it does PLANTED_BUGS, if
# ARCHITECTURE.md names a seam that holds E26's table (read at call time, as
# deriv.APP_RULES is); the seam is the architecture's to name, not this
# file's. The three position mutations change no table, so they are traced
# by hand only, unless the architecture names a seam for them too.
_P1_UNCHANGED = {"P1.1": 6, "P1.1-fallback": 9, "P1.2": 14, "P1.2-alt": 13}
DEFINEDNESS_MUTATIONS = {
    # one per builtin: its former charges nothing
    "no_ln_former": {
        "mutation": "ln u owes nothing",
        "caught_by": [("BAD_MOVES", "ln_negative_literal"),
                      ("BAD_MOVES", "ln_zero_literal"),
                      ("BAD_MOVES", "rewrite_R_owes_domain"),
                      ("BAD_MOVES", "close_value_owes_domain"),
                      ("DEFINEDNESS_CASES", "ln_false_on_goal_domain"),
                      ("DEFINEDNESS_CASES", "ln_true_by_hyp"),
                      ("MATCH_ACCEPTS", "ring_cancels_inv_atom"),
                      ("P1.2", "s2", "1 + x > 0", "[0, 1]"),
                      ("P1.2", "s2", "x^2 - x + 1 > 0", "[0, 1]"),
                      ("P1.2", "s2", "1 + 1 > 0", "true"),
                      ("P1.2", "s9", "2 > 0", "true"),
                      ("P1.2-alt", "s9", "2 > 0", "true"),
                      ("N", "P1.2"), ("N", "P1.2-alt")],
        "admissions": {"P1.1": 6, "P1.1-fallback": 9, "P1.2": 12,
                       "P1.2-alt": 11},
    },
    "no_sqrt_former": {
        "mutation": "sqrt u owes nothing",
        # Without t^2 >= 0 no key uses P1.1's range at installation, so its
        # orientation is first owed at s1 again; the fallback's likewise at
        # s1. P1.2's 3 >= 0 is still owed as h_sqrt3's hypothesis, but with
        # that source only, and s7 no longer owes it.
        "caught_by": [("BAD_MOVES", "sqrt_negative_literal"),
                      ("DEFINEDNESS_CASES", "sqrt_closed_end"),
                      ("MATCH_ACCEPTS", "rewrite_under_infinite_range"),
                      ("P1.1", "goal", "t^2 >= 0", "[0, pi/2]"),
                      ("P1.1", "goal", "0 <= pi/2", "true"),
                      ("P1.1", "s1", "0 <= pi/2", "new"),
                      ("P1.1-fallback", "goal", "x >= 0", "[0, pi^2/4]"),
                      ("P1.1-fallback", "goal", "0 <= pi^2/4", "true"),
                      ("P1.1-fallback", "s1", "0 <= pi^2/4", "new"),
                      ("P1.1-fallback", "s1", "pi^2/4 >= 0", "true"),
                      ("P1.1-fallback", "s1", "0 >= 0", "true"),
                      ("P1.1-fallback", "s3", "0 >= 0", "new"),
                      ("P1.2", "s2", "3 >= 0", "sources"),
                      ("P1.2", "s7", "3 >= 0", "true"),
                      ("N", "P1.1"), ("N", "P1.1-fallback")],
        "admissions": {"P1.1": 5, "P1.1-fallback": 7, "P1.2": 14,
                       "P1.2-alt": 13},
    },
    "no_tan_former": {
        "mutation": "tan u owes nothing",
        "caught_by": [("DEFINEDNESS_CASES", "tan_pi_half"),
                      ("DEFINEDNESS_CASES", "tan_zero_true")],
        "admissions": _P1_UNCHANGED,
    },
    "no_asin_former": {
        "mutation": "asin u owes nothing",
        "caught_by": [("BAD_MOVES", "asin_above_literal"),
                      ("BAD_MOVES", "asin_below_literal"),
                      ("DEFINEDNESS_CASES", "asin_closed_ends")],
        "admissions": _P1_UNCHANGED,
    },
    "no_acos_former": {
        "mutation": "acos u owes nothing",
        "caught_by": [("BAD_MOVES", "acos_above_literal"),
                      ("BAD_MOVES", "acos_below_literal"),
                      ("DEFINEDNESS_CASES", "acos_closed_ends")],
        "admissions": _P1_UNCHANGED,
    },
    "no_acosh_former": {
        "mutation": "acosh u owes nothing",
        "caught_by": [("BAD_MOVES", "acosh_below_literal"),
                      ("DEFINEDNESS_CASES", "acosh_closed_end")],
        "admissions": _P1_UNCHANGED,
    },
    "no_atanh_former": {
        "mutation": "atanh u owes nothing",
        "caught_by": [("BAD_MOVES", "atanh_upper_end"),
                      ("BAD_MOVES", "atanh_lower_end"),
                      ("DEFINEDNESS_CASES", "atanh_interior")],
        "admissions": _P1_UNCHANGED,
    },
    # one per bound of a two-sided domain: the former keeps one bound only
    "asin_no_upper_bound": {
        "mutation": "asin u owes u >= -1 only",
        "caught_by": [("BAD_MOVES", "asin_above_literal"),
                      ("DEFINEDNESS_CASES", "asin_closed_ends")],
        "admissions": _P1_UNCHANGED,
    },
    "asin_no_lower_bound": {
        "mutation": "asin u owes u <= 1 only",
        "caught_by": [("BAD_MOVES", "asin_below_literal"),
                      ("DEFINEDNESS_CASES", "asin_closed_ends")],
        "admissions": _P1_UNCHANGED,
    },
    "acos_no_upper_bound": {
        "mutation": "acos u owes u >= -1 only",
        "caught_by": [("BAD_MOVES", "acos_above_literal"),
                      ("DEFINEDNESS_CASES", "acos_closed_ends")],
        "admissions": _P1_UNCHANGED,
    },
    "acos_no_lower_bound": {
        "mutation": "acos u owes u <= 1 only",
        "caught_by": [("BAD_MOVES", "acos_below_literal"),
                      ("DEFINEDNESS_CASES", "acos_closed_ends")],
        "admissions": _P1_UNCHANGED,
    },
    "atanh_no_upper_bound": {
        "mutation": "atanh u owes u > -1 only",
        "caught_by": [("BAD_MOVES", "atanh_upper_end"),
                      ("DEFINEDNESS_CASES", "atanh_interior")],
        "admissions": _P1_UNCHANGED,
    },
    "atanh_no_lower_bound": {
        "mutation": "atanh u owes u < 1 only",
        "caught_by": [("BAD_MOVES", "atanh_lower_end"),
                      ("DEFINEDNESS_CASES", "atanh_interior")],
        "admissions": _P1_UNCHANGED,
    },
    # one per end whose closedness E26 decides: open and closed swapped
    "ln_closed_at_0": {
        "mutation": "ln u owes u >= 0",
        "caught_by": [("BAD_MOVES", "ln_zero_literal"),
                      ("DEFINEDNESS_CASES", "ln_false_on_goal_domain"),
                      ("P1.2", "s2", "1 + x > 0", "[0, 1]"),
                      ("P1.2", "s2", "x^2 - x + 1 > 0", "[0, 1]")],
        "admissions": _P1_UNCHANGED,  # the same count, other keys
    },
    "sqrt_open_at_0": {
        "mutation": "sqrt u owes u > 0",
        # the fallback's ftc goal holds sqrt 0, whose 0 > 0 is refuted
        "caught_by": [("DEFINEDNESS_CASES", "sqrt_closed_end"),
                      ("P1.1", "goal", "t^2 >= 0", "[0, pi/2]"),
                      ("P1.1-fallback", "s1", "refused")],
    },
    "asin_open": {
        "mutation": "asin u owes u > -1 and u < 1",
        "caught_by": [("DEFINEDNESS_CASES", "asin_closed_ends")],
        "admissions": _P1_UNCHANGED,
    },
    "acos_open": {
        "mutation": "acos u owes u > -1 and u < 1",
        "caught_by": [("DEFINEDNESS_CASES", "acos_closed_ends")],
        "admissions": _P1_UNCHANGED,
    },
    "acosh_open_at_1": {
        "mutation": "acosh u owes u > 1",
        "caught_by": [("DEFINEDNESS_CASES", "acosh_closed_end")],
        "admissions": _P1_UNCHANGED,
    },
    "atanh_closed": {
        "mutation": "atanh u owes u >= -1 and u <= 1",
        "caught_by": [("BAD_MOVES", "atanh_upper_end"),
                      ("BAD_MOVES", "atanh_lower_end"),
                      ("DEFINEDNESS_CASES", "atanh_interior")],
        "admissions": _P1_UNCHANGED,
    },
    # E26 (b): a normaliser that reads Int or D as an atom again. No P1 step
    # normalises either, so PROOFS are unchanged.
    "ring_reads_Int_as_atom": {
        "mutation": "ring_nf treats an Int node as an opaque atom, "
                    "everywhere ring_nf runs",
        "caught_by": [("BAD_MOVES", "ring_refuses_Int"),
                      ("BAD_MOVES", "divisor_test_refuses_Int"),
                      # match_refuses_Int dropped: E57's step 2a refuses
                      # it before ring_nf runs (DATA_CHANGES, adjudicated)
                      ("BAD_MOVES", "ftc_check_refuses_Int")],
        "admissions": _P1_UNCHANGED,
    },
    "ring_reads_D_as_atom": {
        "mutation": "ring_nf treats a Deriv node as an opaque atom",
        "caught_by": [("BAD_MOVES", "ring_refuses_D"),
                      ("BAD_MOVES", "close_D_goal_scope_passes"),
                      ("BAD_MOVES", "divisor_test_refuses_D"),
                      # match_refuses_D dropped: E57's step 2a refuses it
                      # before ring_nf runs (DATA_CHANGES, adjudicated)
                      ("BAD_MOVES", "ftc_check_refuses_D")],
        "admissions": _P1_UNCHANGED,
    },
    "field_reads_Int_as_atom": {  # review fix
        "mutation": "field treats an Int node as an opaque atom",
        "caught_by": [("BAD_MOVES", "field_refuses_Int")],
        "admissions": _P1_UNCHANGED,
    },
    "field_reads_D_as_atom": {
        "mutation": "field treats a Deriv node as an opaque atom",
        "caught_by": [("BAD_MOVES", "field_refuses_D")],
        "admissions": _P1_UNCHANGED,
    },
    "norm_num_admits_Int": {
        "mutation": "E7 leaves an obligation holding an Int node undecided "
                    "and admits it",
        "caught_by": [("BAD_MOVES", "norm_num_refuses_Int"),
                      ("BAD_MOVES", "norm_num_refuses_open_Int"),
                      ("BAD_MOVES", "norm_num_refuses_Int_in_domain")],
        "admissions": _P1_UNCHANGED,
    },
    "norm_num_admits_D": {  # review fix
        "mutation": "E7 leaves an obligation holding a Deriv node undecided "
                    "and admits it",
        "caught_by": [("BAD_MOVES", "norm_num_refuses_D"),
                      ("BAD_MOVES", "norm_num_refuses_D_in_domain")],
        "admissions": _P1_UNCHANGED,
    },
    # review fix: the domain half of E7's refusal, named on its own because
    # a proposition-only test is its own mistake, not a node-kind one.
    "norm_num_ignores_domain": {
        "mutation": "E7's Int-or-D refusal looks at an obligation's "
                    "proposition only, not its domain",
        "caught_by": [("BAD_MOVES", "norm_num_refuses_Int_in_domain"),
                      ("BAD_MOVES", "norm_num_refuses_D_in_domain")],
        "admissions": _P1_UNCHANGED,
    },
    # review fix: E12's d_const guard. No P1 F holds an Int or D, so PROOFS
    # are unchanged; ftc_F_contains_D keeps 'deriv-no-rule' (x is free).
    "deriv_d_const_on_Int_or_D": {
        "mutation": "deriv's d_const fires on an x-free subterm holding an "
                    "Int or Deriv node (the guard dropped); each case below "
                    "becomes an accepted step with ftc_D DISCHARGED",
        "caught_by": [("BAD_MOVES", "ftc_F_holds_x_free_Int"),
                      ("BAD_MOVES", "ftc_F_holds_x_free_D")],
        "admissions": _P1_UNCHANGED,
    },
    # Where E26 (a)'s formers are charged (review fix). Installation's own
    # position domain is already pinned by P1.1's goal t^2 >= 0 @ [0, pi/2]
    # and MATCH_ACCEPTS rewrite_under_infinite_range's goal_emits, and ftc's
    # F by its fixed [a, b] rule (E9), so these three cover the sites that
    # were left: a rewrite's R under an Int, both halves of its P (the
    # enclosing range, and the goal's domain, added by a later review fix),
    # and an Int's limit. No P1
    # rewrite's R carries a former under an Int (P1.1 s1's R is t), and
    # P1's only non-literal limits, pi/2 and pi^2/4, owe the closed 2 # 0
    # and 4 # 0 at domain true (E5), so PROOFS are unchanged.
    "rewrite_R_former_at_goal_domain": {
        "mutation": "a rewrite's R is charged at the goal's domain, not at "
                    "the occurrence's position domain P",
        "caught_by": [("MATCH_ACCEPTS", "rewrite_R_former_at_position"),
                      ("MATCH_ACCEPTS",
                       "rewrite_R_former_at_goal_and_range")],
        "admissions": _P1_UNCHANGED,
    },
    "rewrite_R_former_on_ranges_only": {  # review fix
        "mutation": "a rewrite's R is charged on the enclosing ranges only, "
                    "without the goal's domain",
        "caught_by": [("MATCH_ACCEPTS", "rewrite_R_former_at_goal_and_range")],
        "admissions": _P1_UNCHANGED,
    },
    "limit_former_on_own_range": {
        "mutation": "an Int's lo and hi are charged at the domain that "
                    "includes that Int's own range",
        "caught_by": [("MATCH_ACCEPTS", "limit_former_at_outer_domain")],
        "admissions": _P1_UNCHANGED,
    },
}
del _P1_UNCHANGED

# ---------------------------------------------------------------------------
# 9. Parser round trip (Done-when item 6)
#
# parse(show(t)) == t, as trees, over every term in this file (collected by
# all_term_strings below), plus WHAT.md's four precedence cases with the
# trees GRAMMAR.md §9 gives them, plus §6.3's rule schemas
# (ROUND_TRIP_SCHEMAS, E22), plus the grammar and printer cases of
# ROUND_TRIP_GRAMMAR. ECHO and ECHO_NONCANONICAL are the data for item 6's
# second clause, "each parsed goal is echoed before it is proved".

# Done-when item 6, "each parsed goal is echoed before it is proved" (§15.6).
# For each proof, proof_of_life.py asserts:
#   (1) the first line the run prints for the proof, before step s1 is
#       called, equals ECHO[proof];
#   (2) that line equals show_goal(state.goal), where state.goal is the tree
#       the kernel installed;
#   (3) parse_goal(that line) == state.goal, compared as trees.
# Every canonical P1 goal prints as itself, so (1) cannot show whether the
# echo was printed from the tree or copied from the input string.
# ECHO_NONCANONICAL fixes that: its input has non-canonical spacing and
# redundant brackets, so an echo copied from the input fails (1).
ECHO = {
    "P1.1": P1_1_GOAL,
    "P1.1-fallback": P1_1_FALLBACK_GOAL,
    "P1.2": P1_2_GOAL,
    "P1.2-alt": P1_2_GOAL,
}
# (input goal, expected echo). The input parses to the same tree as
# P1_2_GOAL: `0..1` lexes as NAT, `..`, NAT (GRAMMAR.md §2, longest match),
# and parentheses make no node (§8).
ECHO_NONCANONICAL = ("Int[x=0..1] (1)/((1+x^3)) == ?A", P1_2_GOAL)

ROUND_TRIP_EXTRA = [
    ("term", "-x^2", "(neg (pow x 2))"),
    ("term", "sin x^2", "(sin (pow x 2))"),
    ("term", "1/sqrt 3*x", "(mul (div 1 (sqrt 3)) x)"),
    ("term", "pi^2/4", "(div (pow pi 2) 4)"),
    # From §15.6's "set of precedence-ambiguous inputs" and GRAMMAR.md R1's
    # examples. `-x^2` alone cannot catch the `(-x)^2` misprint §15.6 names:
    # no other term in this file has a negated power base, so a printer that
    # dropped the brackets around a Neg base would pass everything else.
    ("term", "(-x)^2", "(pow (neg x) 2)"),
    ("term", "(-x)^(-1)", "(pow (neg x) -1)"),
    ("term", "a - (-b)", "(add a (neg (neg b)))"),
    ("term", "-(-x)", "(neg (neg x))"),
    ("term", "a*(-b)", "(mul a (neg b))"),
]

# The only exact-output assertions in this file: (input, printed, must not
# be). show(parse_term(input)) == printed, and != must-not-be, so a
# regression shows up as a changed string, not only as a round-trip failure.
# The printed forms are GRAMMAR.md §9's, spacing per R3.
PRINT_EXACT = [
    ("(-x)^2", "(-x)^2", "-x^2"),
    ("(-x)^(-1)", "(-x)^(-1)", "-x^(-1)"),
    ("a - (-b)", "a - (-b)", "a - -b"),
    ("-(-x)", "-(-x)", "--x"),
    ("a*(-b)", "a*(-b)", "a*-b"),
]

# Grammar and printer features the P1 strings never reach, including rows
# GRAMMAR.md §9 says were round-tripped. (kind, string, sig, tree). A goal's
# tree is a tuple of judgement trees. Every entry was round-tripped through
# the scratch prototype of GRAMMAR.md. `-(-x)` is in ROUND_TRIP_EXTRA and
# `a*(-b)` in the P1 strings, so neither is repeated here.
ROUND_TRIP_GRAMMAR = [
    # GRAMMAR.md §9 rows not otherwise present
    ("goal", "0^2 == 0 /\\ (pi/2)^2 == pi^2/4", {},
     ("(== (pow 0 2) 0)", "(== (pow (div pi 2) 2) (div (pow pi 2) 4))")),
    ("judgement", "t^2 in C^1([0, pi/2])", {},
     "(reg (pow t 2) 1 [(iv[] t 0 (div pi 2))])"),
    ("term", "(x - 1/2)^2 + 3/4", {},
     "(add (pow (add x (neg (div 1 2))) 2) (div 3 4))"),
    ("term", "(1 + x)*(x^2 - x + 1)", {},
     "(mul (add 1 x) (add (add (pow x 2) (neg x)) 1))"),
    ("goal", "Int[x = 0 .. 1] 3*x^2 + 2*x == ?A", {},
     ("(== (Int x 0 1 (add (mul 3 (pow x 2)) (mul 2 x))) ?A)",)),
    ("goal", "Int[x = 0 .. 1] x*exp(x^2) == ?A", {},
     ("(== (Int x 0 1 (mul x (exp (pow x 2)))) ?A)",)),
    ("goal", "Int[x = 1 .. e_const] (ln x)/x == ?A", {},  # prints ln x / x
     ("(== (Int x 1 e_const (div (ln x) x)) ?A)",)),
    ("term", "(ln x)^2 / 2", {}, "(div (pow (ln x) 2) 2)"),
    ("judgement", "x > 0 @ [1, e_const]", {}, "(> x 0 [(iv[] x 1 e_const)])"),
    ("judgement", "x # 0 @ (1, e_const)", {}, "(# x [(iv() x 1 e_const)])"),
    ("judgement", "e_const > 1", {}, "(> e_const 1)"),
    ("judgement", "ln e_const == 1", {}, "(== (ln e_const) 1)"),
    # one case per printer path P1 does not reach
    ("term", "x^(-1)", {}, "(pow x -1)"),
    ("term", "x^(1/2)", {}, "(rpow x (div 1 2))"),
    ("term", "x^n", {}, "(rpow x n)"),
    ("term", "x - (-y)", {}, "(add x (neg (neg y)))"),
    ("term", "(a/b)/c", {}, "(div (div a b) c)"),               # R2
    ("judgement", "x >= 0 @ [0, 1)", {}, "(>= x 0 [(iv[) x 0 1)])"),
    ("goal", "Int[x = 0 .. oo] exp(-x) == ?A", {},
     ("(== (Int x 0 oo (exp (neg x))) ?A)",)),
    ("judgement", "x > 0 @ (0, oo)", {}, "(> x 0 [(iv() x 0 oo)])"),
    # a named interval: fv is {x, y}, not {x}, so R4 keeps the name
    ("judgement", "x + y > 0 @ x in [0, 1]", {},
     "(> (add x y) 0 [(iv[] x 0 1)])"),
    ("term", "f(x) + 1", {"f": 1}, "(add (f x) 1)"),
]

# E22. §6.3's rule schemas, as judgements. §15.6 asks for the round trip over
# "every rule schema"; Done-when item 6 narrows that to "every term in the
# script". This reads §15.6's "every rule schema" as the §6.3 entries this
# milestone's deriv runs, parsed with SIG (u and v are ordinary variables, as
# in GRAMMAR.md §9's §6.8 pinning). (kind, string, tree).
#   * d_mul, d_sin, d_cos, d_sqrt, d_ln and d_atan put a D node as an operand
#     of * or /, which is GRAMMAR.md D6's `D[x]u * v` case. No other P1
#     string reaches it.
#   * d_pow_int (literal n) and d_chain (f') stay out, per GRAMMAR.md §10.
#   * d_const stays out for its own reasons: its schema variable `e` is
#     refused by GRAMMAR.md D3, and its side condition "x not free in e" is
#     a meta-level statement, not a proposition.
#   * route_neg and route_div are ring/field routes, not §6.3 entries.
#   * The other thirteen §6.3 entries (twenty-four in all, less these eight
#     and the three excluded above) join this list when deriv implements
#     them.
# Each schema was checked with SymPy as an identity (u, v functions of x),
# and each string round-trips under the scratch prototype of GRAMMAR.md.
ROUND_TRIP_SCHEMAS = [
    ("judgement", "D[x] x == 1", "(== (D x x) 1)"),                  # d_var
    ("judgement", "D[x](u + v) == D[x]u + D[x]v",                    # d_add
     "(== (D x (add u v)) (add (D x u) (D x v)))"),
    ("judgement", "D[x](u * v) == D[x]u * v + u * D[x]v",            # d_mul
     "(== (D x (mul u v)) (add (mul (D x u) v) (mul u (D x v))))"),
    ("judgement", "D[x](sin u) == cos u * D[x]u",                    # d_sin
     "(== (D x (sin u)) (mul (cos u) (D x u)))"),
    ("judgement", "D[x](cos u) == -(sin u) * D[x]u",                 # d_cos
     "(== (D x (cos u)) (mul (neg (sin u)) (D x u)))"),
    ("judgement", "D[x](sqrt u) == D[x]u / (2 * sqrt u) @ u > 0",    # d_sqrt
     "(== (D x (sqrt u)) (div (D x u) (mul 2 (sqrt u))) [(> u 0)])"),
    ("judgement", "D[x](ln u) == D[x]u / u @ u > 0",                 # d_ln
     "(== (D x (ln u)) (div (D x u) u) [(> u 0)])"),
    ("judgement", "D[x](atan u) == D[x]u / (1 + u^2)",               # d_atan
     "(== (D x (atan u)) (div (D x u) (add 1 (pow u 2))))"),
]

# The sig each ROUND_TRIP string must be parsed with. Decision: ROUND_TRIP
# stays a list of (kind, string) pairs, as Done-when item 6's driver reads
# it, and the one string that needs a declared symbol is looked up here.
# Every other string is parsed with SIG.
ROUND_TRIP_SIGS = {s: sig for _, s, sig, _ in ROUND_TRIP_GRAMMAR if sig}

# Undeclared function symbols must be refused (GRAMMAR.md D5). Each is
# (input, sig, code), where code is the ParseError code of GRAMMAR.md §1's
# table (D16). The script asserts `err.code == code`; offset checks are
# optional. The first four are WHAT.md's. The rest are GRAMMAR.md's
# neighbouring refusals, added so the round trip is also a test of what the
# parser refuses.
PARSE_REFUSALS = [
    ("x(x+1)", {}, "D5-undeclared"),  # x is not a declared function symbol
    ("f(x)", {}, "D5-undeclared"),    # f undeclared
    # erf undeclared (§9's closed + erf needs it declared). GRAMMAR.md §3's
    # "undeclared call" row gives D5 before the variable and "anything
    # else" rows.
    ("erf(1)", {}, "D5-undeclared"),
    ("g(x, y)", {}, "D5-undeclared"),  # g undeclared
    ("f(x, y)", {"f": 1}, "D5-arity"),  # more arguments than declared
    ("f(x)", {"f": 2}, "D5-arity"),     # fewer arguments than declared
    ("f + 1", {"f": 1}, "D5-uncalled"),  # a declared name used without (
    ("sin x", {"sin": 1}, "D5-sig-collision"),  # sig entry is a builtin
    ("e^x", {}, "D3-bare-e"),
    ("sin(x)^2", {}, "D6-ambiguous-app-power"),
    ("x^2^3", {}, "D8-pow-chain"),
    ("x^-1", {}, "D8-neg-exponent"),
    ("2x", {}, "implicit-mul"),        # §2: no implicit multiplication
    ("0.5", {}, "D1-decimal"),         # D1: no decimals
    ("sinx", {}, "D4-not-a-name"),
    ("2 + Int[x = 0 .. 1] x", {}, "D7-int-in-arith"),
    ("oo + 1", {}, "oo-misplaced"),   # GRAMMAR.md §5: oo is not arithmetic
    # regularity review 2026-09-25 (main session, delegated by the owner): a
    # term nested too deeply for the parser is refused, never a crash. The
    # parser converts any RecursionError into this ParseError (E21 applies
    # to the parser too, since every goal enters through it).
    ("sin(" * 200 + "x" + ")" * 200, {}, "nesting-too-deep"),
]

# The same, read by parse_judgement rather than parse_term: GRAMMAR.md D18,
# an infinite interval end only on its own side, and only open.
PARSE_REFUSALS_JUDGEMENT = [
    ("x > 0 @ (oo, 0)", {}, "oo-misplaced"),    # oo as a lower end
    ("x > 0 @ (0, -oo)", {}, "oo-misplaced"),   # -oo as an upper end
    ("x > 0 @ [0, oo]", {}, "oo-misplaced"),    # a closed infinite end
]


def all_term_strings():
    """Every (kind, string) in this file that the kernel parser must read.
    kind is "term", "judgement" or "goal"."""
    out = []

    def add(kind, s):
        if s is not None and (kind, s) not in out:
            out.append((kind, s))

    for e in NAMED_ENTRIES.values():
        add("judgement", e["statement"])
        for k in ("lhs", "rhs"):
            if k in e:
                add("term", e[k])
        # REWRITE_RULE step 1 instantiates these as judgements
        for h in e.get("hyps", ()):
            add("judgement", h)
    for p in PROOFS.values():
        add("goal", p["goal"])
        add("goal", p["theorem"])
        for st in p["steps"]:
            add("goal", st["goal_after"])
            if "conclusion" in st:
                add("judgement", st["conclusion"])
            a = st["args"]
            for k in ("at", "F", "value"):
                if k in a:
                    add("term", a[k])
            for v in a.get("inst", {}).values():
                add("term", v)
    for d in DERIV.values():
        add("term", d["F"])
        add("term", d["output"])
        for _, sub, emits in d["trace"]:
            add("term", sub)
            for j in emits:
                add("judgement", j)
    for steps in EXPECTED_OBLIGATIONS.values():
        for obs in steps.values():
            for ob in obs:
                add("judgement", judgement_string(ob[0], ob[1]))
    for obs in FINAL_TRACKER.values():
        for ob in obs:
            add("judgement", judgement_string(ob[0], ob[1]))
    for w in WRONG_ANSWERS:
        m = w["move"][1]
        for k in ("F", "value"):
            if k in m:
                add("term", m[k])
        add("term", w["residual"])
        if "residual_factored" in w:
            add("term", w["residual_factored"])
    for b in BAD_MOVES:
        add("goal", b["goal"])
        m = b["move"][1]
        for k in ("at", "F", "value"):
            if k in m:
                add("term", m[k])
        for v in m.get("inst", {}).values():
            add("term", v)
        for kind, s in m.get("facts", ()):
            if kind == "raw":
                add("judgement", s)
        if "e27" in b:  # user decision 2026-09-24 (evaluated answers)
            add("term", b["e27"]["at"])
            add("term", b["evaluated"])
    for c in EVALUATED_ACCEPTS:
        add("goal", c["goal"])
        add("goal", c["theorem"])
        add("term", c["value"])
        add("term", c.get("evaluated"))
    for a in ANSWERS.values():
        add("term", a)
    for kind, s, _ in ROUND_TRIP_EXTRA:
        add(kind, s)
    for kind, s, _ in ROUND_TRIP_SCHEMAS:
        add(kind, s)
    for kind, s, _, _ in ROUND_TRIP_GRAMMAR:
        add(kind, s)
    for m in MATCH_ACCEPTS:
        add("goal", m["goal"])
        add("goal", m["goal_after"])
        add("term", m["move"][1]["at"])
        for ob in m["goal_emits"] + m["emits"]:
            add("judgement", judgement_string(ob[0], ob[1]))
    for c in DEFINEDNESS_CASES:
        add("goal", c["goal"])
        add("goal", c["theorem"])
        add("term", c["move"][1]["value"])
        for ob in c["goal_emits"] + c["emits"] + c["final"]:
            add("judgement", judgement_string(ob[0], ob[1]))
    add("goal", ECHO_NONCANONICAL[0])
    add("goal", OCCURRENCE_CASE["goal"])
    for k in ("all", "one"):
        c = OCCURRENCE_CASE[k]
        add("goal", c["goal_after"])
        for ob in c["emits"]:
            add("judgement", judgement_string(ob[0], ob[1]))
    for listing in REGULARITY_LISTING.values():
        for premise, subs in listing.items():
            add("judgement", premise)
            for j in subs:
                add("judgement", j)
    return out


# Done-when item 6's list: every string in this file, as (kind, string).
# Parse each with ROUND_TRIP_SIGS.get(string, SIG).
ROUND_TRIP = all_term_strings()


# ---------------------------------------------------------------------------
# 10. The decisions, collected

DECISIONS = {
    "E1": "rewrite matching per §18 Q21's default, made precise "
          "(REWRITE_RULE). An Int encloses an occurrence only when the "
          "occurrence is in its body, not its endpoints (GRAMMAR.md §5)",
    "E2": "rewrite with no `occurrence` acts on every occurrence of `at`. "
          "This extends §6.1's single-position `rewrite h at p` and §18 "
          "Q21's 'target subterm', and is not §6.1 itself. Reason: the "
          "result is the same as applying §6.1 once at each position, and "
          "each position carries its own domain P (step 7) and its own side "
          "conditions (step 8), so it adds no soundness risk. It saves steps "
          "where one subterm repeats, as in the fallback's s2 and s3 (3 "
          "occurrences each). With `occurrence` given, it is §6.1's p "
          "exactly (REWRITE_RULE arguments)",
    "E3": "ring reads a/d, d not a nonzero literal, as a * inv(d), inv(d) an "
          "opaque atom keyed by ring_nf(d) (§6.2, 'division by anything else "
          "is itself an opaque atom')",
    "E4": "range orientation: literal endpoints are ordered by norm_num; "
          "an infinite end fixes the orientation, is always open, and emits "
          "nothing, and two equal infinities are refused; otherwise the step "
          "emits lo <= hi (§5.1, §5.3 method 2, §6.1, §6.4)"
          ". Superseded for non-literal ends by E56 (owner's answers, "
          "consolidation spec 2026-09-24)",
    "E5": "a closed obligation is keyed with domain true (§5.3)",
    "E6": "'/', negative-power and RPow formers are charged when a term "
          "enters the proof (§5.1, §11.2); E26 adds the partial builtins, "
          "charged the same way",
    "E7": "norm_num decides literal obligations at emission; false refuses "
          "the step (§6.2, WHAT.md Stubbed). A partial builtin's domain on a "
          "literal is one (E26: ln(-1) owes -1 > 0); an Int or D node is "
          "never a literal and refuses (E26 (b))",
    "E8": "obligations keyed structurally by (proposition, domain), in each "
          "rule's own orientation, with no subsumption (WHAT.md Scope, "
          "GRAMMAR.md D12)",
    "E9": "ftc takes F and a check; the derivative premise is discharged "
          "in-step and its children are on (a, b); an infinite endpoint is "
          "refused 'ftc-infinite-endpoint' before anything is emitted (§5.1, "
          "§6.4)",
    "E10": "`fact` mints a handle and emits nothing; at use, its "
           "hypotheses and its inst values' formers (E6, E26 (a)) are "
           "charged at the using step's domain, and the statement's own "
           "formers are not re-charged (§6.2, §6.8, §15.3, WHAT.md Scope)",
    "E11": "under D[x], the equation's whole domain in x must be open (§6.1 "
           "rev 9, §6.3 rev 7; REWRITE_RULE step 9). (a) Each hypothesis, "
           "and each obligation step 10 charges from R (E6's and E26's "
           "formers), mentioning x must be strict <, >, # 0 or an open "
           "interval, with "
           "no x-mentioning sqrt, asin, acos, acosh, D or Int subterm. "
           "Reason: for a term continuous on an open domain, the set where "
           "it is > 0, < 0 or # 0 is open. Under the partial reading (step "
           "5) a term's domain is open when every partial former in it has "
           "an open natural domain. '/', negative integer powers, ln, tan, "
           "atanh and RPow (base > 0, §5.1) do; sqrt, asin, acos and acosh "
           "do not (§6.9). So strictness alone is not enough: sqrt x + 1 > 0 "
           "and sqrt x + 1 # 0 hold exactly on [0, oo). (b) If the entry has "
           "hypotheses or R charges a former, no Int between the D[x] and "
           "the occurrence may have "
           "an endpoint mentioning x, because E4 puts a closed range and a "
           "non-strict lo <= hi into the position's domain. This is "
           "conservative (Leibniz would allow some such rewrites). Items not "
           "mentioning x are allowed: their set of x is R or empty. E16's "
           "cong inherits both tests",
    "E12": "deriv tries d_const first on any x-free subterm, and refuses "
           "'Int-or-D-not-normalisable' instead when that subterm holds an "
           "Int or Deriv node (E26 (b)); -u and u/v are "
           "routed; d_pow_int's n - 1 is a literal (§6.3)",
    "E13": "a refused step emits nothing and changes nothing",
    "E14": "residuals are lhs - rhs, compared by ring or field equality "
           "with the stated facts, never as strings (§8.7)",
    "E15": "tags are (method, cites) over §5.3's methods plus reg, computed "
           "by E24's TAG_RULES; 'none' is never expected of an admission in "
           "an unmutated PROOFS run (WHAT.md). OCCURRENCE_CASE's false "
           "t >= 0 @ [-1, 0] is expected to be tagged none, and so are "
           "DEFINEDNESS_CASES' false cos(pi/2) # 0 and x > 0 @ x < 0 (E26), "
           "and the true cos 0 # 0 of tan_zero_true: E24 tags cos u # 0 "
           "none, unless the goal's domain states it (hyp), until §6.8's "
           "cos_nonzero_on is pinned",
    "E16": "refl/trans/cong are internal to rewrite/close and the proof "
           "state, not moves (WHAT.md Scope, §6.1)",
    "E17": "handles: a kernel-private object minted by `fact`, accepted "
           "only by identity with the kernel's record for its id and "
           "lineage; copies, pickles and altered ids are refused. The "
           "lineage is a picklable token, so copying and pickling succeed "
           "and the identity check does the refusing. A genuine id passed "
           "as a bare int is refused too, and FORGERIES "
           "fabricated_handle_id (c) tests it (§15.3, WHAT.md Done-when "
           "item 5). Handles protect fact slots only; proof states are "
           "protected by §15.3's sentinel, and HANDLES_IN_FORCE says both "
           "(decided on the owner's behalf, 2026-09-24)",
    "E18": "§5.3 method 5 also splits off a nonzero rational content c*p, "
           "with no degree drop needed (§5.3, §11.2; see DESIGN_DEFECTS)",
    "E19": "close's scope check is fv(value) ∩ bv(original goal) = ∅, "
           "against the original goal, the one the reported theorem "
           "instantiates, not the current goal; D's variable is not in bv "
           "(§9, §15.2 item 1, GRAMMAR.md §5 bv and D11)",
    "E20": "§5.3 method 4 on a non-strict `>= 0` goal also accepts a "
           "non-negative rational constant, zero included: a non-negative "
           "combination of even powers is >= 0. Needed for the fallback's "
           "0 <= pi^2/4 (§5.3; see DESIGN_DEFECTS)",
    "E21": "a fact-slot forgery passes only by raising while it is built, "
           "where its 'accept' lists raise_at_forge, or by step() returning "
           "its refusal code. In every case an exception escaping step() is "
           "a crash and fails the case. Amended: the three cases not passed "
           "at the slot (direct_tracker_write, print_proved_with_admissions, "
           "json_roundtrip_state) carry their own 'accept' outcomes and "
           "'post', and the script checks 'post' whichever accepted outcome "
           "occurred (§15.3, WHAT.md Done-when item 5)",
    "E22": "the round trip covers §6.3's rule schemas that deriv runs in "
           "this milestone (ROUND_TRIP_SCHEMAS), reading §15.6's 'every rule "
           "schema'; d_const, d_pow_int and d_chain stay out (GRAMMAR.md D3, "
           "§10)",
    "E23": "the closed whitelist admits Num, Const, Var, Neg, Add, Mul, "
           "Div, Pow, RPow and App over the sixteen builtins, and refuses "
           "Call, Deriv, Integral and MVar. Var is admitted: §5.1 lists "
           "variables among the formers §9 points to, §9's exclusions target "
           "opaque and non-elementary nodes, and bound names are the trusted "
           "scope check's (E19). It runs on the raw value. Every P1 goal "
           "carries `answer schema closed` with no extensions (§9, §11)",
    "E24": "the tagger (TAG_RULES) tags an admission with the first §5.3 "
           "method, in §5.3's order, whose cheap untrusted feasibility check "
           "passes, citing the §6.8 entries used, and ('none', ()) if none "
           "passes; regularity is tagged reg by shape. Reason: an exact tag "
           "assertion is only a check if the rule that produces the tag is "
           "stated (§5.3, §7, WHAT.md)",
    "E25": "a charged divisor d is refused 'divisor-normalises-to-zero' when "
           "ring_nf(d) is 0 (at E6, route_div and field) or, inside field, "
           "when its field normal form's numerator is 0; the test runs "
           "before anything is emitted or normalised, and a literal 0 "
           "divisor gets this code, not E7's obligation-refuted (§6.2). "
           "tan's cos u # 0 is a domain, not a divisor, and is not tested "
           "(E26)",
    "E26": "definedness formers (user decision 2026-09-24). (a) Each partial "
           "builtin owes its natural domain, §6.9's C^0 set, as a former "
           "charged exactly like '/' (E6): ln u owes u > 0, sqrt u owes "
           "u >= 0, tan u owes cos u # 0, asin u and acos u owe u >= -1 and "
           "u <= 1, acosh u owes u >= 1, and atanh u owes u > -1 and u < 1. "
           "One linear item per bound, in the "
           "orientation u REL c, closed where the builtin is defined at the "
           "end and open where it is not. A literal one is decided by "
           "norm_num (E7), and a false one refuses the step. field still "
           "emits only divisors. (b) ring, field and norm_num refuse "
           "'Int-or-D-not-normalisable' on any side holding an Int or D "
           "node, and deriv refuses it where d_const would fire on an "
           "x-free subterm holding one (E12). Such a node "
           "has no definedness condition the kernel can state "
           "until regularity and diverges exist; no P1 step normalises one. "
           "Reason: ring's identities hold only where every atom is "
           "defined, and before E26 0*ln(-1) == ?A and "
           "tan(pi/2) - tan(pi/2) == ?A closed as 'Proved.'; §14's "
           "agreement of the total and partial readings rests on every "
           "partial former carrying its condition (§5.1, §6.2, §6.9, §14)",
    "E27": "evaluated answers (user decision 2026-09-24). A value closing a "
           "`closed` goal must be fully evaluated, a property and not a "
           "canonical form: (a) no subterm can still be evaluated by an "
           "equation entry in force, matched as rewrite matches (E1 steps "
           "3-4, ring-normalised arguments), with a stated reading for each "
           "schema entry (sqrt_sq: a closed perfect square; atan_odd: every "
           "coefficient negative; sqrt_sq_val: Pow(sqrt b, n), |n| >= 2); "
           "and (b) no unreduced literal arithmetic, four order-independent "
           "local tests over sum and product flattenings (a literal term "
           "that is not a rational literal in lowest terms; a zero "
           "summand, or a sum whose normal form has fewer monomials than "
           "its summands' normal forms together; a zero, unit, second, "
           "unreduced or like factor; "
           "a unit or nested power, a double negation). Otherwise "
           "'close-not-evaluated', naming the first (a) offender in "
           "pre-order, else the first (b) one, carried as the residual. "
           "Untrusted, in schema.py beside E23, and run last in close, "
           "after the check and check_goal, so every other refusal wins "
           "and the code means 'right value, unevaluated form'. Reasons: "
           "§9 (after ftc, F(b) - F(a) is a whitelisted value, so close "
           "with it is refl again), §6.8 ('every authored goal terminates "
           "in this table', enforced by nothing before), and the user's "
           "decision. ln 2 + ln 3 is accepted: a known limitation, not a "
           "bug; atan(-1/2) and pi*(1/sqrt 3) are refused as deliberate "
           "canonicalisation of sign and division, not evaluation "
           "(EVALUATED_RULE)",
    # E28-E34: discharge spec 2026-09-24, written before any code (section
    # 11, DISCHARGE_RULE, states each in full).
    "E28": "discharge's trust split (§5.3, §7, §15.2 item 5, §15.4 item "
           "1). An untrusted search, beside the tagger and in TAG_RULES' "
           "order, builds one certificate per obligation; a small trusted "
           "checker decides it, rebuilding from the key alone the "
           "constraint set, the target and every sub-obligation's key, so "
           "a certificate names constraints and supplies witnesses but "
           "never a hypothesis. No fallback to a later method when the "
           "checker refuses: a search bug shows as an admission with "
           "REASON_REJECTED, never as a false discharge. Certificates per "
           "method: hyp, a Γ item or a chain of them; range and linear, a "
           "Farkas combination (E29); sign, c0 + sum ci*si^ki checked by "
           "ring_equal, ci > 0, ki even, c0 > 0 (>= 0 on a non-strict "
           "target, E20); sign product, c * f1...fn checked by ring_equal "
           "with each factor's sign by its own certificate and the parity "
           "checked, strict targets only; cite, a §6.8 entry, its "
           "instantiation, its conclusion implying the proposition as "
           "TAG_RULES says, and one certificate per hypothesis. Reason: "
           "§7's claim for `domain` is true only if discharge emits "
           "witnesses the kernel re-checks, and §15.2 moved Fourier-Motzkin "
           "and the sign heuristic out of the trusted base on that "
           "condition",
    "E29": "method 3 is Fourier-Motzkin with a checked Farkas witness, in "
           "stage 1, and method 2 is the same certificate over the range's "
           "own items (owner's decision, 2026-09-24, settling §17 against "
           "§5.3). The search's FM (the tagger's, which already finds the "
           "irreducible combination) emits the non-negative multipliers; "
           "the trusted check is: every label is in the key's constraint "
           "set, every multiplier > 0, the negated goal's is present, and "
           "the combination ring-normalises to a constant k with k < 0, or "
           "k = 0 with a strict constraint used. §5.3's satisfiability "
           "pre-check runs first, in the search, on the set without the "
           "negated goal; an infeasible set skips methods 2-3. No interval "
           "propagation is built. The owner's reason: §17's claim that "
           "hypothesis closure, by-range, sign certificates and interval "
           "propagation cover the target obligations did not survive the "
           "proof-of-life (the linear tag is needed for 0 <= pi/2, "
           "1 <= e_const and e_const > 0, and range for t >= 0 on "
           "[0, pi/2]); an FM implementation already exists, untrusted, in "
           "the tagger; and the trusted Farkas check is smaller and more "
           "auditable than trusted interval propagation, which would add to "
           "§15.2's list the strict/non-strict bookkeeping §15.2 names as "
           "the error-prone part. DESIGN.md §17's stage-1 exclusion list "
           "and stage 4 row, and §15.2 item 5, need updating to match",
    "E30": "the checker checks what soundness needs and no more: not "
           "§5.3 method 5's 'strictly lower degree' (the certificate is "
           "finite, so the check terminates by structural recursion; the "
           "degree rule stays the search's), not method 4's discriminant "
           "(the certificate is always the completed square), and not "
           "linearity (ring-normalising the combination is sound over any "
           "polynomials in opaque atoms). A refusal met inside discharge "
           "(ring on an Int or D node) counts as a rejected certificate, so "
           "E7 stays the only place Int-or-D-not-normalisable is raised",
    "E31": "§18 Q22's first step: before deciding, discharge rewrites the "
           "key (proposition and domain) with §6.8's exact values, every "
           "ENTRIES equation with no schema variable and no hypothesis "
           "(EXACT_VALUE_ENTRIES), matched as rewrite matches (E1 steps "
           "2-4), every occurrence, to a fixed point (each rewrite removes "
           "an App node and adds none, so it terminates). Schema entries "
           "(sqrt_sq, atan_odd, sqrt_sq_val) are not exact values: they "
           "need an instantiation, and two owe hypotheses. The rewrite "
           "preserves the key's truth, and its entries join the tag's "
           "cites",
    "E32": "discharge runs at emission, inside kernel._emit, after E7, on "
           "the step's buffer: a refused step changes nothing (E13), and "
           "Q22 wants the refusal 'at the step where it goes wrong'. A "
           "status is decided once and never changes (discharge reads only "
           "the key and ENTRIES), so the tracker records no admitted -> "
           "discharged transition; _Tracker.add is unchanged. Obligation "
           "gains `certificate`; `reason` becomes REASON_REG, REASON_NONE, "
           "REASON_EMPTY or REASON_REJECTED for an admission. report() is "
           "unchanged: 'Proved.' only when N = 0. With regularity unbuilt "
           "every PROOFS and stage-0 proof reads 'Proved modulo 3 "
           "admissions' (§5.4, WHAT.md item 3)",
    "E33": "decided false (§18 Q22, settled 2026-09-24): a non-Reg "
           "obligation refuses its step with the new code "
           "'obligation-decided-false' when (F1) the exact values make it "
           "literal and norm_num finds it false, (F2) it is closed, an "
           "ordering, and its negation is discharged, or (F3) it has a free "
           "variable and a rational point from COUNTERPOINT_CANDIDATES lies "
           "in its domain (each item there discharged), keeps its terms "
           "defined (each owed former there discharged) and makes it false "
           "by F1 or F2. Nothing else is decided false; an obligation none "
           "reaches stays admitted, tagged by E24. Messages are "
           "DECIDED_FALSE_MESSAGES'. It can only refuse, so it is outside "
           "the trusted base (§15.2's condition, as for E27). So "
           "tan(pi/2) - tan(pi/2) is refused at installation (F1), "
           "OCCURRENCE_CASE's t >= 0 @ [-1, 0] refuses the rewrite (F3, "
           "t = -1), and x > 0 @ x < 0 refuses its goal (F3, x = -1); "
           "with cos_zero and sqrt_zero pinned (E35), tan 0's cos 0 # 0 is "
           "discharged (1 # 0, norm_num) and sqrt x # 0 @ [0, 1] is refused "
           "(F3 at x = 0, where with sqrt_zero it reads 0 # 0); cos 1 # 0 "
           "stays admitted none. F3 goes beyond Q22's example, which is "
           "F1: Q22's reason ('a goal that can only be proved through a "
           "false admission is a wrong goal') applies to any obligation "
           "discharge can show false, and a counter-point is the checkable "
           "form of 'false' for an obligation with a free variable. Its "
           "full reach is the owner's decision (E35 (1))",
    "E34": "the soundness property test (DISCHARGE_PROPERTY_TEST: every "
           "accept holds at random rational points of the key's domain by "
           "the test's own exact evaluation, with pi and e_const sampled in "
           "their sign facts' regions; every refutation re-checked "
           "independently; minimum sample counts so it cannot pass "
           "vacuously; it must fail under each new checker planted bug), "
           "and how the suite switches (DISCHARGE_SWITCH: checker and "
           "search first, tested directly with nothing wired in; then "
           "wiring and the DISCHARGE_* tables in one commit; the "
           "pre-discharge tables kept as the record)",
    # The owner's answers of 2026-09-24 to the discharge spec's five
    # questions (discharge spec 2026-09-24, owner answers).
    "E35": "the owner's answers, 2026-09-24. (1) F3 keeps its full reach: "
           "a goal with no stated domain whose terms are undefined "
           "somewhere (ln x * 0 == ?A) is refused, and D[x] Int[t = 0 .. x] "
           "... needs @ 0 <= x. Reason (owner): it is E26 applied "
           "consistently, a term owes its domain and the learner states "
           "it. (2) The satisfiability pre-check stays untrusted, in the "
           "search. Reason (owner): it can only withhold a discharge, an "
           "empty domain makes obligations vacuously true, and E4 now "
           "builds the range items correctly, which was the real danger. "
           "(3) cos_zero : cos 0 == 1 and sqrt_zero : sqrt 0 == 0 are "
           "pinned now, §6.8 equations with no schema variable and no "
           "hypothesis (DISCHARGE_NEW_ENTRIES), so E31's exact values use "
           "them and E27 refuses cos 0 and sqrt 0 in an answer "
           "(DISCHARGE_E27_CHANGES); cos_nonzero_on waits. (4) One refusal "
           "code, 'obligation-decided-false', whose message says how the "
           "obligation was decided (DECIDED_FALSE_MESSAGES: after exact "
           "values, by its negation, or at a point, and there how). (5) "
           "The bounded counter-point search is accepted: a miss stays "
           "admitted, tagged none (DISCHARGE_UNDECIDED)",
    # E36-E44: int_subst spec 2026-09-24, written before any code (section
    # 12, INT_SUBST_RULE, states each in full).
    "E36": "int_subst is a fifth step() move (§6.4's name; §11.1's `step "
           "subst (x := t^2) over t in [0, pi/2]` is its display). Args, "
           "exactly: {'var': str, 'sub': Term, 'new_var': str, 'lo': Term, "
           "'hi': Term, 'check': 'ring' | 'field', 'facts': [handle, ...]}, "
           "read as x := sub over new_var from lo to hi, with sub(lo) owed "
           "equal to the integral's lower limit and sub(hi) its upper. It "
           "composes with step() exactly as ftc does: the common checks, "
           "then fact slots, then INT_SUBST_RULE's refusals in order, one "
           "buffer of emissions, E13 on refusal. It acts on the goal's "
           "left side only, which must be an Int ('int-subst-no-integral'), "
           "as ftc does; the rhs and the goal's domain are unchanged. "
           "Reasons: §8.4's substitution row ('you supply x := phi(t) and "
           "the range; the tool computes phi'') fixes what the learner "
           "gives; var is redundant with the binder but is what §11.1's "
           "script types, so a mismatch is the learner's error "
           "('int-subst-wrong-variable'), not bad-args; `check` and "
           "`facts` are ftc's (E9), because the endpoint equations need "
           "field for a divisor (x := 1/t) as ftc's check does. A position "
           "argument (int_subst inside a sum, under a D) is not needed by "
           "P1 or SUB1 and is left out, so a substitution under D[x] never "
           "reaches the rule (§6.1 rev 9's argument would otherwise have to "
           "be restated for it)"
           ". Amended by the owner's answers of 2026-09-24: an optional 'mode' ('forward', the default, or 'reverse' with an extra 'f', E45) and an optional 'occurrence' (E48) join the key set, and the move acts on any Int in the goal, not only the top-level left side (E48); the no-integral refusal is then 'nothing to select', and a substitution under D[y] is tested as rewrite's step 9 is",
    "E37": "forward substitution only: x := phi(t) replaces the integration "
           "variable, as §6.4 states the rule and §8.4 describes the move. "
           "Reverse substitution u := g(x), §8.5's chain-rule row "
           "f'(x)*g(f(x)) -> u = f(x), is out of this step. It is the same "
           "theorem read right to left, but the kernel would have to be "
           "handed the new integrand f(u) and check h(x) == f(g(x))*g'(x) "
           "on [a, b] by field, a second trusted check with its own "
           "divisors and facts that §6.4 does not state; ftc already closes "
           "every such integral directly (STAGE0.md gap 5: S2 by F := "
           "exp(x^2)/2). Found while deciding: the forward emulation of "
           "S2's u = x^2, x := sqrt u over [0, 1], is refused, correctly, "
           "because sqrt is not C^1 at 0 (d_sqrt's u > 0 @ [0, 1], F3 at "
           "u = 0; problems/stage0 INT_SUBST_S0_REFUSALS). So the chain-rule "
           "row has no substitution move at all until reverse substitution "
           "is decided (owner question)"
           ". Superseded by the owner's answer of 2026-09-24 (E45): "
           "reverse substitution is in, as int_subst's reverse mode, "
           "and S2 gains the route u := x^2 (problems/stage0 S2R). "
           "The forward x := sqrt u stays refused, correctly",
    "E38": "premises and where they live (INT_SUBST_RULE steps 8-12). With "
           "G the goal's domain and I' the E4 range of (new_var, lo, hi): "
           "lo's and hi's formers at G; sub's formers at G+I'; deriv(sub, "
           "new_var, G+I') and its side conditions on the CLOSED I', unlike "
           "ftc's open J, because §6.4 asks phi in C^1([a, b]) and phi' "
           "stands in the new integrand, which must be defined at the ends; "
           "Reg(sub, 1, G+I') (source int_subst_phi_C1) and Reg(f[x := sub], "
           "0, G+I') (int_subst_f_C0), both admitted 'regularity not "
           "built'. The C^0 premise is on the composed f(phi(t)), not on f "
           "over the old range (§6.4, and §11.1's correction of revision "
           "1); the new integrand f(phi(t))*phi'(t) enters the goal and its "
           "formers are charged at G+I', which is where §11.1's nested "
           "t^2 >= 0 @ [0, pi/2] comes from (sqrt's former, E26, by sign). "
           "The old range [a, b] is used by nothing, so int_subst owes no "
           "key on it and not its orientation",
    "E39": "the endpoint equations sub[new_var := lo] == a and sub[new_var "
           ":= hi] == b (a, b the integral's limits as written), keyed at G "
           "(E5: true when closed), are decided IN THE STEP, never "
           "admitted: first §6.8's exact values (E31's rewrite, trusted), "
           "then `check` (ring, or field with the facts, whose divisors, "
           "hypotheses and inst formers are emitted at G as ftc's are). "
           "Both hold: each is recorded DISCHARGED with tag (check, the "
           "exact-value entries used then the facts' entries), certificate "
           "None, sources int_subst_lo and int_subst_hi, as ftc's premise "
           "is (E9). Either fails: 'int-subst-endpoint-mismatch' with "
           "residual image - limit after the exact values (E14), lower end "
           "first. Reasons: §11.1 decides them 'by ring'; an equation is "
           "no discharge target (DISCHARGE_RULE, Targets), so emitted "
           "normally a true non-literal one ((pi/2)^2 == pi^2/4) could only "
           "be admitted; and without the exact values x := ln t over [1, "
           "e_const] and x := sin t could never pass (ln 1, sin(pi/2) are "
           "atoms to ring). The images need no charge of their own: sub's "
           "formers were charged on I', which contains both ends",
    "E40": "orientation and decreasing phi. The correspondence is by end, "
           "not by order: lo is the preimage of the lower limit. The new "
           "integral is Int[new_var = lo .. hi], as §6.4 writes it, so a "
           "decreasing phi gives reversed limits, which §5.1 gives a "
           "meaning. I' is built by E4: literal ends are ordered by "
           "norm_num and give [min, max] with no orientation owed, which "
           "handles x := 1 - t over [1, 0] and SUB1 (INT_SUBST_ACCEPTS "
           "decreasing_literal_ends); otherwise I' = [lo, hi] and lo <= hi "
           "is owed at G (orient), always, since the Reg premises use I'. "
           "For a decreasing phi with non-literal ends that orientation is "
           "false and F2 refuses the step (INT_SUBST_BAD_MOVES "
           "decreasing_symbolic_ends: x := pi/2 - t over [pi/2, 0]). This "
           "is a limitation, stated: §5.1 calls x = a cos(theta) 'the "
           "canonical case' of reversed output, and it is refused. Owner "
           "question: a flipped conclusion Int[t = hi .. lo] "
           "-(f(phi(t))*phi'(t)), or E4's orient argument"
           ". Superseded in part by the owner's answer of "
           "2026-09-24 (E46): with non-literal ends the kernel now "
           "decides which order discharge proves, keeps the limits "
           "when lo <= hi is discharged, builds the flipped "
           "Int[t = hi .. lo] -(...) when hi <= lo is, and refuses "
           "'int-subst-orientation-undecided' when neither is. "
           "Literal ends are unchanged. decreasing_symbolic_ends is "
           "now accepted, flipped"
           ". And E56 generalises the rule to every step",
    "E41": "phi' is deriv's output, verbatim (E12's literal forms, so t^2 "
           "gives 2*t^1*1), and never an argument. A learner cannot supply "
           "a wrong phi': an extra key is 'bad-args' (E36's exact key "
           "set). deriv is trusted in this milestone (§15.2 item 2, "
           "ARCHITECTURE.md §1), so a wrong phi' would be a trusted-base "
           "bug, the classic 'forgot the dx' error, and the planted bug "
           "int_subst_drops_phi_prime is how the suite shows it is caught. "
           "The kernel does not tidy phi' (it never simplifies anything "
           "itself): P1.1-sheet's new integrand is sin(sqrt(t^2))*(2*t^1*1), "
           "not §11.1's display sin(sqrt(t^2))*(2*t), and the rest of the "
           "route is unaffected because ring reads t^1*1 as t",
    "E42": "freshness, scope and capture (§15.2 items 1 and 3, GRAMMAR.md "
           "§5, D10, D11). new_var must be a variable name (parse_term "
           "gives a Var; else bad-args) that occurs nowhere in the current "
           "goal, free or bound, domain included, so in particular not var "
           "itself ('int-subst-not-fresh'). fv(sub) must lie in fv(goal) + "
           "{new_var}, and fv(lo), fv(hi) in fv(goal) "
           "('int-subst-scope'): sub may not mention the old bound "
           "variable, nor a limit the new one (GRAMMAR.md §5: a bound "
           "variable may not occur in its own endpoints). f[x := sub] is "
           "built by terms.subst, trusted and capture-avoiding, before "
           "anything is emitted, so D10's refusal ('subst-under-D') and "
           "D17's ('rpow-literal-exponent') come first. check_goal on the "
           "new goal is the backstop (D11, shadowing). Freshness is "
           "stricter than soundness needs, since capture-avoiding "
           "substitution and check_goal already make a clash harmless or "
           "refused, and it is kept strict so that the variable the "
           "learner named is the one in the new goal. E19 is unchanged: "
           "close checks the value against the ORIGINAL goal's bound names, "
           "where new_var does not occur, so ?A := t - t + 2 after "
           "P1.1-sheet passes the scope check (the theorem then holds for "
           "every t, so nothing unsound is reported) and is refused by "
           "E27 (b2) instead (INT_SUBST_BAD_MOVES close_with_new_variable)"
           ". Amended by the owner's answers (E45, E48): scope is "
           "relative to the position (free in the goal or bound by an "
           "enclosing Int), and in reverse mode sub may mention var "
           "and f may mention new_var, each and nothing else outside "
           "that scope",
    "E43": "interaction with discharge and E26-E27. Every emission except "
           "the two endpoint equations goes through DISCHARGE_RULE "
           "unchanged: formers, the orientation and deriv's side "
           "conditions are discharged by certificate, or refuse the step "
           "when decided false (E33: x := ln t over [0, 1] at t = 0; the "
           "non-monotone 1/x case at t = 0), or are admitted; the two Reg "
           "premises are admitted REASON_REG. E26 (b): an Int or D in sub "
           "is refused by deriv ('deriv-no-rule' or "
           "'Int-or-D-not-normalisable'), one in a limit by the endpoint "
           "check's ring, and one in the body only reaches Reg keys (which "
           "skip norm_num) and the new goal, where Int and D owe no "
           "former. E27 is untouched: it runs only in close. With "
           "regularity unbuilt, a proof through int_subst reads 'Proved "
           "modulo 3 + 2k admissions' for k substitutions and one ftc",
    "E44": "staging. The move's data lives in section 12's INT_SUBST_* "
           "tables and in problems/stage0's section 12, not in PROOFS, "
           "REFUSAL_CODES, SOURCES or any DISCHARGE_* table, so the suite "
           "stays green until the build: every existing child process runs "
           "PROOFS, and a fifth proof there would need all 48 existing "
           "seams re-traced against it, which tests the old seams and not "
           "the new move. INT_SUBST_SEAMS re-traces the three whose seam "
           "int_subst uses. P1.1 (the t-form) stays in PROOFS as the proof "
           "of its own goal; whether P1.1-sheet becomes ROUTE['P1.1'] is "
           "the owner's (INT_SUBST_SWITCH)"
           ". The owner answered (E47): not now, a follow-up after "
           "the build",
    # E45-E49: the owner's answers of 2026-09-24 to the int_subst spec's
    # five questions (int_subst spec 2026-09-24, owner answers). Section
    # 12's INT_SUBST_RULE states them in full. Where E38, E39 and E42 say
    # G, read P, the position domain (E48).
    "E45": "reverse substitution is in (owner's answer 1), as int_subst's "
           "mode 'reverse': args {'mode': 'reverse', var, sub, new_var, lo, "
           "hi, f, check, facts[, occurrence]}, read as new_var := sub, "
           "where sub = g(x) is a term in var and f = f(new_var), the new "
           "integrand the learner supplies, is a term in new_var; lo and hi "
           "are the learner's new limits, owed equal to g(a) and g(b). The "
           "kernel builds f(g(x)) := f[new_var := g] by terms.subst and "
           "g' := deriv(g, var, P+I) on the CLOSED old range I (E38's "
           "reason: g in C^1([a, b])), and checks body == f(g(x))*g'(x) at "
           "P+I by `check` (field's divisors and the facts' hypotheses and "
           "inst formers at P+I). A failure refuses "
           "'int-subst-check-failed' with residual body - f(g(x))*g'(x) "
           "(E14); success records that equation DISCHARGED with tag "
           "('deriv+' + check, the facts' entries), certificate None, "
           "source int_subst_integrand, as ftc's premise is (E9). The "
           "endpoint equations g(a) == lo and g(b) == hi are E39's, exact "
           "values then check, so the new limits are learner-written "
           "values (0 and 1), not unevaluated images (0^2, 1^2). Premises: "
           "Reg(g, 1, P+I) and Reg(f(g(x)), 0, P+I). The image question: "
           "the theorem needs f continuous on g([a, b]), and the kernel "
           "never states an image. For continuous g on the compact [a, b], "
           "f(g(x)) in C^0([a, b]) is equivalent to f in C^0(g([a, b])) "
           "(g is a closed map onto its image, hence a quotient map: "
           "§6.4's own argument for the forward form), so the premise is "
           "stated on the composition over the OLD range, monotone or not, "
           "and nothing is refused for non-monotonicity "
           "(INT_SUBST_ACCEPTS reverse_non_monotone). f(g(x))'s formers "
           "are charged at P+I, which is f's definedness on the image in "
           "the same way; the new goal's own formers, f on the interval "
           "between the new limits, are charged as any new goal's are, and "
           "hold whenever the premise does, since that interval lies in "
           "g([a, b]) by the intermediate value theorem. The old range's "
           "orientation a <= b is owed when non-literal (the premises use "
           "I), as for ftc. This is §6.4's rule read right to left, with "
           "the identity body == f(g(x))*g'(x) as the checked link. "
           "HolPy's first probe (Int_-1^1 x^2 by u = x^2, giving 0) is "
           "refused at that check (INT_SUBST_BAD_MOVES holpy_probe_reverse)",
    "E46": "orientation of the new range, both modes (owner's answer 2). "
           "Two rational literal ends: E4 orders them, nothing is owed, and "
           "the limits are kept as given, reversed or not, because every "
           "later step orders them the same way and owes nothing false "
           "(SUB1 and decreasing_literal_ends are unchanged). Otherwise the "
           "kernel asks discharge, DISCHARGE_RULE steps (3)-(5) only, with "
           "no refutation, for lo <= hi at P: if that is discharged it is "
           "emitted (orient) and the limits kept; else for hi <= lo at P: "
           "if that is discharged it is emitted (orient) and the new "
           "integral is the flipped Int[new_var = hi .. lo] -(body'), with "
           "the premises on [hi, lo]; else the step is refused "
           "'int-subst-orientation-undecided'. Only the chosen key is "
           "emitted, so a false candidate is not chosen rather than "
           "refuted. Soundness: §5.1 defines a reversed integral, "
           "Int[t = c .. d] g == -Int[t = d .. c] g, and -Int g == "
           "Int(-g) pointwise; the flip is that identity composed with "
           "§6.4's, a trusted rule-table addition (§15.2 item 2) owing "
           "nothing beyond the discharged order, which is what makes "
           "[hi, lo] the range. An undecided non-literal order was "
           "admitted under E4; it is now refused, because the kernel must "
           "know which form to build. x = cos(theta) over [pi/2, 0], "
           "§5.1's canonical case, is accepted (INT_SUBST_ACCEPTS "
           "cos_theta_canonical and cos_theta_full)"
           ". Its decision rule is now E56's, shared by every step "
           "that builds a range, and its refusal code is E56's "
           "'orientation-undecided'; int_subst keeps its flipped form",
    "E47": "P1.1-sheet stays in INT_SUBST_PROOFS (owner's answer 3). "
           "Moving it into PROOFS and ROUTE['P1.1'], with the re-trace of "
           "the existing seams against it, is a follow-up after the build",
    "E48": "position (owner's answer 4). An optional 'occurrence' (int, "
           "E2's 0-based index) selects the k-th Integral node of the "
           "goal's non-?A side (both sides when there is no ?A) in "
           "REWRITE_RULE's pre-order; an index out of range refuses "
           "'int-subst-no-integral', and a binder other than var "
           "'int-subst-wrong-variable'. With no occurrence, exactly one "
           "Int binding var must exist: none refuses "
           "'int-subst-wrong-variable' when the side holds some Int and "
           "'int-subst-no-integral' when it holds none; two or more refuse "
           "'int-subst-ambiguous'. Not E2's every-occurrence default: E2 "
           "is safe because every occurrence is the same term, while the "
           "Ints binding var generally have different limits and bodies, "
           "and one set of args fits one integral's endpoint equations, so "
           "'all' would refuse unless they coincide; the learner names "
           "the one meant. P, the position domain (REWRITE_RULE step 7), "
           "is G plus the E4 range of each Int whose body holds the "
           "selected one, and replaces G throughout; scope (E42) is "
           "relative to it. Under a D[y] (REWRITE_RULE step 9, E11): if y "
           "occurs free in the selected Int's limits or body, in sub, f, "
           "lo or hi, or in a limit of an Int between the D[y] and the "
           "position, the step is refused "
           "'rewrite-under-D-needs-open-domain', rewrite's code, since it "
           "is rewrite's rule. Every key the step emits is built from "
           "those terms and carries a closed range or a Reg judgement, "
           "neither open in y, so when y occurs in one of them step 9 "
           "cannot be met, and when it occurs in none no emitted key "
           "mentions y and step 9's (a) and (b) hold vacuously. "
           "Conservative, as E11 (b) is. Soundness: the step proves "
           "Int_old == Int_new at P under what it emits (every key at P, "
           "P+I or P+I'); replacing an equal subterm at its position is "
           "REWRITE_RULE step 5's congruence (E16's cong) with domain P; "
           "under an enclosing Int the range domain is enough (§6.1), "
           "and under D[y] the test above is step 9",
    "E49": "a sign fact for sqrt atoms is in (owner's answer 5): "
           "sqrt_nonneg : sqrt a >= 0 @ a >= 0, pinned for entries.py "
           "(SQRT_NONNEG_ENTRY) and read by the linear method (§5.3 "
           "methods 2 and 3) for each sqrt atom of the key, as pi_pos and "
           "e_gt_one are read for their constants: label ('fact', "
           "'sqrt_nonneg', u), constraint (sqrt u, non-strict), accepted "
           "only when an atom sqrt w with ring_nf(w) = ring_nf(u) occurs "
           "in the key's proposition or domain (SQRT_FACT_RULE). Its "
           "hypothesis u >= 0 gets no child certificate: an accepted "
           "certificate claims the obligation only where its terms are "
           "defined (DISCHARGE_RULE, the trust split), and where sqrt u is "
           "defined u >= 0 holds, which is also exactly the former E26 "
           "charged where that sqrt entered. Cited as 'sqrt_nonneg' when "
           "its multiplier is positive, after pi_pos and e_gt_one. "
           "Re-derived by hand: no existing expectation changes "
           "(SQRT_FACT_CHANGES lists every key holding a sqrt atom and "
           "why), and 1 + sqrt x # 0 @ [0, 4] is now discharged "
           "('linear', ('sqrt_nonneg',)), so Int_0^4 1/(1 + sqrt x) is a "
           "problem file (problems/stage0 SUB2)",
    # int_subst review 2026-09-24: the main session's decision on the
    # skeptic's F3 finding, within the owner's Q22 decision (E33, E35 (1))
    # to refuse what discharge can show false.
    "E50": "F3 tries the rational roots of the proposition's own "
           "polynomial pieces (main session's decision, 2026-09-24; "
           "COUNTERPOINT_CANDIDATES (4)). The skeptic's finding: "
           "Int[x = -1 .. 5/3] 1/(x^2 + 1) by x := 5/(2*t - 5) over [0, 4], "
           "then ftc, reported 'Proved modulo 9 admissions' for a false "
           "value, because 2*t - 5 # 0 @ [0, 4], false only at t = 5/2, "
           "was admitted tagged none: no candidate is a root of the key's "
           "polynomial. The defect predates int_subst (ftc alone, "
           "Int[x = 0 .. 4] -1/(1 + (x - 5/2)^2) with F := atan(1/(x - "
           "5/2)), shows it), but a substitution's map puts its poles into "
           "keys routinely. The pieces of a proposition's target g "
           "(DISCHARGE_RULE, Targets) are g, each factor of a top-level "
           "product in it, and each base of an integer power, recursively; "
           "each piece whose ring normal form is a polynomial in one "
           "variable v with rational coefficients (no other variable, "
           "constant or atom) contributes its rational roots, found by the "
           "rational root test on its integer coefficients and kept only "
           "where the polynomial is exactly 0, as candidates for v. The "
           "test is bounded as the tagger's factoriser is: a polynomial "
           "whose lowest nonzero or leading integer coefficient exceeds "
           "ROOT_TEST_BOUND (10^6) in absolute value contributes none. The "
           "roots come last for v, after (1)-(3), smallest |r| first and "
           "positive before negative, so every existing first point, and "
           "every existing message, is unchanged, and the 256-point walk "
           "still bounds the search. Only the proposition's pieces count: "
           "at a root of an owed former's polynomial the former is not "
           "settled true, so F3's definedness rule discards that point, "
           "and each former is its own key, where that polynomial is the "
           "target and its roots are tried. Still undecided, and admitted "
           "none: irrational poles (t^2 - 2 # 0 @ [0, 2], "
           "F3_ROOTS_CASES f3_irrational_pole_undecided), roots beyond the "
           "bound, and pieces with more than one variable. An exact "
           "univariate sign decision (Sturm sequences) is recorded as a "
           "future method (DESIGN_DEFECTS). F3 stays untrusted and can "
           "only refuse (E33): a wrong root costs a wrong refusal, which "
           "the refutation's re-check at its point and the property test "
           "catch",
    # E51-E55: consolidation spec 2026-09-24, written before any code
    # (section 13 states each in full).
    "E51": "int_flip (the owner's decision, 2026-09-24): an explicit "
           "trusted move for §5.1's reversed integral, args {} or "
           "{'occurrence': k}, int_subst's selector without a variable (the "
           "one Int, or the k-th; 'int-flip-no-integral', "
           "'int-flip-ambiguous'), its position domain, and its D[y] test "
           "('rewrite-under-D-needs-open-domain'). DECIDED ON THE OWNER'S "
           "BEHALF, and a deviation from the task's wording: the result is "
           "Int[x = b .. a] -(f), not -(Int[x = b .. a] f). Reason: ftc acts "
           "on a top-level Int, and on -(Int ...) it would refuse "
           "'ftc-no-integral', so the owner's aim, ftc running after the "
           "flip, needs either this form or a position argument for ftc; "
           "this form is E46's identity (§5.1 composed with pointwise "
           "linearity), already in the rule table, so it adds a move and no "
           "theorem. The move owes no orientation of its own: the identity "
           "holds whatever the order of a and b. The new integral's formers "
           "are charged as a new term's, with E4's orientation when a key "
           "uses its range; for the intended use, a reversed symbolic range, "
           "that orientation is the true one. Limitation, stated: a goal "
           "whose reversed symbolic integral owes a former cannot be "
           "installed (E4 owes lo <= hi at installation, which F2 refuses), "
           "so int_flip reaches only reversed integrals whose bodies owe "
           "nothing (owner question)"
           ". Owner's answers, 2026-09-24: the form Int[x = b .. a] "
           "-(f) is ACCEPTED, being the same identity as -(Int[x = b .. "
           "a] f) and keeping ftc applicable; and the limitation is "
           "removed by E56, which builds every range from the order "
           "discharge proves, so a reversed symbolic integral whose body "
           "owes a former now installs, and flipping an oriented one is "
           "no longer refused",
    "E52": "P1.1-sheet joins PROOFS and becomes ROUTE['P1.1'] (the owner's "
           "E47, carried out): its tables merge into PROOFS and the "
           "DISCHARGE_* tables, it leaves INT_SUBST_PROOFS, and every child "
           "that runs PROOFS runs it (P1_1_SHEET_JOIN). Re-traced by hand "
           "against all 5 PLANTED_BUGS, 13 DISCHARGE_NEW_PLANTED_BUGS and 30 "
           "DEFINEDNESS_MUTATIONS (P1_1_SHEET_TRACES): N stays 5 except "
           "farkas_swaps_interval_ends (7), and pi_pos_not_in_constraint_set, "
           "search_scales_wrongly and sqrt_open_at_0 refuse it (at s1, s1 "
           "and installation); four more bugs gain a catch in it. P1.1, the "
           "t-form, stays in PROOFS as the proof of its own goal",
    "E53": "the sign product closes non-strict goals (§5.3 method 5, "
           "WHAT.md's consolidation item): factors may be '>=' or '<=' under "
           "a non-strict target, never under a strict one, with the same "
           "identity, parity and children checks (SIGN_PRODUCT_"
           "NONSTRICT_RULE). Soundness: each factor holds its certified sign "
           "where the terms are defined, so the product's sign follows from "
           "the parity, zero included. 1 - x^2 >= 0 @ [0, 1] is "
           "-(x - 1)(x + 1). Changes: DISCHARGE_MUST_REJECT "
           "product_nonstrict_target's reason, and cos_theta_canonical's "
           "two none admissions become discharged (CONSOLIDATION_CHANGES)",
    "E54": "six entries (CONSOLIDATION_ENTRIES): pyth as the owner states "
           "it, (sin u)^2 + (cos u)^2 == 1, and pyth_cos, (cos u)^2 == 1 - "
           "(sin u)^2, its solved form, which a rewrite (tree match at "
           "(cos b)^2) and field (§6.2's a^k == r) can use and which differs "
           "from pyth by a ring identity; the owner's cos sign fact, "
           "cos_nonneg_on : cos u >= 0 @ u >= 0, u <= pi/2, and "
           "sin_nonneg_on : sin u >= 0 @ u >= 0, u <= pi, both read by cite "
           "only, since their hypotheses are real conditions and a Farkas "
           "label has no children; and cos_le_one, cos_ge_neg_one, total "
           "bounds read by the linear method per cos atom, as sqrt_nonneg "
           "is (ATOM_FACT_RULE). E27 (a) counts pyth, not pyth_cos; none is "
           "an exact value. No existing expectation changes by them except "
           "through E53's cos_theta_canonical key",
    "E55": "Int_0^1 sqrt(1 - x^2) = pi/4 by x := cos theta (problems/stage0 "
           "QC1) needs exactly E53 (installation's 1 - x^2 >= 0, and after "
           "the flip 1 - (cos theta)^2 >= 0 as -(cos theta - 1)(cos theta + "
           "1) with cos_le_one and cos_ge_neg_one), pyth_cos twice (a "
           "rewrite turning sqrt(1 - (cos theta)^2) into sqrt(1 - (1 - "
           "(sin theta)^2)), which sqrt_sq then matches by ring_nf, and a "
           "field fact for ftc's check, whose F' holds cos theta^2), and "
           "sin_nonneg_on for sqrt_sq's sin theta >= 0 on [0, pi/2]. NO "
           "extension of field is needed: §6.2 already takes facts a^k == "
           "P/Q with the right side free of fact atoms, and pyth_cos is "
           "one. Nothing large (no trig_norm) is needed. The owner's cos "
           "sign fact is not used by this route (x := sin theta would use "
           "it), and is pinned as asked",
    # consolidation spec 2026-09-24, owner answers
    "E56": "reversed ranges everywhere (owner's answer 2, 2026-09-24, the "
           "main session's recommendation): wherever the kernel builds an "
           "interval from an Int's limits a (lo) and b (hi) - installation's "
           "and every new goal's formers, rewrite's position domain, ftc's "
           "premises and its (a, b), int_subst's old and new ranges, "
           "int_flip's new range, and so every key discharge reads a range "
           "constraint from - two rational literals are ordered by "
           "norm_num as today, an infinite end as today, and otherwise the "
           "kernel puts lo <= hi, then hi <= lo, to DISCHARGE_RULE steps "
           "(3)-(5) at the Int's position domain, with no refutation: the "
           "first discharged is emitted (source orient, as the E4 key was) "
           "and the interval is [lo, hi] or [hi, lo] accordingly, with "
           "nothing further owed about order; if neither is discharged the "
           "step is refused 'orientation-undecided', one code for every "
           "step, replacing int_subst's 'int-subst-orientation-undecided' "
           "(same template, {lo} and {hi}). Supersedes E4's 'otherwise the "
           "step emits lo <= hi' (a false one was refused by F2, an "
           "undecided one admitted) and E46's decision rule; int_subst "
           "keeps its flipped form, now a choice rather than a necessity. "
           "Soundness: §5.1's exploit was a constraint set that assumed "
           "a <= b when b < a, so the range was empty and every obligation "
           "on it vacuous. A proved order cannot be wrong (its certificate "
           "is checked), so the interval built is exactly the set of points "
           "between the limits and is never empty. An Int's value (§5.1: "
           "Int_a^b = -Int_b^a) and its definedness depend only on the "
           "integrand on that set, so every former, hypothesis and premise "
           "stated on it is the right one for either order; ftc's "
           "F(b) - F(a) holds for either order (for b < a, Int_a^b f = "
           "-(F(a) - F(b))), with its premises on [min, max] and (min, "
           "max); rewriting under an Int needs only the range set (§6.1); "
           "int_subst's premises are on the closed interval between its "
           "limits. Equal limits make either order provable and the same "
           "point. The order key is still emitted, discharged, so what a "
           "proof relied on stays in its tracker. Changes: E56_CHANGES"
           ". Amended by the consolidation review (main session, "
           "2026-09-24; E56_AMENDMENTS): (1) every interval in every "
           "emitted key's domain is one E56 decided, the enclosing Ints' "
           "ranges in a position domain P included, so int_subst (and "
           "every move emitting at P) refuses 'orientation-undecided' "
           "naming an enclosing range whose order no discharge proves; "
           "(2) the order is decided lazily, only when a key whose domain "
           "holds that interval is emitted, and each decision is memoised "
           "per key; the semantics are unchanged",
    # consolidation review 2026-09-24
    "E57": "rewrite refuses 'Int-or-D-not-normalisable' when any inst value "
           "or the target `at` holds an Int or D node, on every match "
           "branch, the tree match of a non-App left side included (main "
           "session's decision, soundness, 2026-09-24). The skeptic's "
           "blocker: pyth's left side is a sum, so the tree branch skipped "
           "step 3's ring_nf, whose E26 (b) refusal is what stopped trees "
           "in inst values, and pyth is the first equation entry whose "
           "right side drops its schema variable; (sin(D[x](abs x)))^2 + "
           "(cos(D[x](abs x)))^2 rewrote to 1 with nothing owed and closed "
           "'Proved.', though abs' does not exist at 0 (and likewise "
           "u := Int[x = 1 .. oo] 1, divergent). The principle: NO RULE MAY "
           "ERASE AN Int OR D NODE UNLESS ITS DEFINEDNESS IS OWED; until "
           "§18 Q23's formers land that means never, except where the "
           "rule's own premises owe it. E57_PRINCIPLE checks every move "
           "against it"
           ". Amended by the second review (main session, 2026-09-24): "
           "ftc, int_subst and int_flip refuse 'Int-or-D-not-normalisable' "
           "when a limit of the Int they act on (or int_subst's new limit) "
           "holds an Int or D node, before any orientation is decided "
           "(SECOND_REVIEW_RULE); until then ftc reached "
           "'orientation-undecided' only because norm_num refused the key "
           "inside the order decision",
    # second review 2026-09-24
    "E58": "0^0 is 1 (main session's decision, 2026-09-24): Pow(u, 0), the "
           "integer exponent 0, denotes 1 for every base, 0 included. It is "
           "the convention ring already implements (u^0 normalises to the "
           "constant 1, an integer power being repeated multiplication, the "
           "empty product 1), and the one that keeps ring_nf a sound "
           "identity over every assignment of the atoms. RPow (a real "
           "exponent) is untouched: it owes base > 0 (§5.1). A limit of the "
           "form 0^0 is §6.7's business, a question about a limit, not "
           "about a term's value. deriv still refuses n == 0 (E12: d_pow_int "
           "checks n != 0 on the literal), which is incompleteness, not "
           "unsoundness. Pinned by E58_ACCEPTS; for GRAMMAR.md and DESIGN.md "
           "§5.1 to state (the main session edits them)",
    # regularity spec 2026-09-24 (section 17). Decisions marked 'main
    # session, delegated by the owner 2026-09-24' were open questions the
    # owner delegated; each takes the sound, minimal option.
    "E59": "what e in C^k(D) means (§5.2, §6.4, §6.9; main session, "
           "delegated by the owner 2026-09-24). k is 0 or 1; C^2 and up and "
           "C^omega are not built (REG_CHECK_RULE rejects them). S is the "
           "set of points, over all the judgement's free variables, where "
           "every item of D holds. C^0(D): e is defined at every point of S "
           "and continuous on S (relative topology). C^1(D): every point of "
           "S has an open neighbourhood on which e is defined and "
           "continuously differentiable, jointly in the free variables. No "
           "variable is distinguished: joint regularity implies regularity "
           "in the integration variable with the others fixed, which is "
           "what ftc, int_subst and the Int and D formers use, and every "
           "closure rule of REG_RULES proves joint regularity. Open and "
           "closed intervals are the domain's own business: ftc's C^1 "
           "premise sits on the open (a, b), so sqrt's C^1 side u > 0 is "
           "only asked inside; its C^0 premises and int_subst's premises sit "
           "on the closed range. On a closed range the neighbourhood reading "
           "of C^1 is stronger than §6.4's one-sided C^1([a, b]) and "
           "sufficient for it; its cost is completeness only (x := t*sqrt t "
           "over [0, 1], which deriv's d_sqrt refuses first anyway, "
           "REG_NOT_COVERED). Reason: the one reading under which every rule "
           "is a textbook theorem with its side condition stated pointwise "
           "on D, so each side is an ordinary §5.2 obligation at D",
    "E60": "regularity is a discharge method for Reg keys (§5.3's list "
           "extended, §6.9, §15.2 item 5; WHAT.md 'Start here'). The "
           "untrusted search proposes a derivation by term structure "
           "(REG_CERTIFICATE), the trusted checker in discharge.py checks "
           "it rule by rule (REG_CHECK_RULE), and each side condition is an "
           "ordinary obligation at D decided by discharge's own checkers, "
           "never refuted. At emission a Reg now goes through "
           "REG_DISCHARGE_ORDER in place of DISCHARGE_RULE's step (2): "
           "certificate, then E63's decided-false, then admission with "
           "REASON_NONE (tag none) or REASON_REJECTED (tag reg). "
           "REASON_REG ('regularity not built') is retired. Status is still "
           "decided once, at emission (E32): a Reg's verdict reads only the "
           "key, ENTRIES and the natural-domain table. §6.9's rejection of "
           "'a reflective procedure inside the trusted base' is respected: "
           "the checker decides nothing, it checks one rule instance per "
           "node against a table, which is exactly §14's 'rule table as "
           "data, a rule's condition one datum'",
    "E61": "the rules (REG_RULES), the C^0/C^1 subset ftc and int_subst "
           "need (§6.9, WHAT.md). Structural: const (Num, pi, e_const), var "
           "(any variable), neg, add, mul, div (side b # 0), pow (n >= 0), "
           "pow_neg (n < 0, side a # 0), rpow (side a > 0, both children), "
           "and one rule per builtin applied to one argument. The C^0 sides "
           "of a builtin ARE its row of E26's natural-domain table "
           "(kernel.NATURAL_DOMAINS today), read by the checker, never "
           "transcribed (§6.9: 'the C^0 sets above are exactly the domains "
           "§5.1's partial formers owe'; §14 item 2). The C^1 sides are the "
           "same row with every >= made > and every <= made < (the "
           "interior), plus REG_C1_EXTRA's one row, abs: u # 0. So sqrt is "
           "C^0 on u >= 0 and C^1 on u > 0, ln on u > 0, tan on cos u # 0, "
           "asin/acos C^0 on [-1, 1] and C^1 on (-1, 1), atanh on (-1, 1), "
           "acosh C^0 on u >= 1 and C^1 on u > 1, abs C^0 everywhere and C^1 "
           "where u # 0, and exp, sin, cos, atan, sinh, cosh, tanh, asinh "
           "everywhere. No rule, so no derivation (REG_NOT_COVERED): a "
           "declared symbol (§6.9's hypothesis form waits for §12.1), an Int "
           "node (FTC-1 and Leibniz), a D node (C^2), an MVar",
    "E62": "soundness, per rule (REG_SOUNDNESS; §14 (A)): each rule is a "
           "standard theorem of real analysis, stated with its hypotheses "
           "as the side conditions at D, in E59's reading. Continuity is "
           "preserved by sums, products, quotients where the divisor is "
           "nonzero and composition with a function continuous on a set "
           "containing the inner values (relative topology); each builtin "
           "is continuous on its natural domain. C^1 near a point is "
           "preserved likewise, with the chain rule, because each strict "
           "side condition holds at the point of S and so, by continuity, "
           "on a neighbourhood; each builtin is C^1 (indeed analytic) on the "
           "interior of its natural domain, except abs at 0",
    "E63": "decided false for a Reg (§18 Q22 extended; untrusted, beside "
           "F1-F3, E33): a Reg is refused 'obligation-decided-false' when "
           "one of the C^0 sides of its derivation (REG_RULES at every node "
           "that has a rule, not descending into one that has none), at its "
           "domain, is decided false by F1, F2 or F3. The C^0 sides are "
           "exactly the term's definedness conditions (every '/', negative "
           "power, real power and partial builtin), and a term undefined at "
           "a point of S is C^k on D for no k. The C^1-only sides (sqrt's "
           "u > 0, abs's u # 0, the strict ends) never refute: sqrt x is "
           "not C^1 at 0, but x*abs x is C^1 though its abs fails u # 0, "
           "so failing a sufficient condition decides nothing. Message "
           "DECIDED_FALSE_MESSAGES_REG['reg_undefined']. This is what "
           "refuses the FTC-across-a-pole integrand by regularity as well "
           "as by its former (REG_BAD_MOVES, REG_PLANTED_BUGS "
           "former_div_dropped)"
           ". Amended by the regularity review (main session, delegated by "
           "the owner 2026-09-25): a Reg whose domain is empty is still "
           "refused when a CLOSED side is decided false, since E5 keys a "
           "closed side at domain true: sqrt(-1) + x in C^0(x > 1, x < 0) "
           "is refused through -1 >= 0, though vacuously true. Intended: "
           "it is E7's treatment of a closed former (sqrt(-1) owes -1 >= 0 "
           "wherever it enters, whatever the domain), no move emits a Reg on "
           "an empty domain (every range is built from a proved order, E56, "
           "and a goal's own domain is the learner's), and the cost is only "
           "a refusal (REG_REVIEW_DECIDED_FALSE)",
    "E64": "§18 Q23's formers (the owner's option A, settled; the shapes "
           "decided by the main session, delegated by the owner "
           "2026-09-24). An Int node is STATABLE when neither limit is oo "
           "or -oo and neither holds an Int or D node. A statable "
           "Int[x = a .. b] f owes Reg(f, 0, P + I): f in C^0 on its "
           "closed range I, built by E56 from the order discharge proves, "
           "at the node's position domain P. Continuity on a closed "
           "bounded interval implies Riemann integrability, so this is the "
           "sufficient, statable form of 'f integrable on [a, b]', and it "
           "is exactly ftc's f premise, so a top-level integral's former "
           "and ftc's ftc_f_C0 are one key. D[x] e owes Reg(e, 1, P) at its "
           "position domain (D10: x is free in the node, and P is where it "
           "is evaluated), which implies e differentiable at x at every "
           "point of P. Source 'former'. They are charged wherever a term "
           "enters (installation, a rewrite's R, a new goal, int_subst's "
           "and int_flip's new integral, a fact's inst values), AFTER every "
           "E6/E26 former of the entering term, in pre-order among "
           "themselves, so no existing refusal changes its cause. An "
           "unstatable Int owes nothing and stays what E26 (b) made it "
           "(E65). A rewrite under an Int does not recharge the enclosing "
           "Int: the rewrite proves old body == new body on the range, so "
           "the new integrand is integrable where the old one was owed to "
           "be (§6.1's congruence), and ftc emits its own f premise on the "
           "new body anyway",
    "E65": "improper integrals and `diverges` are deferred, not in this step "
           "(main session, delegated by the owner 2026-09-24). An Int with "
           "an infinite limit owes convergence, and convergence is not "
           "C^0: 1/x is C^0 on [1, oo) and its integral diverges, so "
           "stating it as a Reg would be unsound. conv and diverges are "
           "§5.2 judgements the grammar defers (GRAMMAR.md D2), with their "
           "own rules (§6.4's div_limit, div_compare, div_power, div_pole, "
           "and int_improper) and no stage-1 target needs them; they come "
           "with int_improper, whose target is readiness P5. Until then an "
           "unstatable Int is refused exactly as now by ring, field and "
           "norm_num (E26 (b)), E57 refuses erasing it, and ftc, int_subst "
           "and int_flip refuse acting on it (E9, E36, SECOND_REVIEW_RULE). "
           "Consequence, a DESIGN.md §18 Q23 conflict to fold in: Q23's "
           "second case (I = Int_1^oo 1/x, I - I == 0) stops at the "
           "blanket refusal, not yet at 'the owed 1/x integrable on "
           "[1, oo), which is false'",
    "E66": "how E26 (b) and E57 change (Q23: 'from then on ring and field "
           "read each one as an ordinary atom'). (1) ring and field "
           "(every entry point: rewrite's match, E25's divisor test, field's "
           "divisor test and facts, the moves' checks, the exact values, the "
           "certificate checkers) read a statable Int and every D node as an "
           "opaque atom, identified by its tree exactly (no alpha "
           "equivalence and no normalisation under the binder: incomplete, "
           "never unsound). An unstatable Int is still refused "
           "'Int-or-D-not-normalisable'. (2) UNCHANGED: E7's refusal of an "
           "obligation holding any Int or D node, install's hypothesis gate, "
           "and deriv's d_const guard (main session, delegated by the owner "
           "2026-09-24). Reason: none of them is needed by a target; each "
           "keeps Int and D atoms out of discharge's search and refutation, "
           "whose point evaluation cannot read them (terms.subst refuses "
           "under D); and an F holding one could never have its Reg "
           "premises certified (E61), so deriv's refusal says so at once. "
           "(3) E57's step 2a refuses only an unstatable Int in an inst "
           "value or the target: a statable Int or a D node in the target "
           "was owed where it entered, and R's are now charged at step 10 "
           "(E64), so the principle 'no rule erases an Int or D node unless "
           "its definedness is owed' holds by the owing. REWRITE_RULE step "
           "9 (a) counts a Reg charged from R that mentions x as not open. "
           "(4) SECOND_REVIEW_RULE unchanged. The pyth reproducers: "
           "u := D[x](abs x) is now accepted and closes 'Proved modulo 1 "
           "admissions', owing the false abs x in C^1(true), admitted none; "
           "u := Int[x = 1 .. oo] 1 is still refused",
    "E67": "int_parts is out of this step (main session, delegated by the "
           "owner 2026-09-24): it is §6.4's rule 'around ftc', not one of "
           "stage 1's four pieces, and it needs its own premises (u and v "
           "in C^1 on the range) and its own spec; what Q23 needs of THIS "
           "step is that the integral is an atom whose definedness is owed "
           "and discharged, so the solve-for-I algebra is ring's. "
           "REG_Q23_CASES shows it on I = Int[x = 0 .. pi] exp x * sin x: "
           "2*I - I - I closes to 0, and ((exp pi + 1) - I + I)/2, the "
           "goal an int_parts step would leave, closes to (exp pi + 1)/2, "
           "each a plain 'Proved.' with I's integrability discharged",
    "E68": "every statable Int's order is now decided when it enters, "
           "because its own former uses its range (E56 unchanged; its "
           "laziness no longer spares any statable Int). A goal whose Int "
           "has an undecided symbolic order and a body that owes nothing, "
           "which used to install, is now refused 'orientation-undecided' "
           "at installation. E56_REVIEW_CASES lazy_unused_range_installs "
           "now decides 0 <= (a - 1)^40; E56_TIMING_BOUND stays (main "
           "session, delegated by the owner 2026-09-24), and the untrusted "
           "search must fail the first attempt, (a - 1)^40 <= 0, within it. "
           "The committed search takes 29.7 s on the equivalent "
           "Int[x = (a-1)^40 .. 0] sqrt(x^2) (measured 2026-09-24), so the "
           "build must make that failure cheap; any bound it puts on the "
           "search can only cost admissions, never a discharge (E28), and "
           "must leave every expectation in both data files unchanged",
    "E69": "verdicts: with regularity every proof in PROOFS and every "
           "problem-file proof reads 'Proved.' (REG_VERDICTS, problems "
           "REG_VERDICTS), none with an admission, so the no-none assertion "
           "over PROOFS runs is kept. N catches of planted bugs that relied "
           "on an admitted Reg key (tracker_drops_one) now rely on the "
           "tracker comparison alone; FORGERIES' two admission-bearing "
           "cases move to a finished state that still has one "
           "(REG_FORGERY_STATE)",
    "E70": "staging (REG_SWITCH, the discharge precedent E34): two commits, "
           "the checker and search with item D first, then the wiring, the "
           "formers and the atoms with every asserted table switched by one "
           "constant in proof_of_life.py. Nothing in section 17 is asserted "
           "until then",
}

DESIGN_DEFECTS = [
    "§6.4 ftc does not require a <= b. With b < a the intervals [a, b] and "
    "(a, b) are empty, all four premises are vacuous, and ftc proves "
    "Int[x = 1 .. -1] 1/x^2 == 2, which diverges. Rewriting under Int "
    "(§6.1) has the same hole, and §5.3 method 2 is where it is patched. "
    "Either the rules state their intervals between min(a, b) and max(a, b) "
    "with the order established, or they emit a <= b. E4 does the latter.",
    "§6.1 rev 9 allows rewriting under D[x] only on 'open domain (strict "
    "inequalities only)', but §6.3 rev 7 routes D[x](u / v) through "
    "u / v == u * (1/v) by field, which holds @ v # 0. That is a # 0 item, "
    "not a strict inequality. Read literally, rev 9 forbids the routing "
    "whenever v mentions x, so D[x](x/(x + 1)) has no route. E11 counts "
    "# 0 as open and allows items that do not mention x. The reason: for a "
    "term continuous on an open domain, the set where it is > 0, < 0 or "
    "# 0 is open, and under the partial reading a term's domain is open "
    "when every partial former in it has an open natural domain ('/', "
    "negative integer powers, ln, tan, atanh and RPow do; sqrt, asin, acos "
    "and acosh do not). §6.1 rev 9's own 'strict inequalities only' has "
    "the same hole: a strict inequality over a term involving sqrt of x "
    "can hold on a closed set (sqrt x + 1 > 0 holds exactly on [0, oo)). So "
    "§6.1 needs to say 'open truth set', not 'strict', and needs a rule "
    "for when a syntactic item has one; E11 (a) is this milestone's rule. "
    "§6.1 also does not say that the domain includes the ranges of Ints "
    "between the D[x] and the position, which E4 makes closed; E11 (b) "
    "covers them.",
    "§11.2's obligation block mixes sources and domains. '1 + x > 0 @ [0,1]' "
    "is ln's definedness former on F's closed [0, 1] (E26), which is also "
    "the regularity sub-obligation; deriv's d_ln gives the separate key "
    "1 + x > 0 @ (0, 1). 'x^2 - x + 1 > 0' has no domain, and is owed twice, "
    "by ln's former on [0, 1] and by d_ln on (0, 1). field's divisors "
    "1 + x, x^2 - x + 1 and 1 + x^3 on (0, 1) are not listed. Only the atan "
    "denominator is.",
    "§11.1 displays sqrt_sq's obligation as '0 ≤ t', while §6.8 states it "
    "as t ≥ 0. Under GRAMMAR.md D12 those are different keys. §6.8 also "
    "names the schema variable t, the same name as §11.1's bound variable, "
    "which hides the instantiation §15.2 item 3 says is trusted.",
    "§6.2's 'division by anything else is itself an opaque atom' does not "
    "say whether the atom is a/d or 1/d. Matching atan_odd against "
    "atan((2*0 - 1)/sqrt 3) works only if a/d is a * inv(d) (E3, the "
    "spike's reading).",
    "§5.1 says '/' carries a nonvanishing obligation, but nothing says when "
    "it is charged: at goal statement, at use, or only when field sees it. "
    "E6 charges it on entry.",
    "WHAT.md counts only literal divisors as discharged by norm_num, but "
    "the milestone also emits literal non-divisor obligations: 3 >= 0 from "
    "sqrt_sq_val 3, and 0 >= 0 from sqrt_sq at u := 0. E7 closes them the "
    "same way.",
    "WHAT.md Done-when item 1 accepts (1/3)*ln 2 + pi*sqrt 3/9 but does not "
    "say how it closes. It needs close by field [sqrt_sq_val 3] (§8.7), and "
    "it owes no 3*sqrt 3 # 0, so its N differs from the main form's.",
    "§5.1 lists D[x] among the binders, but §6.4's `D[x] F ≐ f @ (a, b)` "
    "needs x free (the domain constrains it). D[x] e binds x inside e and "
    "evaluates the derivative at x, so fv(D[x] e) = fv(e) ∪ {x} and D is "
    "not alpha-convertible (GRAMMAR.md D10). §6.3 d_const's 'x not free in "
    "e' uses the inner, bound reading. §5.1 should say D[x] both binds and "
    "evaluates. Substitution on D (§15.2 item 1) must then be defined, as "
    "in GRAMMAR.md §5; deriv refuses a Deriv with x free (E12), so ftc "
    "never needs more than its unchanged case (E9).",
    "§5.3 method 5 requires a factorisation into strictly lower-degree "
    "factors, but §11.2 tags 3*sqrt 3 # 0 'by product (sqrt_pos)', and the "
    "fallback's 2*sqrt x # 0 needs the same move. Ring-normalised, these "
    "are 3·s and 2·a, degree 1 in their atom. The only split is a rational "
    "content times the atom, and the atom's factor has the same degree, so "
    "neither the precondition nor the termination argument applies as "
    "written. No other method reaches them alone: cite gives sqrt a > 0, "
    "not c*sqrt a # 0, and sqrt_pos is not in method 3's automatic "
    "constraint set. E18 reads method 5 as also allowing a nonzero rational "
    "content to be split off: c·p with c ∈ ℚ∖{0}. For # 0 the goal then "
    "follows from p # 0. For > 0 or < 0 it follows from p's sign and c's "
    "sign, where c's sign is decided by norm_num. This step needs no degree "
    "drop and terminates because the content is a literal. p then goes "
    "back through the list, here to method 6 (cite sqrt_pos, with its "
    "hypothesis a > 0 emitted: 3 > 0 by norm_num, x > 0 by range on "
    "(0, pi^2/4)). §5.3 should state this case.",
    "§5.3 method 4 calls its witness a positivity witness: a sum of even "
    "powers plus a positive rational, or for a quadratic a positive leading "
    "coefficient and a negative discriminant. Both forms are strict. It "
    "does not say whether it closes non-strict `>= 0` goals. The fallback's "
    "range orientation 0 <= pi^2/4 (E4) ring-normalises to (1/4)*pi^2, with "
    "constant 0 and discriminant 0, so neither form applies. No other "
    "method reaches it: pi^2 is not linear for method 3, method 5 closes "
    "only `>`, `<` and `#`, and no §6.8 entry states it. E20 reads method 4 "
    "as also accepting a non-negative rational constant, zero included, "
    "when the goal is `>= 0`: a non-negative combination of even powers is "
    "`>= 0`, and ring re-checks the decomposition as before. §5.3 should "
    "state this case.",
    "§5.1 gives '/', negative integer powers and real powers a definedness "
    "obligation, but not ln, sqrt, tan, asin, acos, acosh or atanh, and "
    "§6.2 makes all of these, with Int and D, opaque atoms that ring and "
    "field cancel freely. So 0*ln(-1) == ?A and tan(pi/2) - tan(pi/2) == ?A "
    "closed by ring as 'Proved.' with nothing owed: a false Proved under the "
    "partial reading that §6.1 rev 9 and REWRITE_RULE step 5 rely on. §14 "
    "says the total and partial readings 'coincide, because those rules "
    "carry their definedness conditions on the source side' (the claim "
    "PROOF_OF_LIFE.md cites as §15.4), and that depends on every partial "
    "former carrying its condition. §15.4 names the class: a side condition "
    "missing from the rule table is missing from the falsifier bank "
    "generated from it too. The design meant these conditions: §11.1 lists "
    "t^2 >= 0, and §11.2 lists 1 + x > 0 @ [0,1] and x^2 - x + 1 > 0. "
    "Resolved by E26 (user decision 2026-09-24): each partial builtin is a "
    "former owing its §6.9 C^0 domain, and ring, field and norm_num refuse "
    "Int and D, which have no statable condition until regularity and "
    "diverges exist. §5.1 should list each builtin's condition beside it, "
    "as it does for '/', and §6.2 should say that Int and D are not atoms.",
    # Added by user decision 2026-09-24 (evaluated answers).
    "§9's `closed` schema is a node whitelist only, so after ftc the goal's "
    "own F(b) - F(a) is itself a closed value, and closing with it is refl "
    "through ring: the vacuity §9 exists to remove returns one step later. "
    "S2 and S3 closed that way with no §6.8 entry (problems/stage0 FINDINGS "
    "12), and P1.1 would at s2 (BAD_MOVES e27_goal_lhs_after_ftc). §6.8's "
    "'every authored goal terminates in this table' was enforced by "
    "nothing. Resolved by E27: a closed value must be fully evaluated, a "
    "property (no entry in force still applies to a subterm, matched as "
    "rewrite matches; no unreduced literal arithmetic), checked untrusted "
    "beside the whitelist and last in close. §9 should state the "
    "requirement and where it runs; §6.8 should say its claim now holds of "
    "every accepted close relative to the entries in force, and that a new "
    "schema entry states its E27 reading; §16.3's refusal shape should say "
    "that 'close-not-evaluated' carries the offending subterm as its "
    "residual.",
    # Added by the discharge spec 2026-09-24 (section 11, E28-E34).
    "§17 excludes 'Fourier–Motzkin with its Farkas witnesses' from stage 1, "
    "'replaced by hypothesis closure, by-range, sign certificates and "
    "simple interval propagation', and lists FM under stage 4; §5.3 method "
    "3 and WHAT.md's stage-1 list both have FM with its witness. The owner "
    "decided on 2026-09-24 for §5.3: FM with a checked Farkas witness is in "
    "stage 1 and no interval propagation is built (E29). §17's exclusion "
    "list and its stage-4 row should drop FM, and should say why: the "
    "proof-of-life needs the linear tag (0 <= pi/2, 1 <= e_const), the "
    "search already exists untrusted in the tagger, and the trusted check "
    "is smaller than interval propagation would be.",
    "§15.2 item 5 lists as trusted 'method 1's reflexive-transitive "
    "closure ..., method 2's by-range extension, and the satisfiability "
    "check'. Under E28-E29 method 2 is a Farkas certificate over the "
    "range's own items, checked like method 3, and the pre-check runs in "
    "the untrusted search, since its verdict can only withhold a discharge "
    "(DISCHARGE_RULE, the pre-check paragraph). Item 5 should read: the "
    "tracker, the certificate checkers (hyp, Farkas, sign, sign product, "
    "cite) and the exact-value rewrite (E31, which uses item 3's matcher "
    "and item 7's entries). §15.2's list of untrusted code the kernel "
    "calls should add the decided-false check (E33), which can only "
    "refuse, beside the E27 check.",
    "§5.3's paragraph 'Before Fourier–Motzkin is consulted, the constraint "
    "set is checked satisfiable. This closes a class ...' places soundness "
    "in the pre-check. With checked witnesses the class is closed by the "
    "certificate check (an accepted witness proves the key on its domain, "
    "vacuously if empty) together with E4, which owes a range's "
    "non-emptiness as lo <= hi. The pre-check stays, by the owner's "
    "decision, as what keeps the search from reaching for a vacuous "
    "witness, and the checker demands a positive multiplier on the "
    "negated goal. §5.3 should say which carries what.",
    "§5.3 method 5 states 'strictly lower-degree factors' as a condition of "
    "the method; method 4 states 'for a quadratic, positive leading "
    "coefficient and negative discriminant'. Both are search rules, not "
    "checks: the checker needs ring_equal of the factorisation (or of the "
    "completed square) and the factors' signs, and terminates on a finite "
    "certificate (E30). §5.3 should separate what the search tries from "
    "what the kernel checks, as it already does for the factorisation's "
    "source.",
    "§5.4's revision-10 note says the kernel admits what it cannot "
    "discharge 'with the reason discharge not built'. After discharge the "
    "reasons are 'regularity not built', 'no method decides it', 'domain "
    "inconsistent' and 'certificate not accepted' (E32), and an obligation "
    "discharge decides false refuses the step instead of being admitted "
    "(E33). §5.4 should list the reasons and say that an admission tagged "
    "none may still be false (x - 5 # 0 @ [0, oo), DISCHARGE_UNDECIDED).",
    "§18 Q22's settlement names the exact-value route (cos(pi/2) # 0 to "
    "0 # 0). E33 also decides false a closed ordering whose negation is "
    "discharged (the reversed range's pi/2 <= 0, which DOMAIN_RULES E4 "
    "already said would be 'refused once discharge exists') and an "
    "obligation with a free variable at a rational counter-point. The "
    "second follows from Q22's text; the third extends it, and makes a "
    "goal with no stated domain whose terms are undefined somewhere (ln x "
    "* 0 == ?A; E4's 0 <= x for Int[t = 0 .. x]) refused rather than "
    "admitted. The owner settled the full reading on 2026-09-24 (E35 "
    "(1)); Q22 should record it.",
    # int_subst spec 2026-09-24
    "§5.1 says reversed limits are 'normal output of int_subst with a "
    "decreasing phi - x = a cos theta is the canonical case'. Under E4 and "
    "discharge only literal-ended reversed output survives: a non-literal "
    "reversed range owes lo <= hi, which F2 decides false, so x = a*cos "
    "theta over [pi/2, 0] is refused at the int_subst step itself (E40). "
    "§5.1 and §6.4 should say how a decreasing phi with symbolic ends is "
    "handled (a flipped conclusion, or an orient argument), or that it is "
    "not. (Owner answers 2026-09-24, E46: resolved in the kernel by the "
    "flipped form Int[t = hi .. lo] -(...) when discharge proves hi <= lo, "
    "and 'int-subst-orientation-undecided' when it proves neither order; "
    "§5.1 and §6.4 should state both, and that literal ends are kept.)",
    "§8.1 shows `step subst (x := sin t) over t in [0, pi/2]` on P1.1's "
    "goal as '✓ legal' with no progress. Its upper endpoint equation is "
    "sin(pi/2) == pi^2/4, i.e. 1 == 2.467..., false, and no t has sin t = "
    "pi^2/4 since sin <= 1; the kernel refuses it "
    "'int-subst-endpoint-mismatch' (INT_SUBST_BAD_MOVES "
    "sin_guess_from_8_1). §8.6's probe prints 1.3012779 for the same "
    "guess; with the range the example gives, the transformed integral "
    "is Int_0^1 sin(sqrt x) = 2 sin 1 - 2 cos 1 = 0.6023... (SymPy). A "
    "legal, no-progress guess would be x := (pi^2/4)*sin t over [0, pi/2], "
    "whose ends map by sin_zero and sin_pi_half.",
    "§8.5's chain-rule row f'(x)*g(f(x)) -> u = f(x), 'the commonest "
    "substitution there is', is a reverse substitution, and §6.4 and §8.4 "
    "state only the forward move x := phi(t). Its forward emulation for "
    "S2, x := sqrt u, is refused because sqrt is not C^1 at 0 (E37). So "
    "the row names a move the rule table does not have; ftc closes those "
    "integrals directly (STAGE0.md gap 5), and the owner should decide "
    "whether a reverse move is wanted. (Owner answers 2026-09-24, E45: "
    "reverse substitution is in, as int_subst's reverse mode; §6.4 should "
    "state the reverse reading with its checked link body == "
    "f(g(x))*g'(x), and §8.4's substitution row should list what the "
    "learner supplies in each mode.)",
    # int_subst spec 2026-09-24, owner answers
    "§5.3 method 2-3's sign facts are 'each named constant' (rev 9). By "
    "the owner's decision (E49) each sqrt atom of a key brings sqrt_nonneg "
    "the same way, with no child obligation because a certificate claims "
    "its key only where the key's terms are defined; §5.3 and §6.8 should "
    "say so. It is what closes 1 + sqrt x # 0, the divisor §8.5's 'kill "
    "the root' row meets before any substitution.",
    "§6.1 and §6.4 state int_subst on a whole goal. By the owner's "
    "decision (E48) it acts at a position, selected as rewrite selects, "
    "with rewrite's congruence and its step-9 restriction under D[y]; "
    "§6.4 should say so, and that the default without a position is "
    "exactly one integral over var, not E2's every occurrence.",
    "§5.1's canonical example is only half served: the owner's ∫_0^1 "
    "sqrt(1 - x^2) with x = cos theta over [pi/2, 0] is now accepted as a "
    "move (INT_SUBST_ACCEPTS cos_theta_canonical), but the goal still "
    "installs owing 1 - x^2 >= 0 @ [0, 1] tagged none (sign product never "
    "closes a non-strict goal, STAGE0.md S8), and the new integrand owes "
    "1 - (cos theta)^2 >= 0, also none, and needs pyth and a sign fact for "
    "cos on [0, pi/2] to finish. Neither gap is the substitution's. "
    "(Consolidation spec 2026-09-24: both closed, by E53's non-strict sign "
    "product with cos_le_one and cos_ge_neg_one; the goal finishes as "
    "problems/stage0 QC1, E55.)",
    "§11.1 writes the endpoint obligation as one line, '0^2 = 0 ∧ (pi/2)^2 "
    "= pi^2/4 by ring'. §5.2's goals are lists and D12 has no "
    "conjunctions, so they are two keys, decided in-step (E39), and they "
    "need §6.8's exact values as well as ring once phi is a transcendental "
    "(ln 1 = 0, sin(pi/2) = 1). §11.1's list also omits pi/2's 2 # 0 from "
    "the new upper limit, which its revision-10 note mentions.",
    "§6.4 states int_subst's premises but not where phi' is computed or on "
    "which interval its side conditions live. They must be on the closed "
    "range (E38), since phi in C^1([a, b]) is closed; so deriv's side "
    "conditions are sufficient, not necessary: x := t*sqrt t over [0, 1] "
    "is C^1 (phi' = (3/2) sqrt t) but d_sqrt's t > 0 @ [0, 1] refuses it. "
    "That is a completeness limit of reading C^1 off deriv, not a "
    "soundness one, and it goes away only with §6.9's regularity rules.",
    # int_subst review 2026-09-24
    "§18 Q22's settled reading (E33 F3) decides a key false at a rational "
    "point from a fixed candidate set, and the set never held a root of "
    "the key's own polynomial, so a pole inside the range at a point that "
    "is neither an end nor the midpoint was admitted tagged none: the "
    "skeptic's Int[x = -1 .. 5/3] 1/(x^2 + 1) by x := 5/(2*t - 5) reported "
    "'Proved modulo 9 admissions' for a false value. E50 adds the rational "
    "roots of the proposition's univariate pieces. §18 Q22 and §5.4 should "
    "say that an admission tagged none may be false exactly when no "
    "candidate refutes it, that the candidates include those roots, and "
    "that the remaining misses are irrational roots (t^2 - 2 # 0 on "
    "[0, 2]), roots beyond ROOT_TEST_BOUND, and multivariate pieces. "
    "Future method, recorded and not built: an exact univariate sign "
    "decision by Sturm sequences, which would decide t^2 - 2 # 0 on "
    "[0, 2] (a real root in the range, so false) with a certificate the "
    "trusted checker can re-check by counting sign changes; it would be "
    "§5.3's first method that proves an obligation false rather than "
    "failing to prove it.",
    "§5.4's example of a false admission tagged none, x - 5 # 0 on "
    "[0, oo) (E33, the §5.4 entry above, DISCHARGE_UNDECIDED), is refuted "
    "at x = 5 once E50 lands; the example becomes t^2 - 2 # 0 on [0, 2] "
    "(F3_ROOTS_CHANGES).",
    # consolidation spec 2026-09-24
    "§5.3 method 5 closes only strict and # 0 goals, so 1 - x^2 >= 0 on "
    "[0, 1], every sqrt(a^2 - x^2) substitution's own domain, had no "
    "method. E53 extends it to non-strict goals with non-strict factors; "
    "§5.3 should state the four relations, the parity, and that a "
    "non-strict factor never serves a strict target.",
    "§6.2 names pyth as (sin x)^2 + (cos x)^2 == 1, which field cannot use "
    "as stated (a sum on the left; rewrite can, at a tree-equal sum: "
    "corrected by the consolidation review, E57). §6.8 should pin the "
    "solved form pyth_cos : (cos u)^2 == 1 - (sin u)^2 beside it (E54), "
    "and name the sign facts a trigonometric substitution needs: sin on "
    "[0, pi], cos on [0, pi/2], and the total bounds of cos, which the "
    "linear method reads per atom (ATOM_FACT_RULE).",
    "§5.1 and E4: a goal whose integral has symbolic reversed limits and "
    "whose body owes a former cannot be installed, since installation owes "
    "the range's lo <= hi and F2 refuses it; int_flip (E51) reaches only "
    "reversed integrals whose bodies owe nothing, and a flip that makes a "
    "reversed symbolic range whose body owes a former is refused. E46's "
    "rule (build the interval from the order discharge proves) applied in "
    "E4 itself would remove both limits. (Owner's answers 2026-09-24: done, "
    "E56.)",
    # consolidation spec 2026-09-24, owner answers
    "§5.1, §5.3 method 2 and §6.4 (E4): every step that builds a range "
    "now builds it from the order discharge proves, [lo, hi] or [hi, lo], "
    "and refuses 'orientation-undecided' when neither is proved (E56). "
    "§5.1's reversed limits are then ordinary input for every move, not "
    "only int_subst's output; §6.4's ftc should say its premises are on the "
    "interval between a and b, whichever is smaller, and §5.3 that a range "
    "item is never empty.",
    "The consolidation spec (E53) missed one consequence, found while "
    "re-tracing E56: with sign products on non-strict goals, pi/2's sign "
    "closes as (1/2)*pi with pi > 0 by cite pi_pos, so a search that has "
    "lost the linear method's sign facts still proves 0 <= pi/2. Two "
    "discharge routes for one fact are fine for soundness, but the "
    "pi_pos_not_in_constraint_set seam now shows only as a tag "
    "(E56_CHANGES).",
    "§6.4 and E51: the owner's int_flip was stated as Int[x = a .. b] f "
    "== -(Int[x = b .. a] f); the kernel's form is Int[x = b .. a] -(f), "
    "so that ftc, which acts on a top-level integral, can run after it. "
    "§6.4 should state the move in that form, or give ftc a position.",
    # regularity spec 2026-09-24
    "§5.2 and §6.9 declare e in C^k(D) without saying what it means on a "
    "domain with several variables or with closed ends. E59 fixes it: C^0 "
    "is continuity on the domain's point set (relative topology), C^1 is "
    "C^1 on an open neighbourhood of every point, both jointly in the free "
    "variables. §6.4's int_subst premise phi in C^1([a, b]) is one-sided "
    "in the textbook; the neighbourhood reading is stronger and "
    "sufficient.",
    "§6.4 says the x := t*sqrt t completeness limit 'goes away only with "
    "§6.9's regularity rules, which can state C^1 without differentiating "
    "through the root'. The C^0/C^1 subset built here does not: sqrt's C^1 "
    "side t > 0 fails at 0 in any reading of the rule, and a one-sided "
    "rule, or a real power t^(3/2) (which D17 refuses as a literal "
    "exponent), would be needed. int_subst's deriv refuses the step "
    "first in any case (REG_NOT_COVERED).",
    "§18 Q23's second deciding case (I = Int_1^oo 1/x, I - I == 0 'stops "
    "at the owed 1/x integrable on [1, oo), which is false') is not what "
    "this step does: convergence is not C^0 (1/x is C^0 on [1, oo)), so "
    "an improper integral's former cannot be a Reg, and conv/diverges are "
    "deferred (E65). The blanket refusal stands for improper integrals.",
    "§5.1 ('Int and D[x] subterms have no statable definedness condition "
    "until §6.9's regularity and §5.2's diverges are built'), §6.1's E57 "
    "paragraph ('means never') and §6.2 ('all three refuse a side "
    "containing Int or D[x]') are superseded for statable integrals and "
    "for D nodes by E64-E66; they stand for improper integrals and for "
    "integrals with a tree in a limit. E7's refusal and install's "
    "hypothesis gate are kept (E66 (2)), which §5.1 should say.",
    "§6.9 rejects 'a reflective procedure inside the trusted base'. The "
    "regularity checker is trusted code (§15.2 item 5 should list it with "
    "the other certificate checkers), but it is not reflective: it decides "
    "nothing, and checks one REG_RULES instance per node, with each side "
    "condition an ordinary checked obligation. §15.2 item 2 gains "
    "REG_C1_EXTRA (abs's u # 0) as the one datum regularity adds; the C^0 "
    "sides are §5.1's former table itself.",
    "§5.4's admission reasons lose 'regularity not built' (E60); §11.1's "
    "'Proved. 0 admissions', never reachable as written (§6.9's own "
    "admission), is now what the kernel reports for P1.1 from the sheet, "
    "and §11.2's P1.2 likewise.",
]

# What was checked at build time, in scratch, with SymPy 1.14 and mpmath.
# None of it is imported here.
VERIFIED = (
    "every string above parses under a scratch prototype of GRAMMAR.md, and "
    "parse(show(t)) == t for each",
    "deriv of each F equals its integrand (P1.1, the fallback, P1.2), and "
    "each DERIV output, read as a function, equals the true derivative",
    "each DERIV output as a tree equals a literal application of §6.3's "
    "forms under E12",
    "each rewrite step: goal_after is goal_before with every occurrence of "
    "`at` replaced by R, and ring_nf of the arguments agrees",
    "each ftc goal_after is F[b] - F[a] as a tree",
    "each close: lhs - value is 0 under the stated procedure, with sqrt 3 "
    "opaque, and P1.2-alt is nonzero without the fact",
    "each named entry is true (numerically at sample points for schemas)",
    "each obligation is true on its domain (numeric sampling for relations; "
    "continuity of each regularity premise checked by hand, and "
    "definedness sampled)",
    "each field divisor list equals the set of divisors in deriv(F) and f",
    "the answers equal the integrals numerically, to 30 digits",
    "each residual equals lhs - rhs symbolically (sqrt 3 as a free symbol "
    "for W3 and W4) and is nonzero",
    "per-step lists and FINAL_TRACKER agree, and the admission counts match",
    "GRAMMAR.md §5's substitution-into-D examples: (D[x] x^2)[x := 1] = 2 "
    "against the naive 0, (D[x](x*y))[y := x] = x against 2x, and "
    "(D[x](x*z))[x := z] = z against the renamed 2z",
    "ring_nf cancels inv atoms additively: inv(x) - inv(x) + 1 and "
    "x*inv(x) - x*inv(x) + 1 both normalise to 1, x*inv(x) does not "
    "(REWRITE_RULE step 5, MATCH_ACCEPTS)",
    "close_bound_variable_ring_true's lhs minus t - t + 2 is 0 by ring, and "
    "the post-ftc lhs minus t is not",
    "each PLANTED_BUGS tracker_drops_one drop_keys entry, in every proof in "
    "PROOFS whose EXPECTED_OBLIGATIONS contain it, is minted once and never "
    "re-emitted, and the stated counts follow",
    "the E24 rule was traced by hand through every admission in "
    "EXPECTED_OBLIGATIONS, MATCH_ACCEPTS and OCCURRENCE_CASE and reproduces "
    "each expected tag, and through the pi_pos_not_in_constraint_set "
    "variant. SymPy confirmed what the trace rests on: 1 + x^3 = "
    "(1 + x)*(x^2 - x + 1); discriminant -3 for x^2 - x + 1; a Farkas "
    "combination for each set that must be infeasible; and a feasible "
    "point for each set that must not be (t = -1/2 for t >= 0 @ [-1, 0], "
    "pi = -1 without pi_pos, and the opaque-monomial sets of the sign and "
    "product cases)",
    "E25's examples: ring_nf(x - x) = 0; ring_nf(x/x - 1) = x*inv(x) - 1 is "
    "nonzero while cancel(x/x - 1) = 0; and the integral in "
    "rewrite_under_D_through_Int is x*|x|/2 before the rewrite and x^2/2 "
    "after",
    "ECHO_NONCANONICAL's input and every new BAD_MOVES goal round-trip "
    "under the scratch prototype, and the former parses to P1_2_GOAL's tree",
    "every ROUND_TRIP_EXTRA, ROUND_TRIP_SCHEMAS, ROUND_TRIP_GRAMMAR, "
    "MATCH_ACCEPTS and OCCURRENCE_CASE string round-trips under the scratch "
    "prototype, and PRINT_EXACT's forms are what it prints",
    "each ROUND_TRIP_SCHEMAS entry is an identity of calculus with u, v "
    "functions of x; d/dx(-exp(-x)) = exp(-x) (ftc_infinite_endpoint); "
    "ring_nf((t - t + 1)^2) = 1 (rewrite_in_own_endpoint); (1/4)*pi^2 has "
    "constant 0 and discriminant 0 in pi (E20)",
    # Added with E26 (user decision 2026-09-24), with SymPy 1.14 in the
    # session scratchpad. The lists were derived by hand from E26's rules,
    # never from kernel code.
    "E26's new obligations are true on their domains: t^2 >= 0 on "
    "[0, pi/2] and x >= 0 on [0, pi^2/4] (minimum 0), pi^2/4 >= 0, 1 + x > 0 "
    "on [0, 1] (minimum 1), x^2 - x + 1 > 0 on [0, 1] (minimum 3/4, at "
    "x = 1/2), the literal 1 + 1, 1^2 - 1 + 1, 1 + 0, 0^2 - 0 + 1 and 2 "
    "positive and 3 and 0 non-negative, 1/x - 1/x + 1 = 1 on [1, 2], and "
    "x^2 >= 0 on [0, oo); DEFINEDNESS_CASES' cos(pi/2) = 0 and x > 0 on "
    "x < 0 are false, as their none tags say, and x > 0 on x > 0 true",
    "E26's case arguments: ln(-1) = I*pi, ln 0 = zoo, sqrt(-1) = I, asin 2, "
    "asin(-2), acos 2 and acos(-2) are not real, acosh 0 = I*pi/2, "
    "atanh(1) = oo, atanh(-1) = -oo and tan(pi/2) = zoo; sqrt 0 = 0, "
    "asin(1) = pi/2, asin(-1) = -pi/2, acos 1 = 0, acos(-1) = pi, "
    "acosh 1 = 0 and atanh 0 = 0 are real; Int[x = 0 .. oo] 1 = oo; and "
    "|x|'s one-sided difference quotients at 0 tend to -1 and 1",
    "the E24 tags of E26's keys, traced by hand, with the Fourier–Motzkin "
    "sets under them checked: feasible points for t^2 >= 0 @ [0, pi/2] "
    "(t^2 opaque, -1, at t = 0, pi = 1), pi^2/4 >= 0 (pi^2 opaque, -1), "
    "x^2 - x + 1 > 0 @ [0, 1] and x^2 >= 0 @ [0, oo) (x^2 opaque, -1, at "
    "x = 0), both senses of cos(pi/2) # 0 (the atom 0, pi = 1) and "
    "x > 0 @ x < 0 (x = -1); Farkas combinations for x >= 0 @ [0, pi^2/4] "
    "and 1 + x > 0 @ [0, 1] (a dom item used, so range), and for "
    "1/x - 1/x + 1 > 0 @ [1, 2] (the negated goal 1 <= 0 alone, so "
    "linear); discriminant -3 and (x - 1/2)^2 + 3/4 for x^2 - x + 1",
    # Added with the review fixes (user decision 2026-09-24), SymPy 1.14.
    "the review fixes' maths: cos(0) = 1 and cos(pi/2) = 0 (tan_zero_true, "
    "tan_pi_half); -(x + (sqrt x - sqrt x)) and -(x + (a - a)) expand to "
    "-x, and d/dx atan(-x) = -1 at 0 (step 9's cases); d/dx x = 1, "
    "Int[t = 0 .. oo] 1 = oo, D[x] x^2 = 2x, Int[t = 0 .. x] t = x^2/2 "
    "(E26 (b)'s cases); atan(-ln x) + atan(ln x) = 0, ln x > 0 on [1, 2], "
    "and Int[t = 0 .. sqrt y] t = y/2 (the position cases)",
    "p1_expected checked against itself by a scratch script that keys "
    "judgements with kernel/terms.py's parser and nothing else: every step's "
    "new flags against the running tracker, the per-step lists against "
    "FINAL_TRACKER and ADMISSIONS, TRACKER_AT_FORGERY_STATE against P1.2 "
    "through s8, PLANTED_BUGS' counts by simulating each mutation on the "
    "lists, DEFINEDNESS_MUTATIONS' removal counts, every caught_by location "
    "against an existing entry or case, DEFINEDNESS_CASES' finals, reports "
    "and theorems, and all ROUND_TRIP strings round-tripping under "
    "terms.py's parser and printer",
    # Added with the second round of review fixes (user decision
    # 2026-09-24), SymPy 1.14.
    "the second review round's maths: Int[t = 0 .. oo] 1 = oo, d/dx of "
    "x + (c - c) is 1, and Int[x = -1 .. 1] 1 = 2 = F(1) - F(-1) for "
    "F = x (the ftc cases); |h|/h tends to -1 and 1 at 0 (D[x](abs x) and "
    "D[y](abs y)); D[y] y^2 = 2y; atan(-ln(x + y)) + atan(ln(x + y)) = 0, "
    "the LP {x + y <= 0, 1 <= x <= 2, y >= 0} is infeasible (with the "
    "Farkas sum of x + y <= 0, 1 - x <= 0, -y < 0 giving 1 < 0) and "
    "x = 1, y = -5 satisfies the set without y > 0; d/du asin u = "
    "1/sqrt(1 - u^2), d/du acosh u = 1/(sqrt(u - 1)*sqrt(u + 1)), d/du "
    "asinh u = 1/sqrt(u^2 + 1), and u^2 + 1 < 1 has no real solution",
    "every string added in the second review round parses under "
    "kernel/terms.py, and parse(show(t)) == t for each; p1_expected "
    "imports",
    # Added by user decision 2026-09-24 (evaluated answers), SymPy 1.14.
    "E27's cases: every refused value equals its 'evaluated' form (so each "
    "refusal is about form, not truth), and the S2, S3 and P1.1 ones equal "
    "their integrals ((e - 1)/2, 1/2, 2); the ordering case's 1 + 1 + 1 is "
    "not 2; every current reference answer equals its integral (P1.1 and "
    "its fallback 2, both P1.2 forms, S1 2, S2 (e - 1)/2, S3 1/2), and the "
    "two P1.2 forms are equal; each limitation equals the form E27 does "
    "not demand (ln 6, 2*sqrt 2, 1, |y|, 4 + 2*sqrt 3, 4*pi^2, "
    "2*pi*sqrt 3/9)",
    "E27's outcomes were derived by hand from EVALUATED_RULE, then "
    "cross-checked by a throwaway scratch reading of the rule (terms.py's "
    "parser, printer and children walk; SymPy's expansion over "
    "atoms-as-symbols standing in for ring_nf; no kernel module, and not "
    "schema.py): it gives every case's clause, offending subterm, entry "
    "and filled message as stated, accepts every EVALUATED_ACCEPTS value, "
    "every entry's right side and every existing close value that "
    "reaches E27, and fires on t - t + 2, 0*ln(-1) and the suite's f - f, "
    "which is why E27 runs after the refusals those cases assert; every "
    "string added parses, and parse(show(t)) == t for each",
    # Added with the review fix (user decision 2026-09-24, evaluated
    # answers), SymPy 1.14.
    "the review fix's cases: each new refused value equals its "
    "'evaluated' form (2*(pi + 1) - 2 = 2*pi, (e + 1)/2 - 1/2 = e/2, "
    "2*(pi + 1) - 2*pi = 2, (pi + 1)/2 - pi/2 = 1/2, 2*(e - 1) - 2*e = -2, "
    "(pi + 1)^2 - 1 = pi^2 + 2*pi, (sqrt 2)^(-2) = 1/2, (sqrt 3)^(-2) = "
    "1/3, (sqrt 2)^3 = 2*sqrt 2, pi^0 = 1), and each evaluated form "
    "passes E27; each added limitation equals the value E27 does not "
    "demand (exp(ln 2) = ln(exp 2) = ln(e^2) = 2, sin(pi) = 0, cos(pi) = "
    "-1, sin(pi/6) = 1/2, atan 0 = 0, atan 1 = pi/4, atan(sqrt 3) = pi/3, "
    "atan(sqrt 3/3) = pi/6, 4^(1/2) = 2, (pi^2)^(1/2) = pi, "
    "(1/sqrt 3)^2 = 1/3, (pi*sqrt 3)^2 = 3*pi^2, (pi - 1)*(1 - pi) = "
    "-(pi - 1)^2, pi*pi^(-1) = 1, 1*pi^(-1) = 1/pi), and "
    "x*exp(x) - exp(x) = (x - 1)*exp(x) and the canonicalised "
    "atan(-1/2) = -atan(1/2), pi*(1/sqrt 3) = pi/sqrt 3 are right; the "
    "scratch reading, amended for the fix, gives every new case's clause, "
    "subterm, entry and message as stated, accepts every "
    "EVALUATED_ACCEPTS value and every added limitation, and gives every "
    "earlier e27 case the outcome it already records",
    # Added by the discharge spec 2026-09-24, SymPy 1.14, in the session's
    # scratch directory, with kernel/terms.py's parser used only to read
    # the strings (no kernel code decided anything).
    "discharge spec 2026-09-24: an independent SymPy reading of "
    "DISCHARGE_RULE's checker (targets, the constraint set and its labels, "
    "Farkas sums ring-normalised with atoms opaque, sign identities, "
    "products with parity and children, cites with the syntactic "
    "implication, hyp member and chain, the norm_num leaf) accepts every "
    "certificate in DISCHARGE_EXPECTED (P1 and problems/stage0), "
    "DISCHARGE_MATCH_ACCEPTS, DISCHARGE_OCCURRENCE_CASE, the ln_true_by_hyp "
    "and twin certificates and DISCHARGE_CHECKER_ACCEPTS, each with exactly "
    "the tag given; rejects all 31 DISCHARGE_MUST_REJECT certificates, each "
    "for the reason given; every discharged key is true on its domain "
    "(solveset of the negation over the domain empty, pi and e real; the "
    "two-variable keys on a rational grid); every Farkas key's set without "
    "the goal is satisfiable; every must-reject 'truth' holds (the false "
    "ones false at the point named, the true ones true); every F3 message's "
    "point is the first of COUNTERPOINT_CANDIDATES, in order, lying in the "
    "domain with its formers defined and the proposition literal and false "
    "after the exact values (DISCHARGE_BAD_MOVES_CHANGED and _ADDED, "
    "OCCURRENCE_CASE 'all', ln_false_on_goal_domain, the must-reject "
    "'refused' outcomes, the planted-bug and mutation refusals); every "
    "'admitted' outcome and every DISCHARGE_UNDECIDED key is false yet has "
    "no such point; the reversed range's pi/2 <= 0 is false and its "
    "negation's certificate is accepted with ('linear', ('pi_pos',)); "
    "(x + pi)/(x + pi) - 1 cancels to 0; 0 <= pi/2 has no certificate "
    "without pi_pos, and neither the halved multiplier nor the swapped end "
    "is accepted; and the existing suite still passes 334 of 334 with both "
    "data files extended",
    # discharge spec 2026-09-24, owner answers
    "owner answers (E35): the verifier re-run with cos_zero and sqrt_zero "
    "among the exact values accepts and rejects exactly as before; every "
    "F3 message's reading is the kernel-parsed proposition at the point "
    "(terms.subst with terms.lit values, then the exact values), with the "
    "entries listed and only those (it caught one written as a string, "
    "fixed); sqrt x # 0 @ [0, 1] is refused at x = 0 reading 0 # 0 with "
    "sqrt_zero, and has no other point first; cos 0 # 0 reads 1 # 0 with "
    "cos_zero; cos 1 # 0 is true and undecided; cos 0 = 1 and sqrt 0 = 0; "
    "e27_goal_lhs_before_close's value equals 2 and its only application "
    "is cos 0; e27_goal_lhs_after_ftc's first application in pre-order is "
    "still sin(pi/2); the new e27 values equal 1 and 0; no reference "
    "proof's closing value and no other accepted value holds cos 0 or "
    "sqrt 0",
    # int_subst spec 2026-09-24
    "int_subst spec (section 12), SymPy 1.14 in scratch: every transformed "
    "integral equals the original (Int_0^{pi^2/4} sin sqrt x = 2 = "
    "Int_0^{pi/2} sin(sqrt(t^2))*2t; Int_0^1 2x = 1 = Int_1^0 2(1 - t)(-1); "
    "Int_1^1 x = 0 = Int_-1^1 2t^3; Int_0^1 exp x = e - 1 = Int_1^e "
    "exp(ln t)/t; SUB1's 4/15 both ways); every endpoint equation holds "
    "where accepted and fails where refused ((pi/2)^2 = pi^2/4; pi^2 - "
    "pi^2/4 = (3/4)pi^2; sin(pi/2) - pi^2/4 = 1 - pi^2/4, nonzero, and "
    "pi^2/4 > 1); each deriv output is the true derivative; each ftc "
    "check and value (F(0) - F(1) = 1 and 4/15; the sorted-limits bug "
    "gives -1 and -4/15); every discharged key is true on its domain and "
    "every refused one false at its named point (t > 0 and u > 0 at 0, "
    "t^2 # 0 at 0, pi/2 <= 0); Int_-1^1 2/t diverges; Int_{pi/2}^0 "
    "cos(pi/2 - t)(-1) = 1, so the refused decreasing case is a valid "
    "substitution; the subst-under-D cases' true values (2t^2, y*t) "
    "differ from the naive ones (0, 2yt); (t sqrt t)' = (3/2) sqrt t. "
    "DESIGN.md §8.6's 1.3012779 for the sin guess does not match: the "
    "guess over [0, pi/2] gives Int_0^1 sin sqrt x = 0.6023... Every "
    "string in section 12 and in problems/stage0's section 12 parses with "
    "terms.py's parser and round-trips through its printer; every "
    "int_subst goal_after equals Int(new_var, lo, hi, Mul(body[x := sub], "
    "deriv output)) built with terms.subst, every ftc goal_after "
    "F[t := hi] - F[t := lo], and every endpoint key sub[t := end] (a "
    "check of the hand derivation, not a source of it); and both data "
    "files import with their cross-checks, the existing suite still "
    "passing",
    # int_subst spec 2026-09-24, owner answers
    "int_subst spec 2026-09-24, owner answers, SymPy 1.14 in scratch, 107 checks: the flipped forms equal the "
    "originals (Int_0^{pi/2} -(cos(pi/2 - t)(-1)) = 1; x = cos theta "
    "gives pi/4 for sqrt(1 - x^2) and 1/2 for x, and F(pi/2) - F(0) = "
    "1/2); the flip identity; cos(pi/2) = 0 and cos 0 = 1; the sum's value "
    "is unchanged by the move; D[y] of the constant integral is 1 both "
    "ways, while Int_0^1 x*y = y/2 depends on y; y*t over [0, 1/y] is valid "
    "for either sign of y, so its order is genuinely undecided; reverse "
    "mode's identities (x e^(x^2) = (e^(x^2)/2)(2x), 2x^3 = x^2(2x)), "
    "values ((e - 1)/2; 0 = 0 for the non-monotone g) and failures "
    "(S2R-W1's residual -x e^(x^2); HolPy's x^2 - x|x| = 2 at x = -1, "
    "against the true 2/3); SUB2's value 4 - 2 ln 3 both ways, its F', "
    "deriv output and endpoints; sqrt a >= 0 sampled; sqrt x > 0 false at "
    "0. terms.py's parser and printer: every new string parses and "
    "round-trips; every new int_subst goal_after equals the tree rebuilt "
    "from its parts (flipped Neg, position replacement, reverse f), every "
    "reverse identity key body == f[u := g]*g', every ftc goal_after "
    "F[hi] - F[lo], every endpoint image; both data files import with "
    "their cross-checks, and the suite still passes 481 of 481",
    # int_subst review 2026-09-24
    "int_subst review 2026-09-24, SymPy 1.14 in scratch: the reproducer's true value atan(5/3) + "
    "pi/4 = 1.8158 against the reported -atan(3/5) - pi/4 = -1.3258, its "
    "ends mapping (-1, 5/3) and its only pole 5/2 in [0, 4]; ftc alone: "
    "the true -(atan(3/2) + atan(5/2)) = -2.1731 against the ftc value "
    "atan(2/3) + atan(2/5) = 0.9685, F' equal to the integrand off 5/2 and "
    "F jumping by pi there; each F3 walk's earlier candidates true and its "
    "root false (5/2, 5/2, 2, 5); t^2 - 2 with no rational root among "
    "+-1, +-2 and a root sqrt 2 in [0, 2]; x <= 5 true at its root; the "
    "three gap cases' integrals (1 = Int_1^e 1/t, pi^2/4 both ways, "
    "-pi^2/4 both ways). terms.py: every string parses and round-trips, and "
    "every F3 reading is the proposition with terms.lit at the point. Then, "
    "after the hand derivation, the committed kernel (ed40695) was driven "
    "as a black box: REVIEW_ACCEPTS' emissions and goals, "
    "REVIEW_BAD_MOVES' refusal and message, and the new sqrt case's "
    "'unknown-label' match it exactly; the F3 cases show today's false "
    "admissions tagged none (their 'was'); the irrational pole is admitted "
    "'no method decides it'. The suite still passes, both files importing",
    # consolidation spec 2026-09-24
    "consolidation spec 2026-09-24, SymPy 1.14 in scratch, 36 checks: the flip identity and the "
    "flipped proof's value -pi^2/4, its F' and deriv output; 1 - x^2 as "
    "-(x - 1)(x + 1) and as (1 - x)(1 + x), nonnegative on [0, 1], and the "
    "rejected cases false where named; pyth, pyth_cos and their difference "
    "a ring identity; sin >= 0 on [0, pi], cos >= 0 on [0, pi/2], -1 <= "
    "cos <= 1; QC1's value pi/4, its ends, its flipped integral (numeric), "
    "1 - cos^2 as -(cos - 1)(cos + 1), sqrt(sin^2) = sin on [0, pi/2], F' = "
    "sin^2 with pyth, its deriv output, field's numerator zero only after "
    "cos^2 -> 1 - sin^2, and F(pi/2) - F(0) = pi/4. terms.py: every new "
    "string parses and round-trips, and every goal_after of int_flip and "
    "QC1 equals the tree rebuilt from its parts. Then, after the hand "
    "derivation, each of the 48 seams was run on P1.1-sheet through the "
    "suite's own patch functions: every N and every catch in "
    "P1_1_SHEET_TRACES matches; and QC1's s1 on today's kernel emits the "
    "listed keys, the two E53 keys still admitted none, and QC1-W2 is "
    "refused rewrite-lhs-mismatch. Both files import; the suite passes",
    # consolidation spec 2026-09-24, owner answers
    "consolidation spec 2026-09-24, owner answers, SymPy 1.14 in scratch: Int_{pi/2}^0 sqrt(t^2) = -pi^2/8 and "
    "Int_{pi/2}^0 2x = -pi^2/4, each by F(b) - F(a) with b = 0; "
    "Int_{pi/2}^0 2x = Int_0^{pi^2/4} -1 (the reverse case, flipped); the "
    "flip of Int_0^{pi/2} sqrt x equal to it; the ftc identity for b < a; "
    "-(pi/2) >= 0 false and -(pi/2) < 0 true; pi/2 = (1/2)*pi; 0 <= y "
    "neither true nor false for all y. terms.py: every new string parses "
    "and round-trips, and every new goal_after equals its rebuilt tree. "
    "The committed kernel (f22e1dd) still gives every case's 'old' value "
    "(decided_false_reversed_range and reverse_symbolic_old_range_reversed "
    "refused by F2 on pi/2 <= 0, rewrite_under_D_through_Int by F3 on "
    "0 <= x); both files import and the suite passes",
    # consolidation review 2026-09-24
    "consolidation review 2026-09-24: on the committed kernel (834b8a2) both pyth reproducers close "
    "'Proved.' and the z case too; the nested reproducer is accepted with "
    "premises on y in [a, b]; its decided twin emits every key "
    "E56_REVIEW_CASES lists except a <= b @ a <= b, which the amendment "
    "adds; the timing goal installs emitting nothing in 30.5 s. SymPy: "
    "sin^2 + cos^2 = 1 for real z; |x|' has no value at 0 (one-sided "
    "limits -1 and 1); Int_1^oo 1 diverges. terms.py: every new string "
    "parses and round-trips. Both files import; the suite passes",
    # regularity spec 2026-09-24
    "regularity spec 2026-09-24, in scratch (/tmp/claude-1000/reg/): an "
    "independent reading of REG_CHECK_RULE (regcheck.py), with each side "
    "handed to the committed discharge.check, accepts every certificate in "
    "REG_EXPECTED (both files), REG_CASE_CERTS, REG_CHECKER_ACCEPTS and the "
    "cases' certificates with exactly the tag given, and rejects every "
    "REG_MUST_REJECT certificate for exactly its rejects_because; for every "
    "REG_CASE_ADMITTED key it finds no derivation. The committed refuter "
    "(refute.refute) decides every E63 side condition false at exactly the "
    "point and reading given. SymPy 1.14 (symverify.py): every certified "
    "one-variable claim (144) is true in E59's reading (C^0: the domain "
    "inside continuous_domain; C^1: inside the interior of the continuous "
    "domains of e and e'); tan x on cos x > 0, x in [0, 1] checked with the "
    "interval restricted first (a SymPy set artifact otherwise); the "
    "multi-variable and constant ones by hand (atan(-ln(x + y)) with x + y "
    "> 0; x^y = exp(y ln x) with x >= 1; x*y; the constants of "
    "E56_REVIEW_CASES; sqrt 3); every must-reject truth as stated; "
    "Int_0^pi e^x sin x = (e^pi + 1)/2; Int_1^oo 1/x and Int_-1^1 1/x^2 "
    "diverge; Int_0^1 1/(2 sqrt x) = 1 (improper); the fallback's F is "
    "(2/3) x^(3/2) near 0+, C^1 one-sided but undefined left of 0. "
    "terms.py (parsecheck.py): all 876 new strings parse and round-trip. "
    "The committed kernel: installing Int[x = (a-1)^40 .. 0] sqrt(x^2) "
    "takes 29.7 s (E68). Both files import; the suite is unchanged",
)

# Changes to this file made after it was frozen. The first was adjudicated
# during implementation because the frozen data contradicted itself, not to
# fit the code. The rest carry out the owner's decisions of 2026-09-24
# (option (a) for question 1, dropping line-count budgets), or choices made
# on the owner's behalf in carrying them out, as each entry's last field
# says. They were derived by hand from the rules before any kernel change,
# without running or reading the kernel's charging code. The entries marked
# 'user decision 2026-09-24, review fix' are corrections found by reviewing
# this data after E26 was written, made in carrying out the same decision.
# The entries marked 'user decision 2026-09-24 (evaluated answers)' carry
# out the owner's later decision that closed answers be fully evaluated
# (E27). They were written as a spec before any code, without reading or
# running schema.py, and they add cases and change no existing expected
# value.
# Entries are (location, what changed, why, how it was decided).
DATA_CHANGES = (
    ("FORGERIES['print_proved_with_admissions'], 'accept' and its comment",
     "added the outcome honest_report, (c) only: the direct_tracker_write "
     "attempt ends in one of that case's accepted outcomes (raise_at_mutation "
     "or no_effect), and report(state) then returns VERDICTS['P1.1']",
     "a correct kernel's only behaviour for (c) is to return the honest "
     "verdict string with no exception and no refusal, and none of the four "
     "listed outcomes named it, so read literally under the E21 amendment "
     "('any outcome not in accept fails the case') a correct kernel failed "
     "its own case. The new outcome demands what 'post' already demands for "
     "(c), plus that the write attempt lands in direct_tracker_write's "
     "accepted outcomes, so the check is not weakened",
     "adjudicated during implementation"),
    ("HANDLES_IN_FORCE and its comment, the module docstring, DECISIONS E17",
     "'handles' became 'handles for facts, sentinel for proof states'. The "
     "comment gives the reason: a finished ProofState, the only kind "
     "report() gives a verdict for, is only ever produced by step(); "
     "§15.3's realistic failure is a buggy tactic, which the sentinel stops; "
     "§16.3's API boundary will replace in-process states with ids",
     "the old value claimed only the first of the two models in force, "
     "while ProofState uses §15.3's sentinel fallback. §15.3 says to say "
     "which is in force and not leave it ambiguous. The kernel's own "
     "HANDLES_IN_FORCE must match the new string, since the script "
     "compares them",
     "decided on the owner's behalf 2026-09-24 (PROOF_OF_LIFE.md question "
     "3): the owner expressed no preference beyond dropping line budgets; "
     "kept both models and made the claim honest, for the reason given"),
    ("section 5's comments (E6 amended, E26 added, E7 and E25 amended); "
     "DECISIONS E6, E7, E15, E25 and E26; SOURCES['former']; KEYING; "
     "DOMAIN_RULES E4; REWRITE_RULE steps 5 and 10; REFUSAL_CODES; the "
     "NAMED_ENTRIES atan_one_sqrt3 comment (comment only: its sqrt's "
     "3 >= 0 is not re-charged, E26)",
     "E26 added. (a) ln, sqrt, tan, asin, acos, acosh and atanh are formers "
     "owing their natural domain (for ln u, u > 0; sqrt u, u >= 0; tan u, "
     "cos u # 0; asin u and acos u, u >= -1 and u <= 1; acosh u, u >= 1; "
     "atanh u, u > -1 and u < 1), charged like '/'. (b) ring, "
     "field and norm_num refuse an Int or D node with the new code "
     "'Int-or-D-not-normalisable'. obligation-refuted's note names E26",
     "PROOF_OF_LIFE.md question 1: E6 charged only '/', negative powers and "
     "RPow bases, so ring cancelled undefined atoms, and 0*ln(-1) == ?A and "
     "tan(pi/2) - tan(pi/2) == ?A closed as a plain 'Proved.'. §14's "
     "agreement of the total and partial readings needs every partial "
     "former to carry its condition. E26 records its choice of shapes (one "
     "linear item per bound, u REL c) and why",
     "user decision 2026-09-24, option (a): undefined terms owe their "
     "domain"),
    ("EXPECTED_OBLIGATIONS, all four proofs",
     "re-derived under E26. P1.1: installation adds t^2 >= 0 @ [0, pi/2] "
     "(sign) and 0 <= pi/2, so s1's 0 <= pi/2 is no longer new. "
     "P1.1-fallback: installation adds x >= 0 @ [0, pi^2/4] (range) and "
     "0 <= pi^2/4; s1 re-emits both (new False) and adds pi^2/4 >= 0 (sign) "
     "and 0 >= 0 (norm_num) for the new goal's sqrt(pi^2/4) and sqrt 0; "
     "s3's 0 >= 0 is no longer new. P1.2: s2 adds 1 + x > 0 @ [0, 1] "
     "(range) and x^2 - x + 1 > 0 @ [0, 1] (sign) for F's ln, and the "
     "discharged 1 + 1 > 0, 1^2 - 1 + 1 > 0, 1 + 0 > 0 and 0^2 - 0 + 1 > 0 "
     "for the new goal's ln; its 3 >= 0 gains the source former; s7 adds "
     "3 >= 0; s9 adds 2 > 0 (new) and 3 >= 0. P1.2-alt's s9: 3 >= 0 gains "
     "the source former, and 2 > 0 is added",
     "every ln, sqrt, tan, asin, acos, acosh and atanh in each goal, each F, "
     "each new goal, each close value and each rewrite's R now owes its "
     "domain at its position domain (E26 (a)), keyed per E8 and tagged per "
     "E24; none of the new admissions is tagged none, and each was checked "
     "true on its domain (VERIFIED)",
     "user decision 2026-09-24, option (a)"),
    ("FINAL_TRACKER, ADMISSIONS, VERDICTS (derived)",
     "the new keys added; N is 6 for P1.1 (was 5), 9 for P1.1-fallback "
     "(was 7), 14 for P1.2 (was 12) and 13 for P1.2-alt (was 11)",
     "E26's admissions: t^2 >= 0; x >= 0 and pi^2/4 >= 0; F's two ln "
     "domains on [0, 1]. Every other domain it charges in P1 is literal "
     "and discharged by norm_num",
     "user decision 2026-09-24, option (a)"),
    ("MATCH_ACCEPTS goal_emits of both cases; TAG_RULES range/linear; "
     "OCCURRENCE_CASE, REGULARITY_LISTING and PROOFS comments",
     "ring_cancels_inv_atom's installation adds 1/x - 1/x + 1 > 0 @ [1, 2] "
     "tagged ('linear', ()); rewrite_under_infinite_range's adds "
     "x^2 >= 0 @ [0, oo) tagged sign. TAG_RULES now says the Farkas "
     "combination is an irreducible one. The comments note the formers "
     "each place now owes",
     "both goals hold ln or sqrt in their integrand. The first key's "
     "negated goal normalises to 1 <= 0 and is infeasible by itself, and "
     "Farkas combinations are not unique, so without the sentence its tag "
     "('range' or 'linear') would depend on the implementation's search. "
     "Irreducibility makes it 'linear' and changes no tag given before "
     "(each earlier set has one irreducible core, or is the one the suite "
     "pins by tagger.py's deletion order)",
     "user decision 2026-09-24, option (a); the TAG_RULES sentence is its "
     "consequence, kept so tags stay computed by a stated rule (E24)"),
    ("BAD_MOVES close_D_goal_scope_passes",
     "refusal close-check-failed became Int-or-D-not-normalisable, and its "
     "'why' was rewritten",
     "ring now refuses the side D[x] x^2 instead of reading it as an atom "
     "(E26 (b)). The refusal still comes after the scope check and the "
     "whitelist, so the case still pins what it was for: D11 and E19 "
     "accept a goal with D[x]",
     "user decision 2026-09-24, option (a)"),
    ("BAD_MOVES, 18 cases added",
     "ln_negative_literal, ln_zero_literal, sqrt_negative_literal, "
     "asin_above_literal, asin_below_literal, acos_above_literal, "
     "acos_below_literal, acosh_below_literal, atanh_upper_end and "
     "atanh_lower_end (installation refused obligation-refuted); "
     "rewrite_R_owes_domain and close_value_owes_domain (the same code at "
     "a rewrite's R and at close's value); ring_refuses_Int, "
     "ring_refuses_D, field_refuses_D, norm_num_refuses_Int, "
     "divisor_test_refuses_Int and match_refuses_Int "
     "(Int-or-D-not-normalisable)",
     "one refusal per bound of each builtin, so that dropping any single "
     "condition is caught, and six for E26 (b): ring on Int and D, field "
     "on D, norm_num on Int, E25 on Int and the match on Int. That was not "
     "every normaliser and node pair, nor every call site, as this entry "
     "first claimed; the review fix below completes both. 0*ln(-1) == ?A "
     "is refused when it is installed, not at the close: "
     "installation charges the goal's formers (E6), so the close is never "
     "reached",
     "user decision 2026-09-24, option (a)"),
    ("DEFINEDNESS_CASES and DEFINEDNESS_MUTATIONS (new, section 8b); "
     "PROVED, T_HYP and T_LINEAR; all_term_strings; the no-none comment",
     "eight accepted cases: tan_pi_half and ln_false_on_goal_domain "
     "('Proved modulo 1 admissions', the admission tagged none), "
     "ln_true_by_hyp (tagged hyp), and five literal cases reporting "
     "'Proved.' that pin each closed end and atanh's interior. 23 "
     "mutations, each with the cases and P1 locations that catch it: every "
     "builtin's former removed, every bound of a two-sided domain removed, "
     "every end's closedness swapped, and each normaliser reading Int or D "
     "as an atom",
     "so that removing any single partial former is caught (a data-review "
     "choice, made to carry out option (a); the owner did not specify "
     "coverage); the cases also pin E26's open and closed ends exactly. "
     "ln_false_on_goal_domain, against ln_true_by_hyp, is the no-none "
     "check's positive test for definedness. tan_pi_half's none is "
     "unconditional until §6.8's cos_nonzero_on is pinned, so it pins "
     "only that tan is charged (corrected by the review fix below, which "
     "added tan_zero_true)",
     "user decision 2026-09-24, option (a)"),
    ("TRACKER_AT_FORGERY_STATE and its comment; FORGERIES "
     "direct_tracker_write and print_proved_with_admissions",
     "the forgery-state tracker now drops both keys s9 mints, 3*sqrt 3 # 0 "
     "and 2 > 0; the texts' counts became N = 6 and 'Proved modulo 13 "
     "admissions'",
     "P1.2's close owes the value's ln 2 domain, 2 > 0 (E26), a new key",
     "user decision 2026-09-24, option (a)"),
    ("PLANTED_BUGS",
     "every 'admissions' updated; tracker_drops_reemitted's key is first "
     "inserted at P1.1's installation, so it is caught at s1, not s2; "
     "pi_pos_not_in_constraint_set is also caught at P1.1's installation; "
     "the texts of d_ln_emits_nothing and ftc_derivative_premise_on_closed "
     "name the ln formers",
     "E26 moves P1.1's orientation to installation and adds admissions. "
     "d_ln_emits_nothing is still caught at the same four places, because "
     "F's ln formers are on [0, 1] and d_ln's keys on (0, 1) (E8), and "
     "field still emits only divisors",
     "user decision 2026-09-24, option (a)"),
    ("DESIGN_DEFECTS",
     "the §11.2 entry now reads its 1 + x > 0 @ [0,1] as ln's former; a new "
     "entry records that §5.1 and §6.2 lacked partial formers and that "
     "§14's agreement claim (PROOF_OF_LIFE.md cites it as §15.4) depended "
     "on them, resolved by E26",
     "the §11.2 entry called that line a regularity sub-obligation only, "
     "which E26 made incomplete",
     "user decision 2026-09-24, option (a)"),
    ("VERIFIED",
     "four entries appended, for what was checked with SymPy and by a "
     "scratch consistency script",
     "the record of the checks behind the changes above",
     "user decision 2026-09-24"),
    ("GRAMMAR.md §3, D12 and §10 (notes only; no syntax, tree or parse code "
     "changed)",
     "a paragraph saying the seven partial builtins, Int and D[x] parse "
     "with any operand, definedness being E26's obligation and not syntax; "
     "D12 gives E26's orientation (u REL c, two items for a two-sided "
     "domain); §10 names sqrt's t^2 >= 0 @ [0, pi/2] beside sqrt_sq's key",
     "so that a reader of the grammar does not expect ln(-1) to be a parse "
     "refusal, and so that E26's keys follow D12 visibly",
     "user decision 2026-09-24, option (a)"),
    ("DEFINEDNESS_CASES tan_pi_half comment and the new tan_zero_true; the "
     "section 8b header; the no-none comment; the E26 (a) note; DECISIONS "
     "E15; DEFINEDNESS_MUTATIONS no_tan_former",
     "tan_zero_true added: 0*tan 0 == ?A owes the true cos 0 # 0, admitted "
     "and tagged none, 'Proved modulo 1 admissions'. The comments now say "
     "E24 tags every cos u # 0 none, true or false, unless the goal's "
     "domain Γ states it, which hyp closes; that no NAMED_ENTRIES "
     "entry concludes it (§6.8's cos_nonzero_on is not pinned); and that a "
     "PROOFS run containing tan on a goal whose domain does not state it "
     "cannot yet pass the no-none check. "
     "no_tan_former is also caught by tan_zero_true. No tag or expected "
     "value of an earlier case changed",
     "the data presented tan_pi_half's none as the tagger detecting a false "
     "obligation, but by TAG_RULES, with Γ empty, as in both cases, the "
     "tag is none for every u: "
     "cos u is an opaque variable to FM, a degree-1 atom to sign and sign "
     "product, and no pinned entry concludes it. The old comment's 'no "
     "§6.8 entry concludes it' was also wrong: §6.8 lists cos_nonzero_on. "
     "tan_zero_true records the limitation as a pinned fact rather than "
     "prose. SymPy: cos(pi/2) = 0, cos(0) = 1",
     "user decision 2026-09-24, review fix"),
    ("REWRITE_RULE step 9; DECISIONS E11; BAD_MOVES "
     "rewrite_under_D_R_closed_former and rewrite_under_D_R_divisor",
     "step 9 (a)'s openness test now applies to every obligation step 10 "
     "charges from R at an occurrence below D[x] (E6's and E26's formers, "
     "nested ones included), not only to H, with the same refusal "
     "'rewrite-under-D-needs-open-domain'. Two cases pin it: atan_odd "
     "under D[x] with u := x + (sqrt x - sqrt x) (sqrt's x >= 0), and with "
     "u := x + (1/(sqrt x + 1) - 1/(sqrt x + 1)) (a divisor with an "
     "x-mentioning sqrt)",
     "E26 made step 10 charge closed domains (sqrt, asin, acos, acosh), and "
     "step 9 (a) checked H only, so a rewrite below D[x] whose R carried "
     "one was accepted, leaving the equation's domain in x closed: the case "
     "§6.1 rev 9 and step 9 (a)'s subterm clause exist to refuse. The gap "
     "predates E26 through a divisor such as 1/(sqrt x + 1), which step 10 "
     "charged but step 9 never tested. No verdict could be reached from it "
     "in this milestone (E26 (b) refuses ring and field on a side holding "
     "a D), so it was latent. No P1 rewrite is under a D, so no P1 result "
     "changes. SymPy: both inst values' match normalises to -x, and "
     "D[x] atan(-x) is -1 at 0",
     "user decision 2026-09-24, review fix"),
    ("BAD_MOVES field_refuses_Int, norm_num_refuses_D, "
     "norm_num_refuses_open_Int, divisor_test_refuses_D, match_refuses_D "
     "and ftc_check_refuses_Int (6 cases); the E26 (b) block comment; E7 "
     "and E26 (b) prose; DEFINEDNESS_MUTATIONS field_reads_Int_as_atom and "
     "norm_num_admits_D, and new caught_by locations for "
     "ring_reads_Int_as_atom, ring_reads_D_as_atom and norm_num_admits_Int",
     "the E26 (b) cases now cover every normaliser and node pair (ring, "
     "field and norm_num, each on Int and D) and every call site on both "
     "nodes (close's check, ftc's check, E25's ring_nf(d), the match). "
     "field's fact reduction is covered through field's normaliser and "
     "E7's refusal of the fact's hypothesis, as the block comment says. "
     "E7 now says an obligation holding an Int or D is refused, not "
     "admitted, whether or not it is literal or closed. The mutation table "
     "has 25 entries for E26's table and clause (b), 27 in all with the "
     "two position mutations below",
     "a kernel that skipped the refusal in one uncovered place would pass "
     "the suite and could still give a false verdict: with ftc's check "
     "skipping it, Int[x = 0 .. 1] (1 + ((Int[t = 0 .. oo] 1) - "
     "(Int[t = 0 .. oo] 1))) closed as 'Proved modulo 3 admissions' for an "
     "integrand that diverges. And E7's prose read as 'never literal, so "
     "admitted', which the one closed Int case could not tell from "
     "'refused'; no D obligation was pinned at all. No P1 step normalises "
     "an Int or D, so no P1 result changes. SymPy: the inner integral is "
     "oo, D[x] x^2 = 2x, and Int[t = 0 .. x] t = x^2/2",
     "user decision 2026-09-24, review fix"),
    ("MATCH_ACCEPTS rewrite_R_former_at_position and "
     "limit_former_at_outer_domain; DEFINEDNESS_MUTATIONS "
     "rewrite_R_former_at_goal_domain and limit_former_on_own_range, and "
     "its header",
     "two accepted cases pinning E26's position domain at the sites no "
     "case inspected: ln x in a rewrite's R under Int[x = 1 .. 2] re-owes "
     "x > 0 @ [1, 2] (not new, tagged range), and sqrt y in an Int's hi "
     "owes y >= 0 at the goal's domain y >= 0 (tagged hyp), with no "
     "orientation. Two mutations record what they catch",
     "every case whose R carried a former was at domain true, and no case "
     "had a non-closed builtin in an Int limit, while BAD_MOVES assert "
     "only refusal codes; so a kernel charging R, or a limit, at the "
     "wrong domain emitted keys no assertion inspected. No P1 result "
     "changes (P1.1 s1's R is t; P1's non-literal limits owe only closed, "
     "discharged divisors). SymPy: atan(-ln x) + atan(ln x) = 0, and the "
     "integral is y/2",
     "user decision 2026-09-24, review fix"),
    ("HANDLES_IN_FORCE's comment, DECISIONS E17, the DATA_CHANGES preamble "
     "and its HANDLES_IN_FORCE and DEFINEDNESS entries, the "
     "DEFINEDNESS_MUTATIONS header (comments and strings only; no data "
     "value changed)",
     "question 3's model is marked as decided on the owner's behalf, and "
     "the single-former coverage as a data-review choice, not as the "
     "owner's words",
     "the owner chose option (a) for question 1 and dismissed line-count "
     "budgets; they stated no preference on question 3 and did not ask "
     "for a coverage rule. The data credited them with both",
     "user decision 2026-09-24, review fix"),
    ("VERIFIED",
     "one entry appended, for the review fixes' SymPy checks",
     "the record of the checks behind the review fixes above",
     "user decision 2026-09-24, review fix"),
    ("E12's d_const bullet; E9; E26 (b); DECISIONS E12 and E26; "
     "REFUSAL_CODES['Int-or-D-not-normalisable']; GRAMMAR.md §3's definedness "
     "paragraph; BAD_MOVES ftc_F_holds_x_free_Int and ftc_F_holds_x_free_D; "
     "DEFINEDNESS_MUTATIONS deriv_d_const_on_Int_or_D",
     "d_const no longer fires on an x-free subterm holding an Int or Deriv "
     "node: deriv refuses the step 'Int-or-D-not-normalisable' there. The "
     "test sits inside the d_const branch, so an Int or D with x free still "
     "gets 'deriv-no-rule' (ftc_F_contains_D unchanged). E26 (b) now binds "
     "deriv as well as ring, field and norm_num, and says an Int or D in "
     "ftc's F is refused in step (iv), so F's reg admissions and ftc_D are "
     "never minted for it. Two cases pin the guard, and one mutation drops "
     "it",
     "E26 (b) bound only the normalisers, while E12 let d_const fire on any "
     "x-free subterm whatever its former, Int and Deriv included. With "
     "goal Int[x = 0 .. 1] 1 == ?A and F := x + ((Int[t = 0 .. oo] 1) - "
     "(Int[t = 0 .. oo] 1)), deriv gave 1 + 0, ring's check passed on sides "
     "holding no Int, and D[x] F == 1 @ (0, 1) was recorded DISCHARGED for "
     "an undefined F. No verdict followed (the new goal still holds the "
     "Ints, which every later close refuses), but a false premise was "
     "discharged. No P1 F holds an Int or D, so no P1 result changes",
     "user decision 2026-09-24, review fix"),
    ("the no-none comment; the E26 (a) note; the section 8b header; "
     "DEFINEDNESS_CASES tan_pi_half and tan_zero_true comments; DECISIONS "
     "E15; the tan_zero_true DATA_CHANGES entry above (comments and strings "
     "only; no tag, key or expected value changed)",
     "each statement that cos u # 0 is tagged none for every u, and that a "
     "PROOFS run containing tan cannot pass the no-none check, now says: "
     "unless the goal's own domain Γ states it, or an order item it "
     "follows from (cos u > 0, cos u < 0), which hyp closes (§5.3 method 1)",
     "by TAG_RULES hyp fires first whenever Γ contains the condition, as in "
     "tan x * 0 == ?A @ cos x # 0, whose tan former is exactly Γ's item. "
     "tan_pi_half and tan_zero_true have Γ empty, so their tags stand; the "
     "general statements had dropped that qualifier",
     "user decision 2026-09-24, review fix"),
    ("E26 (a), the paragraph on why field emits nothing for partial "
     "builtins (comment only)",
     "the justification is a case split: an atom of field's input was "
     "charged where it entered, or is new in deriv's output and either "
     "covered by the rule's side condition (d_sqrt, d_asin, d_acosh, "
     "d_pow_real) or defined wherever u is (d_asinh's sqrt(u^2 + 1)). It "
     "states the check a new §6.3 entry must pass: every partial atom its "
     "output introduces is defined on the rule's side-condition set",
     "the old text said every new atom was covered by its rule's side "
     "condition, and §6.3's d_asinh introduces sqrt(u^2 + 1) with no side "
     "condition. The conclusion held (u^2 + 1 >= 1), the stated reason did "
     "not. Only d_sqrt of these rules is in this milestone, so nothing "
     "changes in behaviour",
     "user decision 2026-09-24, review fix"),
    ("BAD_MOVES ftc_check_refuses_D; DEFINEDNESS_MUTATIONS "
     "ring_reads_D_as_atom caught_by",
     "a case running E26 (b)'s refusal at ftc's check on D nodes: goal "
     "Int[x = -1 .. 1] (1 + (D[x](abs x) - D[x](abs x))) == ?A, ftc F := x "
     "by ring, refused 'Int-or-D-not-normalisable'. ring_reads_D_as_atom is "
     "also caught there",
     "the earlier review fix claimed every call site on both nodes, but no "
     "D case ran at ftc's check; with ftc skipping the refusal, "
     "Int[x = -1 .. 1] (1 + (D[x](abs x) - D[x](abs x))) closed as 'Proved "
     "modulo 3 admissions' for an integrand undefined at x = 0. With it, "
     "the earlier entry's 'every call site on both nodes' is true",
     "user decision 2026-09-24, review fix"),
    ("BAD_MOVES norm_num_refuses_Int_in_domain and "
     "norm_num_refuses_D_in_domain; DEFINEDNESS_MUTATIONS "
     "norm_num_ignores_domain (new), and new caught_by locations for "
     "norm_num_admits_Int and norm_num_admits_D",
     "two install cases whose ln former's proposition x > 0 holds no Int "
     "or D but whose domain, the goal's hypothesis, does: "
     "ln x * 0 == ?A @ x > (Int[t = 0 .. oo] 1) - (Int[t = 0 .. oo] 1) and "
     "ln x * 0 == ?A @ x > D[y] y^2, each refused "
     "'Int-or-D-not-normalisable' at E7. A separate mutation names the "
     "proposition-only test",
     "E7 and E26 (b) say an obligation with an Int or D in its proposition "
     "or its domain is refused, and every E7 case put it in the "
     "proposition, so a kernel testing the proposition only passed the "
     "suite and would admit the obligation, closing by ring as 'Proved "
     "modulo 1 admissions' for a theorem whose hypothesis compares x with "
     "a difference of divergent integrals. The rule is kept as written (one "
     "rule at E7, no second check at installation). No P1 goal has a "
     "non-true domain, so PROOFS are unchanged",
     "user decision 2026-09-24, review fix"),
    ("the BAD_MOVES E26 (b) block comment; field_refuses_D's and "
     "field_refuses_Int's 'why' (comments and strings only)",
     "the block comment now argues why field's divisor test needs no case "
     "of its own: every divisor in field's input was charged at entry, "
     "where E25's ring_nf refuses an Int or D; close's value holds none "
     "(E23); deriv's output holds none (E12's guard); and a fact's "
     "uncharged terms carry any Int or D into a hypothesis E7 refuses. "
     "The two field cases no longer claim to exercise the divisor test. "
     "The block comment also names deriv's d_const and E7's domain half "
     "among the covered call sites",
     "E26 (b) lists field's divisor test as a call site, and field_refuses_D "
     "said 'its divisor test and its normal form both refuse', but neither "
     "field case has a divisor, so the coverage was stated without either "
     "a case or an argument that the case cannot arise",
     "user decision 2026-09-24, review fix"),
    ("MATCH_ACCEPTS rewrite_R_former_at_goal_and_range; "
     "DEFINEDNESS_MUTATIONS rewrite_R_former_on_ranges_only (new), "
     "rewrite_R_former_at_goal_domain caught_by, and the header's and "
     "position comment's counts",
     "an accepted rewrite whose R re-owes a former at P = (y > 0, "
     "x in [1, 2]): Int[x = 1 .. 2] atan(-ln(x + y)) == ?A @ y > 0 with "
     "atan_odd, u := ln(x + y), x + y > 0 tagged range at installation and "
     "re-owed (not new) by the rewrite. The linear key keeps the tags "
     "derivable from TAG_RULES alone. The mutation table now has 30 "
     "entries: 27 for E26's table and clause (b), and three position "
     "mutations",
     "step 7's P is the goal's domain plus the enclosing ranges, and every "
     "accepted rewrite whose R carried a former had Γ = true, so a kernel "
     "charging R on the ranges alone passed: it would emit x + y > 0 @ "
     "x in [1, 2], feasible at x = 1, y = -5 and tagged none. Every P1 "
     "goal's Γ is true, so PROOFS are unchanged",
     "user decision 2026-09-24, review fix"),
    ("VERIFIED",
     "two entries appended, for the second review round's SymPy checks and "
     "the parse and import checks",
     "the record of the checks behind the review fixes above",
     "user decision 2026-09-24, review fix"),
    ("REWRITE_RULE step 9 (b); DECISIONS E11; BAD_MOVES "
     "rewrite_under_D_through_Int_R_former and "
     "rewrite_under_D_through_Int_R_former_ln",
     "step 9 (b)'s test on Int ends mentioning x now applies when step 10 "
     "charges a former from R at the occurrence, not only when H is "
     "non-empty, as 9 (a) already does. Two cases added, the sqrt one and "
     "its ln twin",
     "step 10 charges R at P, which holds each enclosing range closed with "
     "a non-strict lo <= hi (steps 7, E4), so a charge there closes the "
     "equation's domain in x just as an H item does; the text said an "
     "entry with empty H was unaffected. The gap existed before E26 "
     "through a divisor in R. It was latent (E26 (b) refuses ring, field "
     "and norm_num on a side holding a D). No P1 rewrite is under a D, so "
     "no P1 result changes. SymPy: the match normalises to -t, and "
     "D[x] Int[t = 1 .. x] atan(-t) = -atan(x)",
     "user decision 2026-09-24, review fix"),
    ("the E10 comment, DECISIONS E10, E6's entry list, the BAD_MOVES E26 "
     "(b) block comment (comments and strings only)",
     "a step that uses a fact handle now also inherits the formers of the "
     "fact's inst values (E6, E26 (a)), charged at that step's domain; the "
     "statement's own formers are not re-charged. The E26 (b) comment no "
     "longer says sqrt_sq_val is the only fact entry, or that fact insts "
     "go uncharged",
     "under option (a) a fact instance holding ln(-1) is not a theorem, and "
     "§6.2 grounds field's soundness on each fact being one. Without "
     "charging, atan(-3) == ?A with atan_odd u := 3 + 0*ln(-1) closed as "
     "'Proved.'. E10 admits any §6.8 entry, and atan_odd has no hypothesis "
     "to carry the term. P1's only fact inst is 3, which has no formers, "
     "so PROOFS are unchanged",
     "user decision 2026-09-24, option (a), review fix"),
    ("section 3: EVALUATED_RULE and E27_MESSAGES (new), the §9 close "
     "comment, the E16 refl sentence; DECISIONS E27 (new)",
     "E27 added: a value closing a `closed` goal must be fully evaluated, "
     "(a) no subterm still evaluable by an equation entry in force, matched "
     "as E1 matches, with readings for sqrt_sq, atan_odd and sqrt_sq_val, "
     "and (b) no unreduced literal arithmetic, by tests b1-b4 that depend on "
     "no printed order. Refused 'close-not-evaluated', naming the first (a) "
     "offender in pre-order, else the first (b) one, as the residual, with "
     "E27_MESSAGES' two messages. Untrusted, in schema.py beside E23, and "
     "run last in close, after the check and check_goal",
     "the closed whitelist accepted an unevaluated F(b) - F(a), so S2 and "
     "S3 closed citing no §6.8 entry (problems/stage0 FINDINGS 12, "
     "PROOF_OF_LIFE.md's first open finding) and close with the post-ftc "
     "left side was refl again (§9). 'Fully evaluated' is stated as a "
     "property because equality of closed constants is undecidable in "
     "general and both P1.2 forms must stay accepted. Running last keeps "
     "every trusted refusal code as it was and makes the new code mean "
     "'right value, unevaluated form'",
     "user decision 2026-09-24 (evaluated answers); the rule's precise form, "
     "its schema readings, the order in close and the message wording are "
     "choices made in carrying it out"),
    ("REFUSAL_CODES['close-not-evaluated'] (new)",
     "the code E27 refuses with, carrying the offending subterm as its "
     "residual",
     "every refusal needs a stable code (section 8's convention), and the "
     "script's coverage check needs a case naming it (the e27_* BAD_MOVES)",
     "user decision 2026-09-24 (evaluated answers)"),
    ("BAD_MOVES e27_* (29 cases, new); EVALUATED_ACCEPTS (26 cases, new); "
     "all_term_strings (their strings)",
     "28 closes refused 'close-not-evaluated', each with its clause, "
     "offending subterm, entry and message: 11 for (a), among them the "
     "disguised exp(0^2), exp(1 - 1) and exp(x - x), (sqrt 3)^2, "
     "sin(pi/2) inside an answer, atan_odd, sqrt 4, sqrt(pi^2/4), and "
     "P1.1's post-ftc left side at s2; 17 for (b), among them 1 + 1, "
     "2 - 0, 0*pi, 1^2, 2/4, like terms and factors, and P1.1's left side "
     "at s5. One ordering case, e27_check_failed_wins, a wrong unevaluated "
     "value refused close-check-failed. 26 refl closes accepted: the five "
     "current reference answers, eleven evaluated values (-1/2, pi^2/4, "
     "sqrt 2, 2*x, 2*pi/(3*sqrt 3), ...) and ten stated limitations, "
     "ln 2 + ln 3 first",
     "the rule's cases, written with it so the implementation is checked "
     "against the spec and not fitted to it. No existing expected value "
     "changes: every close value already in this file, in problems/stage0 "
     "and in the suite either passes E27 (2, both P1.2 forms, (e_const - "
     "1)/2, 1/2, 0, 2*x, -atan(3), -1, 3, x, pi) or is refused before E27 "
     "runs (t - t + 2 by E19, Int by E23, 0*ln(-1) by E7, f - f by "
     "check_goal's D5-uncalled). BAD_MOVES assert codes, so the e27 fields "
     "and EVALUATED_ACCEPTS need new code in the script. Until schema.py "
     "implements E27, the 28 refusals come back as accepted closes and fail",
     "user decision 2026-09-24 (evaluated answers)"),
    ("DESIGN_DEFECTS, one entry appended (§9, §6.8, §16.3)",
     "§9's closed schema is a whitelist only, so refl returns after ftc, "
     "and §6.8's 'every authored goal terminates in this table' was "
     "enforced by nothing; resolved by E27, for folding into the design",
     "the place this file records what DESIGN.md must change",
     "user decision 2026-09-24 (evaluated answers)"),
    ("VERIFIED, two entries appended",
     "the SymPy checks behind E27's cases, and the scratch cross-check of "
     "their outcomes",
     "the record of the checks behind the entries above",
     "user decision 2026-09-24 (evaluated answers)"),
    ("EVALUATED_RULE (b2); DECISIONS E27; BAD_MOVES "
     "e27_sum_merges_after_normalising, e27_sum_merges_constant_over_two, "
     "e27_sum_merges_atom_term, e27_sum_merges_halves, "
     "e27_sum_merges_constant_cancels, e27_sum_merges_power (new); "
     "EVALUATED_ACCEPTS e27_distinct_monomials (new)",
     "b2 now also refuses a maximal sum whose ring normal form has fewer "
     "monomials than its summands' normal forms have in total; the zero "
     "test stays, and the rational-multiples test is subsumed. Six refused "
     "cases added: 2*(pi + 1) - 2, (e_const + 1)/2 - 1/2, "
     "2*(pi + 1) - 2*pi, (pi + 1)/2 - pi/2, 2*(e_const - 1) - 2*e_const, "
     "(pi + 1)^2 - 1, each clause b2 at the whole value with message "
     "'<value> is unreduced literal arithmetic'; one accepted contrast, "
     "x*exp(x) - exp(x)",
     "review D2: the pairwise multiples test missed merging between "
     "summands that are sums once normalised, so these unevaluated values "
     "were accepted. The count is order-independent, as the rule "
     "requires, and is within the user's decision. It still accepts both "
     "P1.2 forms, (e_const - 1)/2, e_const/2 - 1/2, x*exp(x) - exp(x) and "
     "every EVALUATED_ACCEPTS value, and changes no earlier case's "
     "outcome, clause or reported subterm (scratch re-run)",
     "user decision 2026-09-24 (evaluated answers), review fix"),
    ("EVALUATED_RULE (a2) sqrt_sq_val; DECISIONS E27; BAD_MOVES "
     "e27_sqrt_sq_val_negative_power, e27_sqrt_sq_val_negative_power_3 "
     "(new)",
     "sqrt_sq_val counts at Pow(sqrt b, n) with |n| >= 2, not n >= 2. "
     "(sqrt 2)^(-2) and (sqrt 3)^(-2) are refused, naming sqrt_sq_val",
     "review D3: field with the fact lowers negative powers too, so the "
     "move exists and the values, 1/2 and 1/3 in disguise, are not "
     "evaluated",
     "user decision 2026-09-24 (evaluated answers), review fix"),
    ("EVALUATED_RULE (b) definitions, the negative-power sentence",
     "stated that a non-literal factor Pow(c, n) with n < 0 counts on the "
     "denominator side in every b3 test, not only in (v)",
     "the sentence was ambiguous. Read for (v) only, 1*pi^(-1) would be "
     "refused by b3 (ii); read for every test, it passes, as 1/pi does. "
     "The review took it as accepted. No earlier case has a negative "
     "power in a product, so no outcome changes",
     "user decision 2026-09-24 (evaluated answers), review fix; the "
     "reading chosen on the owner's behalf"),
    ("EVALUATED_RULE Known limitations; EVALUATED_ACCEPTS e27_atan_zero and "
     "e27_negative_power_other_side (new)",
     "added as accepted by design: exp(ln 2), ln(exp 2), ln(e_const^2), "
     "sin(pi), cos(pi), sin(pi/6), atan 0, atan 1, atan(sqrt 3), cos 0, "
     "atan(sqrt 3/3), 4^(1/2), (pi^2)^(1/2), (1/sqrt 3)^2, "
     "(pi*sqrt 3)^2, (pi - 1)*(1 - pi), pi*pi^(-1), 1*pi^(-1), each with "
     "its reason; atan 0 and pi*pi^(-1) pinned",
     "review D4: these are missing §6.8 entries or forms outside the "
     "stated tests, not rule changes. The two rows pin atan_odd's nonzero "
     "clause and the negative-power side, which no case reached",
     "user decision 2026-09-24 (evaluated answers), review fix"),
    ("EVALUATED_RULE, a 'Deliberate canonicalisation' paragraph (new); "
     "DECISIONS E27",
     "states that refusing atan(-1/2) (write -atan(1/2)) and "
     "pi*(1/sqrt 3) (write pi/sqrt 3) is deliberate canonicalisation of "
     "sign and division, within normal form, not evaluation",
     "review D5: the owner keeps the behaviour and wants it stated, so it "
     "is not read as a bug",
     "user decision 2026-09-24 (evaluated answers), review fix"),
    ("BAD_MOVES e27_sqrt_sq_val_cube and e27_power_zero (new)",
     "(sqrt 2)^3 refused, clause a, sqrt_sq_val; pi^0 refused, clause b4",
     "review suite gaps: sqrt_sq_val beyond E1's n = 2 tree case, and "
     "b4's exponent 0, had no case",
     "user decision 2026-09-24 (evaluated answers), review fix"),
    ("VERIFIED, one entry appended",
     "the SymPy and scratch checks behind the review fix",
     "the record of the checks behind the entries above. New counts: "
     "BAD_MOVES e27_* 39 (38 refused 'close-not-evaluated', 14 (a) and 24 "
     "(b), plus the ordering case); EVALUATED_ACCEPTS 29 (5 answers, 12 "
     "accepts, 12 limitations)",
     "user decision 2026-09-24 (evaluated answers), review fix"),
    # discharge spec 2026-09-24: written before any discharge code, from the
    # rules and the data, without reading kernel.py, tagger.py or field.py.
    # Nothing existing was deleted or changed in value; every entry adds.
    ("DECISIONS E28-E34 (new)",
     "the discharge design: the trust split and each method's certificate "
     "(E28), Fourier-Motzkin with a checked Farkas witness in stage 1 "
     "(E29), what the checker does not check (E30), exact values first "
     "(E31), discharge at emission and how the tracker and verdict read "
     "(E32), decided false with 'obligation-decided-false' (E33), the "
     "property test and the switch (E34)",
     "WHAT.md 'Start here' item 1 asks for the expected results before the "
     "code, as the proof-of-life did",
     "discharge spec 2026-09-24; E29 by the owner's decision of "
     "2026-09-24 (FM into stage 1, after the pre-check, no interval "
     "propagation); E33's F1 by §18 Q22 as settled; the rest decided on "
     "the owner's behalf, with F3's reach left as an owner question"),
    ("section 11 (new): OBLIGATION_DECIDED_FALSE, REFUSAL_CODES_DISCHARGE, "
     "REASON_*, EXACT_VALUE_ENTRIES, DECIDED_FALSE_MESSAGES, T_RANGE_PI, "
     "T_LINEAR_E, DISCHARGE_RULE, COUNTERPOINT_CANDIDATES, the certificate "
     "helpers",
     "the rule stated in full, one paragraph per point, the new refusal "
     "code and its messages, the new admission reasons, and the candidate "
     "order that makes F3's message deterministic",
     "so that the tables below are checks of a stated rule and not fitted "
     "to an implementation (as REWRITE_RULE and EVALUATED_RULE are)",
     "discharge spec 2026-09-24"),
    ("DISCHARGE_EXPECTED, DISCHARGE_OBLIGATIONS, DISCHARGE_FINAL_TRACKER, "
     "DISCHARGE_ADMISSIONS, DISCHARGE_VERDICTS (new)",
     "every P1 admission with a §5.3 tag becomes DISCHARGED with that tag "
     "and the certificate given; N becomes 3 in all four proofs (6, 9, 14, "
     "13 before), 'Proved modulo 3 admissions', the three being ftc's Reg "
     "premises (REASON_REG). The per-step lists are derived from "
     "EXPECTED_OBLIGATIONS by one rule and cross-checked at import against "
     "the hand-written tracker",
     "WHAT.md's target: 'every P1 and stage-0 admission tagged with a §5.3 "
     "method becomes discharged', with regularity waiting for item 3",
     "discharge spec 2026-09-24"),
    ("DISCHARGE_MATCH_ACCEPTS, DISCHARGE_OCCURRENCE_CASE, "
     "DISCHARGE_DEFINEDNESS_CASES, DISCHARGE_BAD_MOVES_CHANGED, "
     "DISCHARGE_BAD_MOVES_ADDED, DISCHARGE_UNDECIDED (new)",
     "the cases after discharge. Changed outcomes: OCCURRENCE_CASE 'all' is "
     "refused (t >= 0 @ [-1, 0], F3 at t = -1); tan_pi_half is refused at "
     "installation (F1, cos_pi_half); ln_false_on_goal_domain is refused "
     "at installation (F3, x = -1); ln_true_by_hyp reports 'Proved.'; "
     "BAD_MOVES rewrite_under_D_through_Int and field_zero_divisor are "
     "refused at installation (F3, x = -1 and x = 1), each with a twin "
     "that keeps its original refusal reachable. New: six Q22 refusals "
     "(reversed range by F2, a false quadratic, a divisor after sin_zero, "
     "the pole of 1/x^2 on [-1, 1], ln x with no stated domain, a close "
     "value) and two false-but-undecided admissions",
     "Q22's settlement makes a decided-false obligation refuse its step, "
     "so every case that expected a false admission, or passed one on the "
     "way to its own refusal, had to be re-traced; the pre-discharge "
     "entries stay as the record",
     "discharge spec 2026-09-24"),
    ("DISCHARGE_MUST_REJECT, DISCHARGE_CHECKER_ACCEPTS (new)",
     "31 certificates the trusted checker must refuse (the owner's four "
     "Farkas cases: a negative multiplier, the strict/non-strict mix-up, "
     "a combination that is no contradiction, a constraint not in the "
     "set; and a forged sum of squares, x^2 - x - 1 > 0 on [0, 1], wrong "
     "and infinite interval ends, a pi_pos cite for e_const, product "
     "parity and closed-end children, unproved cite hypotheses, hyp "
     "misuse), each with the obligation's truth and the kernel's outcome "
     "if emitted; 9 nearest valid neighbours it must accept",
     "item 3 of the task and the owner's list for the Farkas checker",
     "discharge spec 2026-09-24; the Farkas four by the owner's decision "
     "of 2026-09-24"),
    ("DISCHARGE_PLANTED_BUGS, DISCHARGE_NEW_PLANTED_BUGS, "
     "DISCHARGE_MUTATION_CHANGES (new)",
     "the five planted bugs and 30 mutations re-traced under discharge "
     "(most N become 3; ftc_derivative_premise_on_closed and "
     "sqrt_open_at_0 now refuse proofs by F3; tracker_drops_one gains two "
     "Reg keys so that N still catches it; pi_pos_not_in_constraint_set "
     "raises N to 4 in P1.1 and the fallback), and 13 new planted bugs, "
     "one per checker rule whose loss could give a false 'Proved', and one "
     "in the search",
     "a discharged key dropped or removed no longer moves N, so the "
     "pre-discharge caught_by lists would silently weaken",
     "discharge spec 2026-09-24"),
    ("DISCHARGE_PROPERTY_TEST, DISCHARGE_SWITCH (new)",
     "the soundness property test's requirements, and how the suite moves "
     "to the DISCHARGE_* tables in two green commits",
     "item 4 of the task, and E34",
     "discharge spec 2026-09-24"),
    ("DESIGN_DEFECTS, six entries appended; VERIFIED, one entry appended",
     "§17's stage-1 exclusion of FM and §15.2 item 5 (to update for E29), "
     "§5.3's pre-check paragraph and its method 4/5 preconditions, §5.4's "
     "admission reasons, and §18 Q22's reach; the SymPy checks behind "
     "section 11",
     "the places this file records what DESIGN.md must change, and the "
     "record of the checks",
     "discharge spec 2026-09-24"),
    # discharge spec 2026-09-24, owner answers: the owner's answers of
    # 2026-09-24 to the spec's five questions, carried out by hand before
    # any code. Existing pre-discharge values are unchanged; the E27 cases
    # that the new entries change are staged in DISCHARGE_E27_CHANGES.
    ("DECISIONS E35 (new); E33's text",
     "the five answers recorded with the owner as source: F3 keeps full "
     "reach; the pre-check stays untrusted; cos_zero and sqrt_zero pinned "
     "now; one refusal code with a message saying how; the bounded search "
     "accepted. E33 no longer calls F3's reach an owner question, and its "
     "examples follow the new entries",
     "owner answers of 2026-09-24",
     "discharge spec 2026-09-24, owner answers"),
    ("EXACT_VALUE_ENTRIES, DISCHARGE_NEW_ENTRIES (new), T_NORM_NUM_COS0 "
     "(new)",
     "cos_zero : cos 0 == 1 and sqrt_zero : sqrt 0 == 0 pinned in "
     "NAMED_ENTRIES' shape for entries.py, appended after e_gt_one, and "
     "added to the exact values (ten)",
     "E35 (3)",
     "discharge spec 2026-09-24, owner answers"),
    ("DECIDED_FALSE_MESSAGES, _point and every F3 message",
     "F3's template now says how the point decided it: 'where it reads "
     "{reading}', 'where with {entries} it reads {reading}', or 'where its "
     "negation ... holds (...)'; every F3 message in section 11 gained its "
     "reading (and entries where used)",
     "E35 (4): one code, the message saying how it was decided",
     "discharge spec 2026-09-24, owner answers"),
    ("DISCHARGE_DEFINEDNESS_CASES tan_zero_true; DISCHARGE_UNDECIDED; "
     "DISCHARGE_BAD_MOVES_ADDED decided_false_sqrt_at_end (new); "
     "DISCHARGE_MUST_REJECT cite_hypothesis_unproved's if_emitted",
     "tan_zero_true: cos 0 # 0 DISCHARGED ('norm_num', ('cos_zero',)), "
     "'Proved.' (was admitted none). sqrt x # 0 @ [0, 1] is decided false "
     "by F3 at x = 0, where with sqrt_zero it reads 0 # 0, so "
     "Int[x = 0 .. 1] 1/sqrt x is refused at installation (was an "
     "undecided admission, now moved to the refusals); the true-undecided "
     "example is now 0*tan 1's cos 1 # 0",
     "E35 (3)",
     "discharge spec 2026-09-24, owner answers"),
    ("DISCHARGE_E27_CHANGES (new); comments at EVALUATED_ACCEPTS "
     "e27_no_entry_in_force and BAD_MOVES e27_goal_lhs_before_close; "
     "EVALUATED_RULE (a), (a1) and Known limitations, prose",
     "staged for the commit that pins the entries: e27_no_entry_in_force "
     "(cos 0 accepted) removed from EVALUATED_ACCEPTS; e27_goal_lhs_before_"
     "close now refused at cos 0 naming cos_zero, clause a (was b2 at the "
     "root); new e27_cos_zero ('cos 0 can still be evaluated (cos_zero)') "
     "and e27_sqrt_zero ('sqrt 0 can still be evaluated (sqrt_sq)', "
     "sqrt_sq preceding sqrt_zero in ENTRIES). The prose names the two "
     "entries and moves cos 0 out of the limitations",
     "E35 (3). Staged, not applied in place: E27 reads entries.ENTRIES, so "
     "changing the asserted cases before entries.py holds cos_zero would "
     "turn the suite red. No reference proof or accepted answer is "
     "affected (VERIFIED)",
     "discharge spec 2026-09-24, owner answers"),
    ("DISCHARGE_SWITCH (1), DISCHARGE_PLANTED_BUGS "
     "ftc_derivative_premise_on_closed's note, section 11b's settled-"
     "question comments, two DESIGN_DEFECTS entries' wording",
     "commit (1) also pins the entries and applies DISCHARGE_E27_CHANGES; "
     "under the planted bug the fallback now has two refutable keys and x > "
     "0, emitted first (ARCHITECTURE.md §4), is the one named; comments "
     "that called F3's reach an owner question now cite E35 (1); the §5.4 "
     "defect's false-but-undecided example is x - 5 # 0 @ [0, oo), and the "
     "Q22 defect records the owner's settlement",
     "E35",
     "discharge spec 2026-09-24, owner answers"),
    ("VERIFIED, one entry appended",
     "the re-run SymPy checks for the owner's answers",
     "the record of the checks",
     "discharge spec 2026-09-24, owner answers"),
    ("DISCHARGE_NEW_ENTRIES' positions, EXACT_VALUE_ENTRIES' order, "
     "DISCHARGE_E27_CHANGES e27_sqrt_zero, EVALUATED_RULE (a) and (a1) "
     "prose, DISCHARGE_SWITCH (1), DISCHARGE_ORDER_CHECK (new)",
     "sqrt_zero is inserted immediately before sqrt_sq (so it is the first "
     "entry) and cos_zero appended last, after exp_one; e27_sqrt_zero now "
     "names sqrt_zero: 'sqrt 0 can still be evaluated (sqrt_zero)' (it "
     "named sqrt_sq, which the earlier owner-answers entry recorded); "
     "EXACT_VALUE_ENTRIES listed in the new ENTRIES order",
     "the main session's choice, so that sqrt 0 names the direct move. "
     "Re-checked by hand (DISCHARGE_ORDER_CHECK): no other E27 case, "
     "exact-value rewrite or entries-order-dependent expectation changes",
     "discharge spec 2026-09-24, owner answers"),
    ("PLANTED discharge bug farkas_any_fact's caught_by; DISCHARGE_MUST_REJECT farkas_schema_entry_as_fact (new)",
     "farkas_any_fact is now caught at the new case farkas_schema_entry_as_fact (sqrt a # 0 @ [0, 1] with a sqrt_pos 'fact'), not at farkas_non_fact_entry",
     "the build (commit 1 of DISCHARGE_SWITCH) showed farkas_non_fact_entry cannot isolate the mutation: with the fact rule dropped its combination -pi/2 + (1/2)*sqrt a is still no constant, so it is rejected anyway. In the new case the entry's atom is the proposition's, so only the fact rule stops the false claim; it is false at a = 0 (sqrt_zero). Checked by the main session",
     'adjudicated during implementation'),
    ("PLANTED discharge bug farkas_swaps_interval_ends's caught_by",
     "('N', 'P1.2') removed; the bug stays caught at farkas_constant_not_contradiction, N for P1.1 and P1.1-fallback, and the farkas property test",
     "the wiring build (commit 2) showed P1.2's count does not move: on [0, 1] the swapped lower-end label gives x - 1 >= 0, a stronger constraint, and -(1 + x) + (x - 1) = -2 still refutes each range key's negated goal, so the certificates stay accepted. The spec's reasoning holds only where the upper end is not a rational constant. Checked by the main session",
     'adjudicated during implementation'),
    ("COUNTERPOINT_CANDIDATES: a 256-point bound, and definedness of the domain items at the point",
     "F3 walks at most the first 256 points in candidate order, and a miss is admitted, tagged none; a point counts only where the formers of the proposition and of every domain item are settled true",
     "skeptic review of the wired discharge (b99972e). The Cartesian product was exponential in the variable count (9 variables took 30 s inside install); E35 (5) already accepts misses. Separately, F3 named a counter-point where a domain item was itself undefined, refusing a key that is true where it is defined; 'keeps every term defined' is now stated to cover the domain items. No expected outcome in the spec changes: every refusal's point is within the first 256, and none relies on an undefined domain item",
     'discharge review fix 2026-09-24'),
    # int_subst spec 2026-09-24: written before any code, without reading
    # kernel.py. Additions only; no existing expected value, table or case
    # changes, and nothing new is asserted until the build (E44).
    ("DECISIONS E36-E44 (new)",
     "int_subst's args and step() composition (E36), forward direction "
     "only (E37), premises and their domains (E38), the in-step endpoint "
     "equations (E39), orientation and decreasing phi (E40), phi' from "
     "deriv (E41), freshness, scope, capture and E19 unchanged (E42), the "
     "interaction with discharge, E26 and E27 (E43), and staging (E44)",
     "WHAT.md 'Start here' item 1: the spec for int_subst before any code",
     "int_subst spec 2026-09-24"),
    ("section 12 (new): INT_SUBST_MOVE, INT_SUBST_ARGS, "
     "REFUSAL_CODES_INT_SUBST, INT_SUBST_MESSAGES, SOURCES_INT_SUBST, "
     "DISCHARGE_METHODS_INT_SUBST, T_RING and its two cited forms, "
     "INT_SUBST_RULE",
     "the move stated in full, step by step: six new refusal codes with "
     "message templates, four new sources, the in-step check's tags",
     "E36-E43, stated as REWRITE_RULE and DISCHARGE_RULE are, so the "
     "tables are checks of a rule and not fitted to an implementation",
     "int_subst spec 2026-09-24"),
    ("section 12 (new): INT_SUBST_PROOFS['P1.1-sheet'], INT_SUBST_DERIV, "
     "INT_SUBST_OBLIGATIONS, INT_SUBST_EXPECTED, INT_SUBST_FINAL_TRACKER, "
     "INT_SUBST_ADMISSIONS, INT_SUBST_VERDICTS, INT_SUBST_ANSWERS, "
     "INT_SUBST_NUMERIC",
     "P1.1 from the sheet's goal Int[x = 0 .. pi^2/4] sin(sqrt x) == ?A: "
     "s1 int_subst x := t^2 over t in [0, pi/2], then P1.1's six steps; 15 "
     "keys, 5 admitted (two int_subst Reg, three ftc Reg), 'Proved modulo "
     "5 admissions', theorem Int[x = 0 .. pi^2/4] sin(sqrt x) == 2",
     "WHAT.md: 'P1.1 then starts from the sheet's own goal'; §11.1's "
     "obligation list, derived by hand under INT_SUBST_RULE",
     "int_subst spec 2026-09-24"),
    ("section 12 (new): INT_SUBST_ACCEPTS, INT_SUBST_BAD_MOVES",
     "three accepted moves (decreasing phi with literal ends, continued to "
     "'Proved modulo 5 admissions'; a non-monotone phi; ln's endpoints by "
     "exact values) and eighteen refusals (freshness three ways, scope "
     "twice, no integral under D[y], wrong variable, infinite endpoint, a "
     "supplied phi', two endpoint mismatches including §8.1's sin guess, "
     "phi undefined on the new range, the non-monotone divergent case, a "
     "decreasing phi with symbolic ends, subst-under-D twice, an Int in "
     "phi, and a close naming the new variable)",
     "item 3 of the task: must-refuse cases with exact codes and messages",
     "int_subst spec 2026-09-24"),
    ("section 12 (new): INT_SUBST_PLANTED_BUGS, INT_SUBST_SEAMS, "
     "INT_SUBST_SWITCH, and an import-time cross-check",
     "seven planted bugs for the move's rules, three existing seams "
     "re-traced on P1.1-sheet and SUB1, and how the suite switches in one "
     "commit with PROOFS and every DISCHARGE_* table untouched",
     "E44: a spec must say what catches each rule's loss, and the suite "
     "must stay green until the build",
     "int_subst spec 2026-09-24"),
    ("DESIGN_DEFECTS, five entries appended; VERIFIED, one entry appended",
     "§5.1's decreasing-phi claim against E4 and F2; §8.1/§8.6's sin guess "
     "shown legal though its endpoint fails, and §8.6's probe value; §8.5's "
     "chain-rule row naming a move the table lacks; §11.1's conjunction and "
     "its missing 2 # 0; §6.4 silent on where phi' and its side conditions "
     "live, and deriv's C^1 as sufficient, not necessary",
     "the places this file records what DESIGN.md must change, and the "
     "record of the checks",
     "int_subst spec 2026-09-24"),
    # int_subst spec 2026-09-24, owner answers: the owner's answers of 2026-09-24 to the spec's five questions,
    # carried out by hand before any code. Existing P1 and stage-0
    # expectations are unchanged (SQRT_FACT_CHANGES); int_subst's own
    # staged cases change where listed.
    ("DECISIONS E45-E49 (new); E36, E37, E40, E42 and E44 amended (a "
     "closing sentence each)",
     "reverse mode (E45), the flipped orientation (E46), P1.1-sheet staged "
     "(E47), the position selector (E48), sqrt_nonneg (E49); E37's "
     "forward-only and E40's refusal of symbolic decreasing phi are "
     "superseded, E36's top-level-only and E42's scope made relative to the "
     "position, E44's owner question answered",
     "the owner's answers 1-5 of 2026-09-24",
     "int_subst spec 2026-09-24, owner answers"),
    ("section 12: INT_SUBST_ARGS_REVERSE, INT_SUBST_OPTIONAL, "
     "INT_SUBST_MODES (new); REFUSAL_CODES_INT_SUBST (three codes added: "
     "int-subst-ambiguous, int-subst-orientation-undecided, "
     "int-subst-check-failed; two descriptions reworded); "
     "INT_SUBST_MESSAGES (four templates added; wrong-variable gains a "
     "'/none' form, no-integral an '/occurrence' form); SOURCES_INT_SUBST "
     "(int_subst_integrand added, two reworded); T_RING_COS_PI_HALF, "
     "T_RING_COS_ZERO, T_LINEAR_SQRT, SQRT (new); INT_SUBST_RULE rewritten",
     "the rule now has both modes, the selector and P, the D test, the "
     "orientation decision and the flip, and the soundness at a position; "
     "its step numbers changed (the old 2-15 are the new 2-16 with "
     "selection, the D test and the reverse check inserted)",
     "E45, E46, E48",
     "int_subst spec 2026-09-24, owner answers"),
    ("INT_SUBST_BAD_MOVES decreasing_symbolic_ends (removed), "
     "no_integral_under_D (refusal changed), wrong_variable (message "
     "changed)",
     "decreasing_symbolic_ends was refused 'obligation-decided-false' on "
     "pi/2 <= 0 and is now INT_SUBST_ACCEPTS "
     "decreasing_symbolic_ends_flipped; no_integral_under_D was "
     "'int-subst-no-integral' and is now "
     "'rewrite-under-D-needs-open-domain'; wrong_variable's message is "
     "the '/none' template, since no occurrence is given",
     "E46: a discharged reverse order flips; E48: the Int is selected "
     "anywhere, and below D[y] the D test refuses it; E48's default",
     "int_subst spec 2026-09-24, owner answers"),
    ("INT_SUBST_ACCEPTS: six cases added (decreasing_symbolic_ends_flipped, "
     "cos_theta_canonical, cos_theta_full, sum_second_occurrence, "
     "under_D_constant_integral, reverse_non_monotone); "
     "INT_SUBST_BAD_MOVES: nine added (no_integral_anywhere, "
     "ambiguous_default, occurrence_out_of_range, under_D_body_mentions_y, "
     "orientation_undecided, reverse_g_undefined, holpy_probe_reverse, "
     "reverse_f_mentions_old_variable, f_in_forward_mode)",
     "the owner's requested cases: the canonical x := cos theta (with "
     "cos_pi_half and cos_zero in the endpoint check), a sum's second "
     "integral, an Int under D refused as rewrite refuses and its accepted "
     "twin, the default with no occurrence, reverse mode's wrong f and "
     "undefined g, and HolPy's reverse probe",
     "owner answers 1, 2 and 4",
     "int_subst spec 2026-09-24, owner answers"),
    ("INT_SUBST_PLANTED_BUGS: int_subst_no_orientation redefined and "
     "re-traced; six added (int_subst_flips_without_decision, "
     "int_subst_occurrence_ignored, int_subst_under_D_unchecked, "
     "int_subst_reverse_skips_check, "
     "int_subst_reverse_premise_on_new_range, sqrt_fact_strict)",
     "no_orientation's catch moved from the removed refusal to the "
     "flipped cases and orientation_undecided; each new rule has a bug "
     "that a case catches",
     "E45, E46, E48, E49",
     "int_subst spec 2026-09-24, owner answers"),
    ("SQRT_NONNEG_ENTRY, SQRT_FACT_RULE, SQRT_FACT_CHANGES, "
     "SQRT_FACT_MUST_REJECT, SQRT_FACT_CHECKER_ACCEPTS (new); "
     "INT_SUBST_SWITCH rewritten",
     "the sqrt sign fact pinned, its label and hypothesis argument, the "
     "re-derivation of every key holding a sqrt atom (none changes), two "
     "checker rejections and two acceptances; the switch now carries "
     "entries.py, the checker, the search, the tagger and the property "
     "test's sqrt family, and says P1.1-sheet joins PROOFS after the build",
     "E47, E49",
     "int_subst spec 2026-09-24, owner answers"),
    ("DESIGN_DEFECTS: the §5.1 and §8.5 entries gain the owner's "
     "resolution; three entries appended (§5.3/§6.8 sqrt sign facts, "
     "§6.1/§6.4 int_subst at a position, §5.1's canonical example still "
     "half served); VERIFIED, one entry appended",
     "what DESIGN.md must now say, and the record of the re-run checks",
     "the places this file records what DESIGN.md must change",
     "int_subst spec 2026-09-24, owner answers"),
    ("INT_SUBST_SEAMS pi_pos_not_in_constraint_set",
     "the seam no longer expects P1.1-sheet to finish with 6 admissions and 0 <= pi/2 admitted tagged none; it is caught at P1.1-sheet s1 as a refusal (int-subst-orientation-undecided)",
     "the int_subst build showed the old expectation contradicts E46: [0, pi/2] is not a literal range, so s1 must prove one order of the new limits to choose the new integral's form, and without pi's sign fact neither is proved, so s1 is refused. Checked by the main session against E46's text",
     'adjudicated during implementation'),
    # int_subst review 2026-09-24: the skeptic's review of the int_subst build (ed40695). E50 is
    # the main session's decision; the expectation changes it makes are
    # staged in F3_ROOTS_CHANGES, and every new case in section 12b, so the
    # committed suite stays green until the build.
    ("DECISIONS E50 (new); COUNTERPOINT_CANDIDATES, paragraph (4) appended",
     "F3 also tries the rational roots of the proposition's univariate "
     "polynomial pieces, last for each variable, bounded by "
     "ROOT_TEST_BOUND (10^6); owed formers' roots are argued out; "
     "irrational roots stay undecided",
     "the skeptic's false theorem: a pole of a substitution's map (or of "
     "ftc's F) at a rational interior point was admitted tagged none",
     "the main session's decision, within the owner's Q22 decision (E33, "
     "E35 (1))"),
    ("section 12b (new): ROOT_TEST_BOUND, F3_ROOTS_CASES, "
     "F3_ROOTS_UNDECIDED, F3_ROOTS_CHANGES",
     "three refusals with their messages (the skeptic's reproducer, now "
     "refused at its int_subst step on 2*t - 5 # 0 @ [0, 4] at t = 5/2; "
     "ftc alone on x - 5/2 # 0 @ [0, 4] at x = 5/2; t - 2 # 0 @ [0, 3] at "
     "t = 2), the irrational pole t^2 - 2 # 0 @ [0, 2] still admitted none, "
     "and the one existing expectation that changes: DISCHARGE_UNDECIDED's "
     "x - 5 # 0 @ [0, oo) becomes a refusal at x = 5, with every other "
     "false undecided key and every refusal message re-traced unchanged",
     "E50; the task's items 1 and 2",
     "int_subst review 2026-09-24"),
    ("section 12b (new): REVIEW_ACCEPTS, REVIEW_BAD_MOVES, "
     "REVIEW_SQRT_FACT_MUST_REJECT",
     "the skeptic's three test gaps: forward_constant_body_partial_phi (a "
     "constant body, so step 9 alone gives t > 0 its 'former' source), "
     "reverse_symbolic_old_range_oriented and _reversed (reverse mode's "
     "old-range orientation, owed, and refused by F2 when reversed), and "
     "sqrt_fact_label_for_absent_atom (a sqrt label for an absent atom "
     "beside a present one, 'unknown-label')",
     "three mutations (m_no_sub_formers, m_reverse_no_old_orient, "
     "m_sqrt_fact_any_u) passed all 565 checks",
     "int_subst review 2026-09-24"),
    ("section 12b (new): REVIEW_PLANTED_BUGS, REVIEW_SWITCH",
     "f3_no_root_candidates and the three surviving mutations as planted "
     "bugs, each with the new case that catches it; how the tables join "
     "the asserted ones",
     "a rule without a catching case is untested",
     "int_subst review 2026-09-24"),
    ("DESIGN_DEFECTS, two entries appended; VERIFIED, one entry appended",
     "§18 Q22 and §5.4 on F3's reach, Sturm sequences recorded as a future "
     "exact univariate sign method, and §5.4's false-undecided example "
     "moving to t^2 - 2 # 0 on [0, 2]; the record of the checks",
     "the places this file records what DESIGN.md must change",
     "int_subst review 2026-09-24"),
    # consolidation spec 2026-09-24: written before any code; every change to an asserted table is
    # staged (P1_1_SHEET_JOIN, CONSOLIDATION_CHANGES) and applied by the
    # suite at the build, so the committed suite stays green.
    ("DECISIONS E51-E55 (new)",
     "int_flip, in the form Int[x = b .. a] -(f) (decided on the owner's "
     "behalf, with reasons); P1.1-sheet joining PROOFS and ROUTE; the sign "
     "product on non-strict goals; six entries; the route that finishes "
     "Int_0^1 sqrt(1 - x^2) with no extension of field",
     "WHAT.md 'Start here' item 1 and the owner's decisions of 2026-09-24",
     "consolidation spec 2026-09-24"),
    ("section 13a (new): INT_FLIP_MOVE, INT_FLIP_ARGS, INT_FLIP_OPTIONAL, "
     "REFUSAL_CODES_INT_FLIP, INT_FLIP_MESSAGES, INT_FLIP_RULE, "
     "INT_FLIP_ACCEPTS, INT_FLIP_BAD_MOVES",
     "the move stated; a reversed symbolic goal flipped and closed to "
     "-pi^2/4 (modulo 3), a sum's second integral flipped; six refusals "
     "(no integral, ambiguous, occurrence out of range, under D, an extra "
     "argument, a flip creating an unusable reversed range)",
     "the task's item 1",
     "consolidation spec 2026-09-24"),
    ("section 13b (new): P1_1_SHEET_TRACES, P1_1_SHEET_JOIN",
     "P1.1-sheet's merge into PROOFS, ROUTE, ECHO, ANSWERS, NUMERIC, DERIV "
     "and the DISCHARGE_* tables, and its re-trace under all 48 children: "
     "N 5 except farkas_swaps_interval_ends (7); refused by "
     "pi_pos_not_in_constraint_set and search_scales_wrongly (s1) and "
     "sqrt_open_at_0 (installation); new catches for "
     "ftc_derivative_premise_on_closed, tracker_drops_one, "
     "farkas_swaps_interval_ends and no_sqrt_former",
     "the task's item 2 (E47's follow-up); every value derived by hand, "
     "then confirmed by running each seam against the staged proof",
     "consolidation spec 2026-09-24"),
    ("section 13c (new): T_PRODUCT_COS, SIGN_PRODUCT_NONSTRICT_RULE, "
     "SIGN_PRODUCT_CHECKER_ACCEPTS, SIGN_PRODUCT_MUST_REJECT",
     "the non-strict sign product, its search rule, two accepted forms of "
     "1 - x^2 >= 0 @ [0, 1], and three rejections (a factor that changes "
     "sign, the parity, a non-strict factor under a strict target)",
     "the task's item 3",
     "consolidation spec 2026-09-24"),
    ("section 13d (new): CONSOLIDATION_ENTRIES, ATOM_FACT_RULE, ATOM_FACTS, "
     "ATOM, T_CITE_SIN, CONSOLIDATION_CHECKER_ACCEPTS, "
     "CONSOLIDATION_MUST_REJECT, CONSOLIDATION_PLANTED_BUGS, "
     "CONSOLIDATION_CHANGES, CONSOLIDATION_SWITCH",
     "pyth, pyth_cos, sin_nonneg_on, cos_nonneg_on, cos_le_one and "
     "cos_ge_neg_one pinned; how cite and the linear method read them; "
     "their checker cases and planted bugs; the existing expectations the "
     "section changes (product_nonstrict_target's reason, "
     "cos_theta_canonical's two keys now discharged); the switch",
     "the task's items 3-5",
     "consolidation spec 2026-09-24"),
    ("DESIGN_DEFECTS: one entry's closing note; four appended. VERIFIED: one "
     "appended",
     "§5.3 method 5, §6.2/§6.8's pyth and sign facts, E4's reversed "
     "installation, int_flip's form; the record of the checks",
     "the places this file records what DESIGN.md must change",
     "consolidation spec 2026-09-24"),
    # consolidation spec 2026-09-24, owner answers: the owner accepted both of the consolidation spec's
    # recommendations on 2026-09-24. Written before any code; changes to
    # asserted tables are staged in E56_CHANGES.
    ("DECISIONS E51 (closing sentence), E4, E40 and E46 (a superseding "
     "note each), E56 (new)",
     "E51's form Int[x = b .. a] -(f) accepted by the owner (the same "
     "identity, ftc applicable) and its limitation removed; E56: one "
     "orientation rule for every step, the proved order building the "
     "interval, 'orientation-undecided' when neither order is proved, one "
     "code replacing int-subst-orientation-undecided",
     "the owner's answers 1 and 2",
     "owner's answers of 2026-09-24"),
    ("section 13 (staged, amended in place): INT_FLIP_RULE step 4; "
     "INT_FLIP_ACCEPTS flip_reversed_symbolic_to_value's why; "
     "flip_oriented_symbolic_with_former moved from INT_FLIP_BAD_MOVES to "
     "INT_FLIP_ACCEPTS; P1_1_SHEET_TRACES pi_pos_not_in_constraint_set "
     "(refused -> N 5, tag catches) and search_scales_wrongly (its code); "
     "CONSOLIDATION_CHANGES (one entry added); CONSOLIDATION_SWITCH (a "
     "sentence)",
     "E56 makes the flip of an oriented symbolic integral usable; E53, "
     "which the consolidation spec had not traced under the pi_pos seam, "
     "discharges 0 <= pi/2 there by a content split with cite pi_pos",
     "E56; a correction found while re-tracing",
     "consolidation spec 2026-09-24, owner answers"),
    ("section 14 (new): REFUSAL_CODES_E56, E56_MESSAGES, E56_ACCEPTS, "
     "E56_BAD_MOVES, E56_PLANTED_BUGS, E56_CHANGES",
     "two reversed symbolic goals proved by ftc without int_flip (to "
     "-pi^2/8 and -pi^2/4, each modulo 3); a goal whose order is undecided "
     "(refused at installation) and a replacement F2 case; two planted "
     "bugs; every changed expectation with its old and new values",
     "the owner's answer 2 and the task's cases",
     "consolidation spec 2026-09-24, owner answers"),
    ("DESIGN_DEFECTS: one entry's closing note, two appended; VERIFIED: "
     "one appended",
     "E56 for §5.1/§5.3/§6.4, and the E53 consequence the consolidation "
     "spec missed; the record of the checks",
     "the places this file records what DESIGN.md must change",
     "consolidation spec 2026-09-24, owner answers"),
    ("CONSOLIDATION_MUST_REJECT sin_fact_not_a_label if_emitted; SIGN_PRODUCT_NONSTRICT_RULE (a paragraph)",
     "if_emitted's tag drops pi_pos; the rule states that a content of -1 is not split off under a non-strict target",
     "the consolidation build: sin theta >= 0 @ [0, pi/2]'s child theta <= pi is closed by the range alone ((theta - pi, strict) + theta + 2*(pi/2 - theta) = 0), so pi_pos is unneeded; and splitting off -1 under a non-strict target made the one factor restate the key, contradicting the flat certificates the data pins. Checked by the main session",
     'adjudicated during implementation'),
    # consolidation review 2026-09-24: the skeptic's review of the consolidation build (834b8a2);
    # written before any code, staged, no existing expected value changes
    ("DECISIONS E57 (new); E56 (a closing amendment)",
     "E57: rewrite refuses Int-or-D-not-normalisable when an inst value or "
     "the target holds an Int or D node, on every branch, and the principle "
     "that no rule erases one; E56: enclosing ranges in a position domain "
     "are decided (orientation-undecided otherwise), and every order is "
     "decided lazily and memoised",
     "a false plain 'Proved.' through pyth's tree branch; int_subst's "
     "premises on an undecided enclosing range; 30 s to install a goal "
     "whose range no key uses",
     "the main session's decisions, 2026-09-24"),
    ("section 15 (new): E57_RULE, E57_PRINCIPLE, E57_BAD_MOVES, "
     "E57_ACCEPTS, E56_AMENDMENTS, E56_TIMING_BOUND, E56_REVIEW_CASES, "
     "REVIEW2_PLANTED_BUGS, REVIEW2_CHANGES, REVIEW2_SWITCH",
     "both reproducers refused, the sound pyth rewrite on z proved plainly; "
     "every move checked against the principle; the nested reproducer "
     "refused naming a and b, its decided twin accepted; the timing case",
     "the task's items 1-3",
     "consolidation review 2026-09-24"),
    ("CONSOLIDATION_ENTRIES pyth 'use'; DESIGN_DEFECTS §6.2 pyth entry",
     "'neither rewrite nor field can use it as stated' corrected: rewrite "
     "can, at a tree-equal sum, and E57 guards it",
     "the claim was false (the skeptic)",
     "consolidation review 2026-09-24"),
    ("VERIFIED, one entry appended", "the record of the checks",
     "the record of the checks", "consolidation review 2026-09-24"),
    ("DEFINEDNESS_MUTATIONS ring_reads_Int_as_atom and ring_reads_D_as_atom caught_by",
     "('BAD_MOVES', 'match_refuses_Int') and ('BAD_MOVES', 'match_refuses_D') removed; the mutations stay caught at their other three and four locations",
     "the E57 build: step 2a tests the target `at` too, so both cases are refused Int-or-D-not-normalisable before step 3's ring_nf runs, and a ring_nf that reads Int or D as an atom can no longer be observed there; REVIEW2_CHANGES' 'nothing changes' missed this. Checked by the main session",
     'adjudicated during implementation'),
    # second review 2026-09-24: an independent second review of 45132e5; spec only, staged
    ("DECISIONS E57 (amended), E58 (new); E57_PRINCIPLE's ftc and int_flip "
     "rows",
     "ftc, int_subst and int_flip refuse Int-or-D-not-normalisable on a "
     "limit holding an Int or D node, before orientation; 0^0 = 1 for the "
     "integer exponent",
     "the second review's minors 1 and 2 (the main session's decisions)",
     "second review 2026-09-24"),
    ("section 16 (new): SECOND_REVIEW_RULE, SECOND_REVIEW_BAD_MOVES, "
     "E58_ACCEPTS, SECOND_REVIEW_SWITCH",
     "three refusals on Int[x = 0 .. (Int[y = 1 .. oo] 1)] 0 (ftc, reverse "
     "int_subst, int_flip) and two plain 'Proved.' cases (0^0, (x - x)^0); "
     "no existing expectation changes",
     "the task's items 1 and 2",
     "second review 2026-09-24"),
    ("SECOND_REVIEW_BAD_MOVES int_subst_reverse_limit_holds_Int",
     "hi 'Int[y = 1 .. oo] 1' -> '1'; the 'was' note corrected",
     "the second-review build: the old hi holds oo, which INT_SUBST_RULE step 1 refuses bad-args before step 3 reaches the new trees-in-limits test, and on 45132e5 the move was already bad-args, not orientation-undecided. With hi := 1 the selected Int's own upper limit trips the test after step 3. Checked by the main session against INT_SUBST_RULE step 1",
     'adjudicated during implementation'),
    # regularity spec 2026-09-24: written before any code, staged
    # (REG_SWITCH); the old -> new of every changed expectation is in
    # REG_CASE_CHANGES, REG_BAD_MOVES_CHANGED, REG_E57_CHANGES,
    # REG_SUITE_CHANGES, REG_FORGERY_CHANGES and REG_BUG_RETRACE
    ("DECISIONS E59-E70 (new)",
     "regularity's meaning (E59), regularity as a checked discharge method "
     "(E60), the C^0/C^1 rule table with the natural-domain table as its "
     "C^0 sides (E61), soundness per rule (E62), decided false through a "
     "definedness side (E63), §18 Q23's Int and D formers (E64), improper "
     "integrals and diverges deferred (E65), how E26 (b) and E57 change "
     "(E66), int_parts out (E67), every statable Int's order decided at "
     "entry (E68), verdicts (E69), staging (E70); the delegated ones marked "
     "'main session, delegated by the owner 2026-09-24'",
     "WHAT.md 'Start here: regularity, the last piece of stage 1', and the "
     "owner's settlement of §18 Q23",
     "regularity spec 2026-09-24"),
    ("section 17 (new): REG_RULES, REG_C1_EXTRA, REG_SIDES_LISTED, "
     "REG_CERTIFICATE, REG_CHECK_RULE, REG_REASONS, REG_SOUNDNESS, "
     "REG_DISCHARGE_ORDER, REG_TAG_RULE, REG_SEARCH_RULE, FORMER_RULE, "
     "DECIDED_FALSE_MESSAGES_REG, REG_NOT_COVERED, REG_EXPECTED, "
     "REG_STEP_ADDS, REG_NOT_NEW, REG_OBLIGATIONS, REG_FINAL_TRACKER, "
     "REG_ADMISSIONS, REG_VERDICTS, REG_Q23_CASES, REG_Q23_REFUSALS, "
     "REG_E57_CHANGES, REG_E57_ACCEPTS, REG_MUST_REJECT, "
     "REG_CHECKER_ACCEPTS, REG_BAD_MOVES, REG_DECIDED_FALSE, REG_UNDECIDED, "
     "REG_INSTALL_CASES, REG_CASE_CERTS, REG_CASE_ADMITTED, "
     "REG_CASE_CHANGES, REG_BAD_MOVES_CHANGED, REG_SUITE_CHANGES, "
     "REG_BAD_MOVES_ADDED, REG_FORGERY_STATE, REG_FORGERY_CHANGES, "
     "REG_PLANTED_BUGS, REG_BUG_RETRACE, REG_PROPERTY_TEST, REG_SWITCH, "
     "REG_TEXT_CHANGES",
     "every PROOFS proof 'Proved.' with each Reg key's certificate; the "
     "Int formers each proof gains; the atom algebra of Q23 on "
     "Int_0^pi e^x sin x; the pyth reproducers (the D one now owing its "
     "false condition, the divergent one still refused); 22 must-reject "
     "certificates and 17 must-accept neighbours; the FTC-across-a-pole "
     "trap refused by its former and by regularity; 24 planted bugs; every "
     "changed expectation with its old and new value",
     "the task's items 1-6",
     "regularity spec 2026-09-24"),
    ("expected values that change at the switch (not edited in place; "
     "each table named keeps its current value until REG_SWITCH's second "
     "commit)",
     "every Reg row admitted ('reg', ()) 'regularity not built' -> "
     "DISCHARGED ('reg', cites); every PROOFS N 3 or 5 -> 0 and every "
     "verdict -> 'Proved.'; each case's installation list gains its Int "
     "and D formers; BAD_MOVES close_D_goal_scope_passes -> "
     "close-check-failed, divisor_test_refuses_D -> "
     "divisor-normalises-to-zero, ring_refuses_D, field_refuses_D, "
     "match_refuses_D and ftc_check_refuses_D -> accepted (owing their "
     "false D conditions, admitted none), rewrite_under_D_through_Int_R_"
     "former and its ln twin -> orientation-undecided at installation; "
     "E57_BAD_MOVES pyth_erases_D -> accepted, 'Proved modulo 1 "
     "admissions'; E56_REVIEW_CASES int_subst_enclosing_range_undecided "
     "refused at installation, lazy_unused_range_installs deciding its "
     "order; the suite's rewrite_inst_shadows -> shadowing; FORGERIES' two "
     "admission cases on REG_FORGERY_STATE; DEFINEDNESS_MUTATIONS "
     "ring_reads_D_as_atom and field_reads_D_as_atom retired",
     "E64-E69: each traced by hand from the stated rules, listed with its "
     "old value where it is recorded",
     "regularity spec 2026-09-24"),
    ("DESIGN_DEFECTS (six appended), VERIFIED (one appended)",
     "what DESIGN.md must fold in for regularity, and the record of the "
     "checks",
     "the places this file records what DESIGN.md must change",
     "regularity spec 2026-09-24"),
    # regularity build 2026-09-25, adjudicated: the builder's five
    # data_change_requests, each checked against the spec's own rules
    ("INT_SUBST_BAD_MOVES non_monotone_divergent 'message' (amended in "
     "place, old kept as 'was'); REG_BAD_MOVES_CHANGED's 'unchanged, "
     "re-traced' INT_SUBST_BAD_MOVES line",
     "_point('t^2 # 0 @ [-1, 1]', '0^2 # 0', t='0') -> _reg_undefined("
     "'1/t^2 in C^0([-1, 1])', 't^2 # 0 @ [-1, 1]', that point message); "
     "the re-trace line now names the exception; _reg_undefined moves "
     "beside _point so the table can use it",
     "INT_SUBST_RULE step 15 emits step 13's premises before step 14's "
     "formers, and REG_DISCHARGE_ORDER (2r-c) refutes the C^0 premise "
     "Reg(1/t^2, 0, [-1, 1]) through its div side at t = 0 (the same point "
     "and reading); the spec's re-trace missed it. Same code",
     "regularity build 2026-09-25, adjudicated"),
    ("REG_CASE_CHANGES INT_FLIP_ACCEPTS flip_sum_second_occurrence",
     "'certificates' added: {('0 <= pi/2', 'true'): _PI_HALF}",
     "the case adds a DISCHARGED 0 <= pi/2 row, and REG_CASE_CHANGES' own "
     "rule requires every added row's certificate; _PI_HALF is the one "
     "DISCHARGE_EXPECTED pins for that key",
     "regularity build 2026-09-25, adjudicated"),
    ("REG_BUG_RETRACE 'PLANTED_BUGS tracker_drops_one'",
     "'add': (P1.2|P1.2-alt, s2, '1/(1 + x^3) in C^0([0, 1])', 'new'); "
     "'step_lists_changed': True (PLANTED_BUGS' False superseded)",
     "E64 emits that key first at installation, the wrapper drops every "
     "emission, and KEYING reads `new` from the tracker before the step, "
     "so ftc's row at s2 reads new where REG_NOT_NEW says not new; the "
     "other drop keys are each emitted once",
     "regularity build 2026-09-25, adjudicated"),
    ("REG_BUG_RETRACE 'INT_SUBST_PLANTED_BUGS int_subst_no_orientation' "
     "(new)",
     "'drop': (INT_SUBST_BAD_MOVES, orientation_undecided)",
     "E64/E68: step 14's new-integral former decides the order the mutation "
     "skipped and refuses with the case's own code and message (0, 1/y); "
     "still caught at its two INT_SUBST_ACCEPTS locations. "
     "int_subst_flips_without_decision keeps the location (its message "
     "names 1/y and 0)",
     "regularity build 2026-09-25, adjudicated"),
    ("REG_BUG_RETRACE 'REVIEW2_PLANTED_BUGS rewrite_tree_branch_skips_E57' "
     "(new)",
     "'drop': (E57_BAD_MOVES, pyth_erases_D)",
     "REG_E57_CHANGES moved the case to REG_E57_ACCEPTS, where E66 (3) "
     "passes a D node on every branch, so the mutation changes nothing "
     "there; still caught at pyth_erases_divergent_Int",
     "regularity build 2026-09-25, adjudicated"),
    ("SOURCES['former'], DISCHARGE_METHODS ('reg' added), TAG_RULES' reg "
     "paragraph, ADMISSION_METHODS['reg'] (prose, as REG_TEXT_CHANGES "
     "listed)",
     "the stub-phase texts ('tagged by its shape alone', 'only listed in "
     "this milestone') replaced by E60/E64's",
     "REG_SWITCH's second commit names REG_TEXT_CHANGES; the prose is the "
     "spec's to edit, and no check reads it",
     "regularity build 2026-09-25, adjudicated"),
    # regularity review 2026-09-25: spec only, staged (REG_REVIEW_SWITCH)
    ("DECISIONS E63 (amended)",
     "a Reg on an empty domain is refused when a closed side is decided "
     "false, recorded as intended",
     "the review's minor; the main session's decision, delegated by the "
     "owner: E7 treats a closed former the same way, no move emits a Reg "
     "on an empty domain, and the cost is a refusal",
     "regularity review 2026-09-25"),
    ("section 18 (new): REG_SIDE_KEY_RULE, REG_REVIEW_MUST_REJECT, "
     "REG_REVIEW_DECIDED_FALSE, REG_REVIEW_DEEP_CASES, "
     "REG_DEEP_ADMIT_REASONS, REG_REVIEW_PLANTED_BUGS, REG_REVIEW_NOTES, "
     "REG_REVIEW_CHANGES, REG_REVIEW_SWITCH",
     "two must-reject certificates whose hyp side names the item one past "
     "the Reg's domain (child-rejected/unknown-item), the rule that a side "
     "is keyed at exactly with_domain(prop, key.dom), the vacuous-domain "
     "refusal pinned, and three deep-term installs (two that crashed, one "
     "control)",
     "the review's major (the M3 suite gap), its minor, and its crash "
     "note; no existing expected value changes",
     "regularity review 2026-09-25"),
    ("PARSE_REFUSALS: nesting-too-deep (new)",
     "a 200-deep parenthesised sin(...) is refused nesting-too-deep; the parser converts any RecursionError into that ParseError",
     "the regularity review's spec agent found parse_term raising RecursionError on sin(sin(...(x))) at depth ~150-200: a crash in trusted code under E21, since every goal enters through the parser. Converting the overflow (rather than a fixed depth bound) keeps juxtaposed forms that parse at depth 350 working. Main session, delegated by the owner",
     'regularity review 2026-09-25'),
)


# ---------------------------------------------------------------------------
# 11. Real discharge, specified before any code (discharge spec 2026-09-24)
#
# WHAT.md "Start here" item 1. DECISIONS E28-E34 give the design in brief,
# with § references; DISCHARGE_RULE states it in full, one paragraph per
# point, as REWRITE_RULE and EVALUATED_RULE do, so that every table below is
# a check of a stated rule and not fitted to an implementation. Written from
# DESIGN.md revision 10 (§5.3, §5.4, §6.8, §7, §14, §15.2-§15.4, §17, §18
# Q22), ARCHITECTURE.md and the data files, without reading kernel.py,
# tagger.py or field.py. The owner decided on 2026-09-24, while this was
# being written, that Fourier-Motzkin with a checked Farkas witness comes
# into stage 1 (E29).
#
# The pre-discharge tables above (EXPECTED_OBLIGATIONS, FINAL_TRACKER,
# ADMISSIONS, VERDICTS, and the cases' statuses) are kept unchanged. They
# are the record of the stub phase, and the suite asserts them until the
# build switches over, which E34 describes. Nothing below changes any
# goal_after, occurrence count, source, `new` flag or tag of a PROOFS
# obligation: discharge changes statuses, adds a certificate and a reason to
# each obligation, and adds one refusal code.

OBLIGATION_DECIDED_FALSE = "obligation-decided-false"
REFUSAL_CODES_DISCHARGE = {
    OBLIGATION_DECIDED_FALSE:
        "§18 Q22 (settled 2026-09-24), E33: discharge decided a "
        "non-literal obligation false, after §6.8's exact values (F1), by "
        "a certified negation of a closed obligation (F2), or at a "
        "rational counter-point of its domain (F3). An obligation that is "
        "literal as emitted keeps E7's obligation-refuted. Carries no "
        "residual; the message is DECIDED_FALSE_MESSAGES' template",
}

# The reason an admission carries after discharge (ARCHITECTURE.md §2's
# Obligation.reason; ADMISSION_REASON, 'discharge not built', is retired
# with the switch, E34). A discharged obligation's reason is None.
REASON_REG = "regularity not built"          # every Reg key (WHAT.md item 3)
REASON_NONE = "no method decides it"         # tag ('none', ())
REASON_REJECTED = "certificate not accepted"  # tag names a method, but the
# trusted checker refused the search's certificate or none was produced.
# Never expected in an unmutated run: it is what a search bug looks like.
REASON_EMPTY = "domain inconsistent"  # §5.3's pre-check found the key's
# constraint set infeasible, and no method that does not read it (1, 4-6)
# closed the key. Vacuously true, and admitted rather than discharged.

# §6.8's exact values as discharge reads them (E31): every ENTRIES equation
# with no schema variable and no hypothesis. Their current value, for the
# suite to check against entries.ENTRIES rather than as a second list the
# kernel reads.
# In ENTRIES order once the two E35 entries are in (sqrt_zero first,
# cos_zero last); the suite compares it as a set, and E31's rewrite does
# not depend on the order (see DISCHARGE_ORDER_CHECK).
EXACT_VALUE_ENTRIES = ("sqrt_zero",  # E35 (3), before sqrt_sq
                       "sin_pi_half", "cos_pi_half", "sin_zero", "ln_one",
                       "atan_one_sqrt3", "ln_e", "exp_zero", "exp_one",
                       "cos_zero")  # E35 (3), appended last

# E33's messages, one code and a message that says how (E35 (4)). {key} is
# terms.show of the obligation's judgement (so a
# closed key prints without '@ true'), {rewritten} of the judgement after
# the exact values, {negation} of the negated proposition, {tag} is the
# method then its cites joined by ', ', {entries} the entries used joined
# by ', ' in first-use order, and {point} is 'v = q' per variable, sorted by
# name, joined by ', ', each q printed by terms.show(terms.lit(q)).
DECIDED_FALSE_MESSAGES = {
    # F1
    "exact": "{key} is false: with {entries} it reads {rewritten}",
    # F2
    "negation": "{key} is false: its negation {negation} holds ({tag})",
    # F3 (E35 (4), owner answers: the message says how it was decided).
    # {reading} is terms.show of the proposition at the point, the point's
    # values substituted as terms.lit(q) and the exact values applied, not
    # evaluated further: a literal proposition norm_num finds false.
    "point": "{key} is false at {point}, where it reads {reading}",
    "point_exact": "{key} is false at {point}, where with {entries} it "
                   "reads {reading}",
    "point_negation": "{key} is false at {point}, where its negation "
                      "{negation} holds ({tag})",
}

T_RANGE_PI = ("range", ("pi_pos",))
T_NORM_NUM_COS0 = ("norm_num", ("cos_zero",))  # E31 then E7's norm_num
T_LINEAR_E = ("linear", ("e_gt_one",))  # as problems/stage0 defines it

DISCHARGE_RULE = (
    "Scope. Discharge decides every obligation the kernel emits except a "
    "Reg (regularity is item 3 of WHAT.md's stage 1, not built) and ftc's "
    "derivative premise (discharged in-step, E9). It runs at emission, "
    "inside kernel._emit, on the step's buffer, so a refused step changes "
    "nothing (E13) and nothing reaches the tracker until the step has "
    "succeeded (ARCHITECTURE.md §5).",

    "Order at emission. (1) discharged_by given: DISCHARGED with that tag, "
    "as now. (2) A Reg: ADMITTED, ('reg', ()), reason REASON_REG. (3) E7 "
    "unchanged: norm_num decides a literal key (True: DISCHARGED, "
    "('norm_num', ()); False: refused 'obligation-refuted'), and a key "
    "holding an Int or D node is refused 'Int-or-D-not-normalisable' here "
    "and nowhere later (E26 (b)). (4) Exact values (E31): the key is "
    "rewritten with EXACT_VALUE_ENTRIES to a fixed point; if that changed "
    "it and made it literal, norm_num decides it: True gives DISCHARGED "
    "with ('norm_num', entries used), False refuses "
    "'obligation-decided-false' (F1). (5) Certify: the untrusted search "
    "proposes one certificate for the rewritten key, and the trusted "
    "checker decides it; accepted gives DISCHARGED with the tag the "
    "certificate determines, the exact-value entries used prepended to its "
    "cites. (6) Refute (E33): F2 for a closed key, F3 for a key with a free "
    "variable; found refuses 'obligation-decided-false'. (7) Otherwise "
    "ADMITTED with tagger.tag(key, gamma) as now (E24 unchanged) and reason "
    "REASON_EMPTY when the pre-check found the domain inconsistent, else "
    "REASON_NONE when that tag is ('none', ()), else REASON_REJECTED.",

    "The trust split (E28). The search is untrusted and lives beside the "
    "tagger, whose feasibility checks it extends to build the witness they "
    "already find (§7). It tries the methods in §5.3's order, exactly as "
    "TAG_RULES orders them, and hands the checker the first certificate it "
    "builds, with no fallback to a later method if the checker refuses it: "
    "a search bug then shows as an admission with REASON_REJECTED, never as "
    "a different discharge. The checker is trusted (§15.2 item 5) and "
    "small. It never searches. It rebuilds from the key alone everything "
    "it checks against (the constraint set, the target, each "
    "sub-obligation's key), so a certificate can name constraints and "
    "supply witnesses but can never supply a hypothesis. A certificate is "
    "plain data: terms, rationals, labels and nested certificates, and a "
    "field the checker does not know makes it reject. Acceptance implies "
    "the obligation holds at every point of its domain where its terms are "
    "defined; definedness is carried by the separate former keys (E6, "
    "E26). Rejection only withholds a discharge.",

    "Targets. A key's proposition is read as g REL 0 with g a term the "
    "checker builds: a > b gives g = a - b, strict; a >= b gives a - b, "
    "non-strict; a < b gives b - a, strict; a <= b gives b - a, "
    "non-strict. e # 0 needs the certificate's sense: '>' reads it as "
    "g = e, strict, '<' as g = -e, strict, and '#', for a sign product "
    "only, keeps it as g = e # 0; a # 0 certificate without a fitting "
    "sense is rejected. An equation (==) is never a discharge target: "
    "only E7 or F1 decide one, and no P1 or stage-0 obligation is one "
    "except ftc's premise.",

    "The constraint set (methods 2 and 3). Each constraint is a pair "
    "(h, strict) meaning h > 0 or h >= 0, built by the checker and named by "
    "a label. ('goal',): the negated target, (-g, not strict) for a strict "
    "target and (-g, strict) for a non-strict one. ('dom', i, 'lo') and "
    "('dom', i, 'hi'): an Interval item i on v gives (v - lo, open at lo) "
    "and (hi - v, open at hi), each only for a finite end. ('dom', i, "
    "'rel'): a relation item i of the domain (Γ) read as a target is; a "
    "NonZero or == item, and any index the domain does not have, is no "
    "label. ('fact', name): an ENTRIES entry with no schema variable and no "
    "hypothesis whose statement is an ordering between closed terms "
    "(today pi_pos : pi > 0 and e_gt_one : e_const > 1), and only when a "
    "constant it mentions occurs in the key's proposition or domain "
    "(§5.3 rev 9's 'whenever it occurs', TAG_RULES). A label outside this "
    "set rejects the certificate.",

    "Farkas certificate (methods 2 and 3, E29). {'method': 'farkas', "
    "'sense': ..., 'multipliers': {label: rational}}. The checker accepts "
    "iff: every label is in the set; every multiplier is a rational > 0 "
    "(zero is written by omission, a negative one rejects); the ('goal',) "
    "multiplier is present; the sum over labels of multiplier * h, "
    "ring-normalised (atoms and non-linear monomials opaque, as ring "
    "always reads them), is a rational constant k; and that constant "
    "contradicts the sum's relation: k < 0 (the sum is >= 0 or > 0 and "
    "equals a negative number, '0 <= -c with c > 0'), or k = 0 and some "
    "label with a positive multiplier is strict ('0 < 0'). Two non-strict "
    "constraints summing to 0 are no contradiction. The tag is ('range', "
    "cites) when some ('dom', ...) label has a positive multiplier, else "
    "('linear', cites), cites being the facts used in the order pi_pos, "
    "e_gt_one, as TAG_RULES reads them. Linearity is never checked: "
    "ring-normalising the combination is the whole check, and it is sound "
    "for any polynomials over opaque atoms (a positive combination of "
    "non-negative quantities is non-negative). The suite compares the "
    "multipliers exactly, scaled so that ('goal',) has 1; the combination "
    "is an irreducible one (TAG_RULES), which fixes it up to that scale.",

    "The satisfiability pre-check (§5.3, kept by the owner's decision of "
    "2026-09-24, E29). Before Fourier-Motzkin is consulted for a key, the "
    "search runs it on the key's constraint set without ('goal',). If that "
    "set is infeasible, the key's domain is empty in the linear relaxation, "
    "methods 2 and 3 are not attempted for it, and it goes on to methods "
    "4-6 and then to refutation; if nothing closes it, it is admitted with "
    "REASON_EMPTY and E24's tag (the tagger has no pre-check, so that tag "
    "can be 'range'). The pre-check runs in the untrusted "
    "search, because its verdict cannot make a false obligation "
    "discharged: an accepted Farkas witness proves the key on every point "
    "of its domain whatever the pre-check said, vacuously if the domain is "
    "empty. The checker's demand for a positive ('goal',) multiplier "
    "refuses a witness that ignores the proposition altogether; it cannot "
    "refuse one that adds the negated goal to an empty domain's "
    "contradiction, and need not, since that discharge is vacuously true. "
    "What keeps a vacuous discharge from mattering is E4: a range's order is "
    "owed as its own obligation lo <= hi, which is discharged, refuted "
    "(F2) or admitted in its own right.",

    "Hyp certificate (method 1). {'method': 'hyp', 'member': i} or "
    "{'method': 'hyp', 'chain': (i1, ..., in)}. Only relation and NonZero "
    "items of the key's domain count, never an Interval (a range is a "
    "Farkas certificate's). member: the proposition is item i as a tree, "
    "or it is e # 0 and item i is e > 0, e < 0, 0 < e or 0 > e with the "
    "same e. chain: each item read as lo <= hi or lo < hi (a > b and "
    "a >= b flipped to b < a and b <= a); consecutive items link by tree "
    "equality of one's hi and the next's lo; the chain gives lo1 R hin with "
    "R strict iff some link is; the proposition, read the same way, has "
    "the same two ends as trees, and is strict only if R is. e # 0 is "
    "closed by a strict chain from e to 0 or from 0 to e. Tag ('hyp', ()).",

    "Sign certificate (method 4). {'method': 'sign', 'sense': ..., "
    "'const': c0, 'squares': ((c1, s1, k1), ...)}. Accepted iff every ci "
    "is a rational > 0, every ki an even integer >= 2, every si a term with "
    "no MVar, oo, Int or D node, c0 a rational that is > 0 for a strict "
    "target and >= 0 for a non-strict one (E20), and ring_equal(g, c0 + "
    "sum ci*si^ki). The si may hold atoms g does not: the identity is a "
    "polynomial identity over opaque atoms, so it holds whatever value an "
    "atom takes. §5.3's quadratic with negative discriminant is a search "
    "rule only: the certificate is its completed square, (x - 1/2)^2 + 3/4 "
    "for x^2 - x + 1. 'The goal as written first' is also a search rule: "
    "for 1 + ((2*x - 1)/sqrt 3)^2 the certificate is that sum itself. The "
    "suite compares c0 exactly and the squares as a multiset of (ci, ki, "
    "ring normal form of si up to sign). Tag ('sign', ()).",

    "Sign product certificate (method 5). {'method': 'sign product', "
    "'sense': ..., 'content': c, 'factors': ((f1, r1, cert1), ...)}. "
    "Accepted iff the key is a >, < or # 0 key (a non-strict target "
    "rejects, TAG_RULES), c is a rational other than 0, "
    "ring_equal(g, c * f1 * ... * fn), and each fj's sub-obligation holds "
    "by its own certificate: for a # 0 key the sense is '#', rj is '# 0', "
    "and the "
    "sub-obligation is fj # 0; otherwise rj is '>' or '<', the "
    "sub-obligation is fj > 0 or fj < 0, and sign(c) times (-1) to the "
    "number of '<' factors is +1. E18's content split is the one-factor "
    "case. The checker does not check §5.3's 'strictly lower degree': "
    "soundness does not need it, and the checker terminates by structural "
    "recursion on a finite certificate; the degree rule stays the search's "
    "termination rule. The suite compares c exactly and the factors as a "
    "multiset of (ring normal form of fj, rj), each certificate "
    "recursively. The tag is ('sign product', union of the factors' "
    "cites).",

    "Cite certificate (method 6). {'method': 'cite', 'entry': name, "
    "'inst': {var: term}, 'hyps': ((prop, cert), ...)}. Accepted iff the "
    "entry is in ENTRIES and its statement is an ordering or NonZero "
    "judgement (an equation entry rejects); inst binds exactly its schema "
    "variables and every one of them occurs in the conclusion; the "
    "conclusion statement[inst] implies the proposition syntactically as "
    "TAG_RULES defines it (the same tree, or `a > 0` or `0 < a` for a "
    "proposition a # 0, a >= 0 or 0 <= a with the same a); and there is "
    "exactly one child per instantiated hypothesis, in the entry's order, "
    "each accepted at the key's domain. Because every schema variable "
    "occurs in the conclusion and the conclusion is the proposition or its "
    "strengthening, each inst value is a subterm of the proposition, whose "
    "formers were charged where it entered (KEYING), so a cite charges no "
    "former of its own (E10's rule, satisfied by construction). The tag is "
    "('cite', (name,) + the children's cites).",

    "Leaves and children. {'method': 'norm_num'} is accepted only for a "
    "literal proposition that norm_num decides True. A child's key is "
    "built by the checker as terms.with_domain(child proposition, the "
    "parent's domain), so E5 applies (sqrt 3 > 0 has domain true) and a "
    "child can never carry a domain its parent did not have. Children are "
    "decided by the same dispatcher, with the same exact-value step, but "
    "never refuted, and they are never tracker entries (TAG_RULES: "
    "sub-obligations only decide whether the parent's check passes).",

    "Refusals inside discharge. Neither the search nor the checker nor the "
    "refutation raises a refusal of its own. A terms.Refused met inside "
    "any of them (ring meeting an Int or D node, say) counts as a rejected "
    "certificate or as no refutation. Only E7 refuses "
    "Int-or-D-not-normalisable, so DEFINEDNESS_MUTATIONS' norm_num "
    "mutations still show as a changed outcome and are not masked by a "
    "second guard.",

    "Tracker and verdict (E32). An obligation's status is decided once, at "
    "emission, and never changes: no later step adds anything discharge "
    "reads (its only inputs are the key and entries.ENTRIES), so there is "
    "no admitted -> discharged transition to record. Obligation gains a "
    "field `certificate`: the accepted certificate for methods 1-6, None "
    "for norm_num, for the deriv+check premise and for every admission. "
    "`reason` is REASON_REG, REASON_NONE or REASON_REJECTED for an "
    "admission and None otherwise. _Tracker.add is unchanged: a re-emitted "
    "key keeps the status it has, and because discharge is a function of "
    "the key, the re-emission's own status in the step's list is the same "
    "one. report() is unchanged: 'Proved.' exactly when no entry is "
    "ADMITTED, else VERDICT with N the admitted count. With regularity "
    "unbuilt, every proof in PROOFS and every stage-0 proof reads 'Proved "
    "modulo 3 admissions', the three being ftc's Reg premises.",

    "Decided false (§18 Q22, E33). A non-Reg obligation is decided false, "
    "and its step refused 'obligation-decided-false', in exactly three "
    "ways. F1: step (4)'s exact values made it literal and norm_num finds "
    "it false (cos(pi/2) # 0 reads 0 # 0). F2: it is closed (no free "
    "variable, domain true by E5), its proposition is an ordering, and its "
    "negation (a > b to a <= b, a >= b to a < b, a < b to a >= b, a <= b to "
    "a > b) is discharged by steps (3)-(5) at domain true (pi/2 <= 0, whose "
    "negation pi/2 > 0 is linear with pi_pos). A closed e # 0 is decided "
    "false only by F1, since its negation is an equation. F3: it has a "
    "free variable and there is a rational point p, drawn from "
    "COUNTERPOINT_CANDIDATES in their order, such that every domain item "
    "at p (a closed proposition) is discharged by steps (3)-(5), every "
    "former the proposition owes at p (kernel._owed over its subterms, "
    "each closed) is discharged by steps (3)-(5), and the proposition at p "
    "is decided false by F1 (literal after exact values, norm_num False) "
    "or F2. The first such point in candidate order is the one named. "
    "Nothing else is decided false: in particular, a certificate the "
    "checker rejects decides nothing, and an obligation none of F1-F3 "
    "reaches stays ADMITTED, tagged by E24, with its reason.",

    "Decided false is outside the trusted base. It can only refuse a step, "
    "and a refused step changes nothing (E13), so a bug in F1-F3 costs a "
    "wrongly refused step, never a false 'Proved' (§15.2's condition for "
    "trusted code calling untrusted code, argued as ARCHITECTURE.md §1 "
    "argues schema.check_evaluated). It is still checked, so that a wrong "
    "refusal is not a search accident either: each refutation is re-decided "
    "at its point by exact rational evaluation and by the trusted "
    "checkers, and the property test (DISCHARGE_PROPERTY_TEST) re-evaluates "
    "every refutation independently.",
)

# E33 F3's candidate points. Stated so that the message names one point
# deterministically; the search that walks them is untrusted.
COUNTERPOINT_CANDIDATES = (
    "Variables: every free variable of the key (proposition and domain), "
    "sorted by name. Values for a variable v, in this order, a value kept "
    "at its first occurrence only: (1) for each domain item in the "
    "domain's order that bounds v alone against a rational literal c "
    "(an Interval item on v with a rational end, lo before hi, or a "
    "relation item v REL c or c REL v): c when that bound is closed or "
    "non-strict; c + 1 for a strict lower bound and c - 1 for a strict "
    "upper bound; (2) for each Interval item on v whose two ends are both "
    "rational literals, their midpoint; (3) 0, 1, -1. Points: the "
    "Cartesian product in lexicographic order, the first variable "
    "slowest. Irrational or symbolic ends (pi/2, e_const) contribute no "
    "value; the point must still satisfy them, which steps (3)-(5) decide "
    "(0 <= pi^2/4 by sign).",
    # skeptic review of b99972e: the product is exponential in the number of
    # variables (9 variables: 30 s inside install)
    "Bound: the walk visits at most the first 256 points of that order. "
    "A key with no refuting point among them is not decided false, and "
    "is admitted tagged none, as any other miss is (E35 (5)).",
    # skeptic review of b99972e: a counter-point where a domain item is
    # itself undefined refuted a key that is true where it is defined
    "A point counts only where every term is defined: the formers owed by "
    "the proposition AND by every domain item must be settled true at the "
    "point, and a domain item holds there only if it is defined there.",
    # int_subst review 2026-09-24 (E50, the main session's decision)
    "(4) Roots, after (1)-(3) for each variable v: the rational roots of "
    "each polynomial piece of the proposition's target that is univariate "
    "in v with rational coefficients (E50: the target, each factor of a "
    "top-level product, each base of an integer power, recursively), by "
    "the rational root test on the piece's integer coefficients, bounded "
    "by ROOT_TEST_BOUND (10^6) on the lowest nonzero and the leading "
    "coefficient, each kept only where the polynomial is exactly 0, "
    "smallest |r| first and positive before negative, and a root outside "
    "a domain item bounding v against a rational literal dropped. Like "
    "every candidate, a root counts only where the domain and every "
    "owed former are settled true (the paragraph above). An irrational "
    "root is never a candidate.",
)

# Certificate helpers. Labels as DISCHARGE_RULE names them; rationals as
# strings for fractions.Fraction; terms as GRAMMAR.md strings.
GOAL = ("goal",)


def LO(i):
    return ("dom", i, "lo")


def HI(i):
    return ("dom", i, "hi")


def REL(i):
    return ("dom", i, "rel")


def FACT(name):
    return ("fact", name)


def _farkas(mults, sense=None):
    return {"method": "farkas", "sense": sense, "multipliers": dict(mults)}


def _sos(const, squares, sense=None):
    return {"method": "sign", "sense": sense, "const": const,
            "squares": tuple(squares)}


def _product(content, factors, sense=None):
    return {"method": "sign product", "sense": sense, "content": content,
            "factors": tuple(factors)}


def _cite(entry, inst, hyps):
    return {"method": "cite", "entry": entry, "inst": dict(inst),
            "hyps": tuple(hyps)}


def _member(i):
    return {"method": "hyp", "member": i}


def _chain(*items):
    return {"method": "hyp", "chain": tuple(items)}


NORM_NUM_LEAF = {"method": "norm_num"}

# The certificates P1 needs, written once and reused where the same shape
# recurs. Each was derived by hand from DISCHARGE_RULE and re-checked with
# SymPy (VERIFIED).
_RANGE_LO = _farkas({GOAL: "1", LO(0): "1"})           # v - lo against g
_RANGE_LO_NZ = _farkas({GOAL: "1", LO(0): "1"}, ">")    # the same, for # 0
_PI_HALF = _farkas({GOAL: "1", FACT("pi_pos"): "1/2"})  # pi/2 against pi > 0
_PI_SQ = _sos("0", [("1/4", "pi", 2)])                  # (1/4)*pi^2, E20
_QUAD = _sos("3/4", [("1", "x - 1/2", 2)])              # x^2 - x + 1
_QUAD_NZ = _sos("3/4", [("1", "x - 1/2", 2)], ">")
_SQRT3 = _cite("sqrt_pos", {"a": "3"}, [("3 > 0", NORM_NUM_LEAF)])
_ONE_PLUS_X3 = _product("1", [("1 + x", "# 0", _RANGE_LO_NZ),
                              ("x^2 - x + 1", "# 0", _QUAD_NZ)], "#")

# DISCHARGE_EXPECTED[proof][(prop, dom)] = (tag, certificate), for every key
# the pre-discharge FINAL_TRACKER admits with a §5.3 tag. Each becomes
# DISCHARGED with that same tag: the search follows TAG_RULES' order, so
# the method that discharges is the one the tagger named (E28). How each
# was reached:
#   * t >= 0, x >= 0, x > 0, 1 + x > 0 and their # 0 forms on a range with
#     lower end 0: ('goal',) plus the lower end. For t >= 0 on [0, pi/2]:
#     (0 - t, strict) + (t - 0, closed) = 0 with a strict constraint. For
#     1 + x > 0 on [0, 1]: (0 - (1 + x), non-strict) + (x - 0) = -1.
#   * 0 <= pi/2 and pi/2 >= 0: (0 - pi/2, strict) + (1/2)(pi, strict) = 0.
#   * t^2 >= 0, 0 <= pi^2/4, pi^2/4 >= 0: non-strict, constant 0 (E20).
#   * x^2 - x + 1: its completed square, 3/4 + (x - 1/2)^2.
#   * 1 + x^3 # 0: 1 * (1 + x)(x^2 - x + 1), each factor # 0 by its own
#     certificate on the same domain.
#   * sqrt 3 # 0: sqrt_pos with a := 3, whose hypothesis 3 > 0 is literal.
#   * 3*sqrt 3 # 0 and 2*sqrt x # 0: E18's content split, the factor's
#     # 0 by sqrt_pos, whose hypothesis x > 0 on (0, pi^2/4) is range.
#   * Every Farkas key passes the pre-check: [0, pi/2] with pi > 0 at
#     t = 0, pi = 1; (0, pi^2/4) with pi^2 opaque; [0, 1] and (0, 1).
DISCHARGE_EXPECTED = {
    "P1.1": {
        ("t^2 >= 0", "[0, pi/2]"): (T_SIGN, _sos("0", [("1", "t", 2)])),
        ("0 <= pi/2", "true"): (T_LINEAR_PI, _PI_HALF),
        ("t >= 0", "[0, pi/2]"): (T_RANGE, _RANGE_LO),
    },
    "P1.1-fallback": {
        ("x >= 0", "[0, pi^2/4]"): (T_RANGE, _RANGE_LO),
        ("0 <= pi^2/4", "true"): (T_SIGN, _PI_SQ),
        ("x > 0", "(0, pi^2/4)"): (T_RANGE, _RANGE_LO),
        ("2*sqrt x # 0", "(0, pi^2/4)"): (
            T_PRODUCT_SQRT,
            _product("2", [("sqrt x", "# 0",
                            _cite("sqrt_pos", {"a": "x"},
                                  [("x > 0", _RANGE_LO)]))], "#")),
        ("pi^2/4 >= 0", "true"): (T_SIGN, _PI_SQ),
        ("pi/2 >= 0", "true"): (T_LINEAR_PI, _PI_HALF),
    },
    "P1.2": {
        ("1 + x^3 # 0", "[0, 1]"): (T_PRODUCT, _ONE_PLUS_X3),
        ("sqrt 3 # 0", "true"): (T_SQRT_POS, _SQRT3),
        ("1 + x > 0", "[0, 1]"): (T_RANGE, _RANGE_LO),
        ("x^2 - x + 1 > 0", "[0, 1]"): (T_SIGN, _QUAD),
        ("1 + x > 0", "(0, 1)"): (T_RANGE, _RANGE_LO),
        ("x^2 - x + 1 > 0", "(0, 1)"): (T_SIGN, _QUAD),
        ("1 + x # 0", "(0, 1)"): (T_RANGE, _RANGE_LO_NZ),
        ("x^2 - x + 1 # 0", "(0, 1)"): (T_SIGN, _QUAD_NZ),
        ("1 + ((2*x - 1)/sqrt 3)^2 # 0", "(0, 1)"): (
            T_SIGN, _sos("1", [("1", "(2*x - 1)/sqrt 3", 2)], ">")),
        ("1 + x^3 # 0", "(0, 1)"): (T_PRODUCT, _ONE_PLUS_X3),
        ("3*sqrt 3 # 0", "true"): (
            T_PRODUCT_SQRT, _product("3", [("sqrt 3", "# 0", _SQRT3)], "#")),
    },
}
DISCHARGE_EXPECTED["P1.2-alt"] = {
    k: v for k, v in DISCHARGE_EXPECTED["P1.2"].items()
    if k != ("3*sqrt 3 # 0", "true")}
# For a # 0 key the sense of a sign product is written '#': the target is
# g # 0 and every factor's sub-obligation is fj # 0, each decided with its
# own sense.


def _after_discharge(ob, table):
    """A pre-discharge per-step obligation under DISCHARGE_RULE: an
    admission whose key DISCHARGE_EXPECTED lists becomes DISCHARGED, with
    its tag unchanged (asserted below); everything else is unchanged."""
    prop, dom, sources, status, tag, new = ob
    if status == ADMITTED and (prop, dom) in table:
        assert table[(prop, dom)][0] == tag, (prop, dom)
        return (prop, dom, sources, DISCHARGED, tag, new)
    return ob


# The per-step lists after discharge, derived by that one rule from the
# hand-written EXPECTED_OBLIGATIONS. They are cross-checked against
# DISCHARGE_FINAL_TRACKER, which is written out by hand.
DISCHARGE_OBLIGATIONS = {
    proof: {sid: [_after_discharge(ob, DISCHARGE_EXPECTED[proof])
                  for ob in obs]
            for sid, obs in steps.items()}
    for proof, steps in EXPECTED_OBLIGATIONS.items()}

DISCHARGE_FINAL_TRACKER = {
    "P1.1": [
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("t^2 >= 0", "[0, pi/2]", DISCHARGED, T_SIGN),
        ("t >= 0", "[0, pi/2]", DISCHARGED, T_RANGE),
        ("0 <= pi/2", "true", DISCHARGED, T_LINEAR_PI),
        ("2*sin t - 2*t*cos t in C^0([0, pi/2])", "[0, pi/2]", ADMITTED,
         T_REG),
        ("2*sin t - 2*t*cos t in C^1((0, pi/2))", "(0, pi/2)", ADMITTED,
         T_REG),
        ("D[t](2*sin t - 2*t*cos t) == sin t * (2*t)", "(0, pi/2)",
         DISCHARGED, T_DERIV_RING),
        ("sin t * (2*t) in C^0([0, pi/2])", "[0, pi/2]", ADMITTED, T_REG),
    ],
    "P1.1-fallback": [
        ("4 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("x >= 0", "[0, pi^2/4]", DISCHARGED, T_RANGE),
        ("0 <= pi^2/4", "true", DISCHARGED, T_SIGN),
        ("2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^0([0, pi^2/4])",
         "[0, pi^2/4]", ADMITTED, T_REG),
        ("2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^1((0, pi^2/4))",
         "(0, pi^2/4)", ADMITTED, T_REG),
        ("D[x](2*sin(sqrt x) - 2*sqrt x * cos(sqrt x)) == sin(sqrt x)",
         "(0, pi^2/4)", DISCHARGED, T_DERIV_FIELD),
        ("sin(sqrt x) in C^0([0, pi^2/4])", "[0, pi^2/4]", ADMITTED, T_REG),
        ("x > 0", "(0, pi^2/4)", DISCHARGED, T_RANGE),
        ("2*sqrt x # 0", "(0, pi^2/4)", DISCHARGED, T_PRODUCT_SQRT),
        ("pi^2/4 >= 0", "true", DISCHARGED, T_SIGN),
        ("0 >= 0", "true", DISCHARGED, T_NORM_NUM),
        ("pi/2 >= 0", "true", DISCHARGED, T_LINEAR_PI),
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
    ],
    "P1.2": [
        ("1 + x^3 # 0", "[0, 1]", DISCHARGED, T_PRODUCT),
        ("3 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("6 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("sqrt 3 # 0", "true", DISCHARGED, T_SQRT_POS),
        ("3 >= 0", "true", DISCHARGED, T_NORM_NUM),
        ("1 + x > 0", "[0, 1]", DISCHARGED, T_RANGE),
        ("x^2 - x + 1 > 0", "[0, 1]", DISCHARGED, T_SIGN),
        (P1_2_F + " in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
        (P1_2_F + " in C^1((0, 1))", "(0, 1)", ADMITTED, T_REG),
        ("D[x](" + P1_2_F + ") == 1/(1 + x^3)", "(0, 1)", DISCHARGED,
         T_DERIV_FIELD_FACT),
        ("1/(1 + x^3) in C^0([0, 1])", "[0, 1]", ADMITTED, T_REG),
        ("1 + x > 0", "(0, 1)", DISCHARGED, T_RANGE),
        ("x^2 - x + 1 > 0", "(0, 1)", DISCHARGED, T_SIGN),
        ("1 + x # 0", "(0, 1)", DISCHARGED, T_RANGE),
        ("x^2 - x + 1 # 0", "(0, 1)", DISCHARGED, T_SIGN),
        ("1 + ((2*x - 1)/sqrt 3)^2 # 0", "(0, 1)", DISCHARGED, T_SIGN),
        ("1 + x^3 # 0", "(0, 1)", DISCHARGED, T_PRODUCT),
        ("1 + 1 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("1^2 - 1 + 1 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("1 + 0 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("0^2 - 0 + 1 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("3*sqrt 3 # 0", "true", DISCHARGED, T_PRODUCT_SQRT),
        ("2 > 0", "true", DISCHARGED, T_NORM_NUM),
    ],
}
DISCHARGE_FINAL_TRACKER["P1.2-alt"] = (
    [ob for ob in DISCHARGE_FINAL_TRACKER["P1.2"] if ob[0] != "3*sqrt 3 # 0"]
    + [("9 # 0", "true", DISCHARGED, T_NORM_NUM)])

# N after discharge: only ftc's three Reg premises remain, in every proof.
DISCHARGE_ADMISSIONS = {
    "P1.1": 3,           # three regularity (was 6)
    "P1.1-fallback": 3,  # three regularity (was 9)
    "P1.2": 3,           # three regularity (was 14)
    "P1.2-alt": 3,       # three regularity (was 13)
}
DISCHARGE_VERDICTS = {name: VERDICT.format(n=n)
                      for name, n in DISCHARGE_ADMISSIONS.items()}
# Every remaining admission's reason is REASON_REG, and no admission is
# tagged none: the no-none assertion over PROOFS runs still holds.

# The data cross-checks itself when imported, as the E26 source check does.
for _p, _rows in DISCHARGE_FINAL_TRACKER.items():
    _pre = {(r[0], r[1]): r for r in FINAL_TRACKER[_p]}
    assert set(_pre) == {(r[0], r[1]) for r in _rows}, _p
    for _r in _rows:
        _old = _pre[(_r[0], _r[1])]
        assert _r[3] == _old[3], (_p, _r)          # tags unchanged
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

# ---------------------------------------------------------------------------
# 11b. The cases after discharge: what changes in MATCH_ACCEPTS,
#      OCCURRENCE_CASE, DEFINEDNESS_CASES and BAD_MOVES
#
# A case not named here keeps every expected value, with each admission it
# lists that DISCHARGE_* names below turned DISCHARGED. Every BAD_MOVES and
# SUITE_BAD_MOVES case was traced for an installation or earlier emission
# that F1-F3 would now refute before the case's own refusal: two BAD_MOVES
# cases change (DISCHARGE_BAD_MOVES_CHANGED), and each gets a twin that
# keeps its original refusal reachable (DISCHARGE_BAD_MOVES_ADDED). The
# suite's own cases in proof_of_life.py (read, not edited) are literal or
# true where they emit, and none changes.

# A refusal expected from discharge: (template key, parts) filled per
# DECIDED_FALSE_MESSAGES. Keys and terms are GRAMMAR.md strings, printed by
# the suite with terms.show after parsing, never compared as raw strings.
def _point(key, reading, entries=(), **values):
    """An F3 refusal: at the point, `reading` is the literal proposition
    norm_num finds false, after the exact values `entries` (E35 (4))."""
    parts = {"key": key, "point": dict(sorted(values.items())),
             "reading": reading}
    if entries:
        parts["entries"] = tuple(entries)
        return ("point_exact", parts)
    return ("point", parts)


def _reg_undefined(key, cond, inner):
    """E63's refusal (section 17): a Reg decided false through one of its
    C^0 sides, whose own message is `inner`."""
    return ("reg_undefined", {"key": key, "cond": cond, "inner": inner})


def _exact(key, entries, rewritten):
    return ("exact", {"key": key, "entries": tuple(entries),
                      "rewritten": rewritten})


def _negation(key, negation, tag):
    return ("negation", {"key": key, "negation": negation, "tag": tag})


DISCHARGE_MATCH_ACCEPTS = {
    # every listed key becomes DISCHARGED with its tag, no other change
    "ring_cancels_inv_atom": {
        ("x # 0", "[1, 2]"): (T_RANGE, _RANGE_LO_NZ),
        # ring-normalised, the negated goal alone is (-1, non-strict): k < 0
        ("1/x - 1/x + 1 > 0", "[1, 2]"): (T_LINEAR, _farkas({GOAL: "1"})),
    },
    "rewrite_under_infinite_range": {
        ("x^2 >= 0", "[0, oo)"): (T_SIGN, _sos("0", [("1", "x", 2)])),
        # the infinite end gives no constraint; the lower end is enough
        ("x >= 0", "[0, oo)"): (T_RANGE, _RANGE_LO),
    },
    "rewrite_R_former_at_position": {
        ("x > 0", "[1, 2]"): (T_RANGE, _RANGE_LO),
    },
    "rewrite_R_former_at_goal_and_range": {
        # (0 - (x + y), non-strict) + (y, strict) + (x - 1) = -1
        ("x + y > 0", "y > 0, x in [1, 2]"): (
            T_RANGE, _farkas({GOAL: "1", REL(0): "1", LO(1): "1"})),
    },
    "limit_former_at_outer_domain": {
        ("y >= 0", "y >= 0"): (T_HYP, _member(0)),
    },
}

DISCHARGE_OCCURRENCE_CASE = {
    # installation's two t^2 >= 0 keys, not asserted before, now asserted
    "goal_emits": [
        ("t^2 >= 0", "[0, 1]", (S_FORMER,), DISCHARGED, T_SIGN, True),
        ("t^2 >= 0", "[-1, 0]", (S_FORMER,), DISCHARGED, T_SIGN, True)],
    "goal_certificates": {
        ("t^2 >= 0", "[0, 1]"): _sos("0", [("1", "t", 2)]),
        ("t^2 >= 0", "[-1, 0]"): _sos("0", [("1", "t", 2)])},
    # Without `occurrence` the rewrite emits t >= 0 on both ranges, in
    # pre-order: [0, 1] is discharged by range, then [-1, 0] is decided
    # false by F3 at its closed lower end, so the step is REFUSED and the
    # state is unchanged. Before discharge it was accepted with the false
    # key admitted and tagged none: §5.3's own example of 'not a
    # simplification, a rejected step' is now rejected.
    "all": {"refusal": OBLIGATION_DECIDED_FALSE,
            "message": _point("t >= 0 @ [-1, 0]", "-1 >= 0", t="-1")},
    "one": {"emits": [("t >= 0", "[0, 1]", (S_SQRT_SQ,), DISCHARGED,
                       T_RANGE, True)],
            "certificates": {("t >= 0", "[0, 1]"): _RANGE_LO}},
}

DISCHARGE_DEFINEDNESS_CASES = {
    # Q22's own case: installation is refused (F1), so the close never runs.
    # 2 # 0 is emitted first and discharged; the refusal emits nothing.
    "tan_pi_half": {"refusal": OBLIGATION_DECIDED_FALSE, "at": "install",
                    "message": _exact("cos(pi/2) # 0", ["cos_pi_half"],
                                      "0 # 0"),
                    "was": VERDICT.format(n=1)},
    # E35 (3), owner answers: with cos_zero pinned, step (4) rewrites
    # cos 0 # 0 to the literal 1 # 0, which norm_num discharges, citing
    # cos_zero. No certificate (norm_num). The report becomes 'Proved.'.
    # (Before the owner's answer it was true and still undecided; the
    # true-and-undecided example is now DISCHARGE_UNDECIDED's tan 1.)
    "tan_zero_true": {"goal_emits": [("cos 0 # 0", "true", (S_FORMER,),
                                      DISCHARGED, T_NORM_NUM_COS0, True)],
                      "final": [("cos 0 # 0", "true", DISCHARGED,
                                 T_NORM_NUM_COS0)],
                      "report": PROVED,
                      "was": VERDICT.format(n=1)},
    # F3 at the first candidate, x = -1 (the strict upper bound 0, less 1)
    "ln_false_on_goal_domain": {
        "refusal": OBLIGATION_DECIDED_FALSE, "at": "install",
        "message": _point("x > 0 @ x < 0", "-1 > 0", x="-1"),
        "was": VERDICT.format(n=1)},
    # hyp now closes it: the report becomes 'Proved.'
    "ln_true_by_hyp": {"goal_emits": [("x > 0", "x > 0", (S_FORMER,),
                                       DISCHARGED, T_HYP, True)],
                       "certificates": {("x > 0", "x > 0"): _member(0)},
                       "final": [("x > 0", "x > 0", DISCHARGED, T_HYP)],
                       "report": PROVED,
                       "was": VERDICT.format(n=1)},
    # sqrt_closed_end, asin_closed_ends, acos_closed_ends, acosh_closed_end
    # and atanh_interior are literal (E7) and unchanged: 'Proved.'.
}

DISCHARGE_BAD_MOVES_CHANGED = {
    # Installation owes t^2 >= 0 on t in [0, x] (sign, discharged) and the
    # orientation 0 <= x @ true, which is false at x = -1 (F3, the third
    # default candidate). Refused before the rewrite runs. The goal states
    # no domain, and E4's orientation of Int[t = 0 .. x] is false for
    # x < 0: E33 makes the learner state @ 0 <= x (the owner's decision,
    # E35 (1)). The twin below keeps step 9 (b) reachable.
    "rewrite_under_D_through_Int": {
        "refusal": OBLIGATION_DECIDED_FALSE, "at": "install",
        "message": _point("0 <= x", "0 <= -1", x="-1"),
        "was": "rewrite-under-D-needs-open-domain"},
    # Installation's x/x - 1 # 0 @ [1, 2] was admitted none; F3 decides it
    # false at x = 1 (the closed lower end): 1/1 - 1 # 0 owes 1 # 0, true,
    # and reads 0 # 0. The twin keeps field's own E25 test reachable.
    "field_zero_divisor": {
        "refusal": OBLIGATION_DECIDED_FALSE, "at": "install",
        "message": _point("x/x - 1 # 0 @ [1, 2]", "1/1 - 1 # 0", x="1"),
        "was": "divisor-normalises-to-zero"},
}

# New cases, in BAD_MOVES' shape, each with the installation's emissions
# where they are new information.
DISCHARGE_BAD_MOVES_ADDED = [
    {"id": "rewrite_under_D_through_Int_stated",
     "twin_of": "rewrite_under_D_through_Int",
     "goal": "D[x](Int[t = 0 .. x] sqrt(t^2)) == ?A @ 0 <= x",
     "setup": [],
     "move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "t"},
                          "at": "sqrt(t^2)"}),
     "refusal": "rewrite-under-D-needs-open-domain",
     "goal_emits": [
         ("t^2 >= 0", "0 <= x, t in [0, x]", (S_FORMER,), DISCHARGED,
          T_SIGN, True),
         ("0 <= x", "0 <= x", (S_ORIENT,), DISCHARGED, T_HYP, True)],
     "certificates": {("t^2 >= 0", "0 <= x, t in [0, x]"):
                      _sos("0", [("1", "t", 2)]),
                      ("0 <= x", "0 <= x"): _member(0)},
     "why": "the stated domain makes the orientation hyp, so installation "
            "succeeds, and step 9 (b) still refuses: the range [0, x] is "
            "closed in x below D[x] whatever Γ says"},
    {"id": "field_zero_divisor_opaque",
     "twin_of": "field_zero_divisor",
     "goal": "Int[x = 1 .. 2] 1/((x + pi)/(x + pi) - 1) == ?A",
     "setup": [],
     "move": ("ftc", {"F": "x", "check": "field", "facts": []}),
     "refusal": "divisor-normalises-to-zero",
     "goal_emits": [
         # (0 - (x + pi), non-strict) + (x - 1) + (pi, strict) = -1
         ("x + pi # 0", "[1, 2]", (S_FORMER,), DISCHARGED, T_RANGE_PI, True),
         # ring_nf is x*inv(x + pi) + pi*inv(x + pi) - 1, nonzero, so E25
         # installs it; no method closes it (TAG_RULES: none), and F3 finds
         # no point: at every candidate in [1, 2] the proposition keeps pi,
         # is not literal after exact values, and is a # 0, so F2 does not
         # apply. Admitted none, as field_zero_divisor's divisor was.
         ("(x + pi)/(x + pi) - 1 # 0", "[1, 2]", (S_FORMER,), ADMITTED,
          T_NONE, True)],
     "certificates": {("x + pi # 0", "[1, 2]"):
                      _farkas({GOAL: "1", LO(0): "1", FACT("pi_pos"): "1"},
                              ">")},
     "reasons": {("(x + pi)/(x + pi) - 1 # 0", "[1, 2]"): REASON_NONE},
     "why": "field's divisor test finds the numerator of (x + pi)/(x + pi) "
            "- 1 zero (SymPy: cancel gives 0), so ftc is refused "
            "divisor-normalises-to-zero, never ftc-check-failed (E25), "
            "with an opaque atom where F3 cannot evaluate"},
    # §18 Q22's refusals, one per way of deciding false and per place a
    # term enters.
    {"id": "decided_false_reversed_range",
     "goal": "Int[t = pi/2 .. 0] sqrt(t^2) == ?A",
     "setup": [], "move": ("install", {}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _negation("pi/2 <= 0", "pi/2 > 0", T_LINEAR_PI),
     "why": "F2. DOMAIN_RULES E4 said a non-literal reversed range's "
            "orientation is 'refused once discharge exists'. Installation "
            "discharges 2 # 0 (E7) and t^2 >= 0 @ [pi/2, 0] (sign, which "
            "does not read the domain; the pre-check finds that domain "
            "empty, so no Farkas certificate is attempted for it), then "
            "emits pi/2 <= 0: closed, no certificate, and its negation "
            "pi/2 > 0 is linear, (0 - pi/2, non-strict) + (1/2)(pi, strict) "
            "= 0 with a strict constraint"},
    {"id": "decided_false_quadratic",
     "goal": "Int[x = 0 .. 1] ln(x^2 - x - 1) == ?A",
     "setup": [], "move": ("install", {}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("x^2 - x - 1 > 0 @ [0, 1]", "0^2 - 0 - 1 > 0", x="0"),
     "why": "F3 at the first candidate: -1 > 0. The same key as "
            "DISCHARGE_MUST_REJECT sign_false_quadratic, reached through a "
            "move: no search certificate exists (discriminant 5), and a "
            "forged one is rejected there"},
    {"id": "decided_false_after_exact_value",
     "goal": "Int[x = 0 .. 1] 1/sin x == ?A",
     "setup": [], "move": ("install", {}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("sin x # 0 @ [0, 1]", "0 # 0",
                       entries=("sin_zero",), x="0"),
     "why": "F3 composed with F1: at x = 0 the proposition sin 0 # 0 "
            "reads 0 # 0 with sin_zero. ring_nf(sin x) is nonzero, so E25 "
            "installs the divisor"},
    {"id": "decided_false_pole",
     "goal": "Int[x = -1 .. 1] 1/x^2 == ?A",
     "setup": [], "move": ("install", {}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("x^2 # 0 @ [-1, 1]", "0^2 # 0", x="0"),
     "why": "F3 at the range's midpoint, after its two ends pass: the "
            "integrand's divisor is zero inside the range. This is the "
            "FTC-across-a-pole trap stage 0b found HolPy's kernel passing "
            "(§17), refused where the goal is installed, before any ftc. "
            "TAG_RULES tags the key none (x^2 is opaque to FM, has constant "
            "0 on a strict target, and x * x needs x # 0 on [-1, 1])"},
    {"id": "decided_false_sqrt_at_end",
     "goal": "Int[x = 0 .. 1] 1/sqrt x == ?A",
     "setup": [], "move": ("install", {}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("sqrt x # 0 @ [0, 1]", "0 # 0",
                       entries=("sqrt_zero",), x="0"),
     "why": "F3, with F1 at the point (E35 (3), owner answers): at x = 0, "
            "the first candidate (the closed lower end), the domain holds, "
            "the proposition owes sqrt 0's 0 >= 0 (literal, true), and "
            "sqrt 0 # 0 reads 0 # 0 with sqrt_zero. The method search has "
            "nothing (cite sqrt_pos needs x > 0 on [0, 1], itself none). "
            "Installation's other key, x >= 0 @ [0, 1], is discharged by "
            "range; the refusal emits nothing. Before sqrt_zero this key "
            "was admitted none (DISCHARGE_UNDECIDED)"},
    {"id": "decided_false_no_stated_domain",
     "goal": "ln x * 0 == ?A",
     "setup": [], "move": ("install", {}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("x > 0", "0 > 0", x="0"),
     "why": "F3: ln x owes x > 0 at the goal's domain, true, and x = 0 is "
            "the first default candidate. Before discharge this installed "
            "and closed modulo 1 admission tagged none. A goal whose terms "
            "are undefined on part of its stated domain is a wrong goal "
            "(Q22's reason); kept by the owner's decision, E35 (1)"},
    {"id": "decided_false_at_close",
     "goal": "0 == ?A", "setup": [],
     "move": ("close", {"value": "0*sqrt x", "check": "ring",
                        "facts": []}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("x >= 0", "-1 >= 0", x="-1"),
     "why": "F3 on close's value: the scope check, the whitelist and E7 "
            "pass, and the value's sqrt x owes x >= 0 at G, false at -1 "
            "(0 and 1 pass). Charged before the check, so it is not "
            "close-check-failed"},
]

# Obligations discharge decides neither way: admitted, tagged none, with
# REASON_NONE. Each is installed and its installation list asserted; none
# is closed.
DISCHARGE_UNDECIDED = [
    # (undecided_false_sqrt_at_end moved to DISCHARGE_BAD_MOVES_ADDED as
    # decided_false_sqrt_at_end once sqrt_zero was pinned, E35 (3).)
    {"id": "undecided_true_tan_one",
     "goal": "0*tan 1 == ?A",
     "goal_emits": [
         ("cos 1 # 0", "true", (S_FORMER,), ADMITTED, T_NONE, True)],
     "reasons": {("cos 1 # 0", "true"): REASON_NONE},
     "why": "true (cos 1 = 0.5403...), and no rule decides it: no entry "
            "evaluates cos 1 or concludes its sign (cos_nonzero_on waits, "
            "E35 (3)), FM sees an opaque atom, and a closed # 0 has no F2. "
            "The true-but-undecided example tan_zero_true was before "
            "cos_zero"},
    {"id": "undecided_false_unbounded_candidates",
     "goal": "Int[x = 0 .. oo] 1/(x - 5) == ?A",
     "goal_emits": [
         ("x - 5 # 0", "[0, oo)", (S_FORMER,), ADMITTED, T_NONE, True)],
     "reasons": {("x - 5 # 0", "[0, oo)"): REASON_NONE},
     "why": "false at x = 5, but COUNTERPOINT_CANDIDATES gives x only 0, "
            "1 and -1 (the lower end 0 and the defaults), none of them 5: "
            "F3 is a bounded search and says so. The divisor's ring_nf is "
            "nonzero, so E25 installs it"},
]

# ---------------------------------------------------------------------------
# 11c. Must-reject: the trusted checker called directly
#
# Each case hands the checker a key and a certificate, as the search would.
# 'expected' is the checker's verdict, 'rejects_because' the first rule of
# DISCHARGE_RULE the certificate breaks, and 'truth' whether the obligation
# holds on its domain (('false', point) with a point where it fails, or
# ('true',)): a rejected certificate of a true obligation shows the checker
# does not accept a bad witness even for a good claim. 'if_emitted' is the
# kernel's outcome if the same key were emitted, the search offering its
# own certificate: a rejected forged certificate never refuses anything,
# and what happens is decided by the rules, not by the forgery.
DISCHARGE_MUST_REJECT = [
    # Farkas: the owner's four, then the label and end rules.
    {"id": "farkas_negative_multiplier",
     "key": ("x <= 0", "[0, 1]"),
     "cert": _farkas({GOAL: "1", LO(0): "-1"}),
     "rejects_because": "a multiplier is negative",
     "note": "(x - 0, strict) - (x - 0) = 0 with a strict constraint: "
             "accepted if the sign of multipliers were not checked",
     "truth": ("false", {"x": "1"}),
     "if_emitted": ("refused", _point("x <= 0 @ [0, 1]", "1 <= 0", x="1"))},
    {"id": "farkas_nonstrict_pair",
     "key": ("x > 0", "[0, 1]"),
     "cert": _farkas({GOAL: "1", LO(0): "1"}),
     "rejects_because": "k = 0 and no used constraint is strict",
     "note": "the strict/non-strict mix-up: (0 - x, non-strict) + (x - 0, "
             "closed end) = 0 is 0 >= 0, no contradiction. The same "
             "certificate is accepted for x > 0 @ (0, 1) (DISCHARGE_"
             "CHECKER_ACCEPTS farkas_open_end)",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _point("x > 0 @ [0, 1]", "0 > 0", x="0"))},
    {"id": "farkas_constant_not_contradiction",
     "key": ("x >= 1", "[0, 1]"),
     "cert": _farkas({GOAL: "1", LO(0): "1"}),
     "rejects_because": "k = 1 > 0 is no contradiction",
     "note": "(1 - x, strict) + (x - 0) = 1. A checker that read the lower "
             "end with the upper end's value, x - 1 >= 0, would sum to 0 "
             "with a strict constraint and accept a false claim",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _point("x >= 1 @ [0, 1]", "0 >= 1", x="0"))},
    {"id": "farkas_not_constant",
     "key": ("t >= 0", "[0, pi/2]"),
     "cert": _farkas({GOAL: "1", HI(0): "1"}),
     "rejects_because": "the combination pi/2 - 2*t is not a constant",
     "note": "the wrong end of a true obligation's range",
     "truth": ("true",),
     "if_emitted": ("discharged", T_RANGE)},
    {"id": "farkas_label_not_in_set",
     "key": ("x > 0", "x > -1"),
     "cert": _farkas({GOAL: "1", REL(1): "1"}),
     "rejects_because": "the domain has no item 1",
     "note": "the witness a buggy search builds from the claim itself: "
             "with x > 0 as item 1, (0 - x) + (x, strict) = 0 would pass",
     "truth": ("false", {"x": "-1/2"}),
     "if_emitted": ("refused", _point("x > 0 @ x > -1", "0 > 0", x="0"))},
    {"id": "farkas_fact_not_in_set",
     "key": ("e_const > 0", "true"),
     "cert": _farkas({GOAL: "1", FACT("pi_pos"): "1"}),
     "rejects_because": "pi does not occur in the key, so pi_pos is not in "
                        "its set",
     "note": "the Farkas form of 'a cite of pi_pos for e_const'",
     "truth": ("true",),
     "if_emitted": ("discharged", T_LINEAR_E)},
    {"id": "farkas_non_fact_entry",
     "key": ("0 <= pi/2", "true"),
     "cert": _farkas({GOAL: "1", FACT("sqrt_pos"): "1/2"}),
     "rejects_because": "sqrt_pos has a schema variable and a hypothesis, "
                        "so it is no constraint",
     "truth": ("true",),
     "if_emitted": ("discharged", T_LINEAR_PI)},
    {"id": "farkas_schema_entry_as_fact",
     "key": ("sqrt a # 0", "[0, 1]"),
     "cert": _farkas({GOAL: "1", FACT("sqrt_pos"): "1"}, ">"),
     "rejects_because": "sqrt_pos has a schema variable and a hypothesis, "
                        "so it is no constraint; here the entry's own atom is "
                        "the proposition's, so only that rule stops a false "
                        "claim (sqrt a > 0 read as a constraint drops a > 0)",
     "truth": ("false", {"a": "0"}),
     # sqrt_zero at a = 0 reads 0 # 0 (E35 (3))
     "if_emitted": ("refused", _point("sqrt a # 0 @ [0, 1]", "0 # 0",
                                      entries=("sqrt_zero",), a="0"))},
    {"id": "farkas_infinite_end",
     "key": ("x <= 5", "[0, oo)"),
     "cert": _farkas({GOAL: "1", HI(0): "1"}),
     "rejects_because": "an infinite end gives no constraint",
     "truth": ("false", {"x": "6"}),
     # the candidates for x are 0, 1 and -1, and 6 is not among them
     "if_emitted": ("admitted", T_NONE, REASON_NONE)},
    {"id": "farkas_nonzero_item",
     "key": ("x > 0", "x # 0"),
     "cert": _farkas({GOAL: "1", REL(0): "1"}),
     "rejects_because": "a NonZero item gives no constraint",
     "truth": ("false", {"x": "-1"}),
     # x = 0 is not in the domain, 1 satisfies the claim, -1 refutes it
     "if_emitted": ("refused", _point("x > 0 @ x # 0", "-1 > 0", x="-1"))},
    {"id": "farkas_nonzero_without_sense",
     "key": ("1 + x # 0", "[0, 1]"),
     "cert": _farkas({GOAL: "1", LO(0): "1"}),
     "rejects_because": "a # 0 target needs a sense",
     "truth": ("true",),
     "if_emitted": ("discharged", T_RANGE)},
    {"id": "farkas_goal_unused",
     "key": ("x > 5", "x >= 1, x <= 0"),
     "cert": _farkas({REL(0): "1", REL(1): "1"}),
     "rejects_because": "no ('goal',) multiplier",
     "note": "(x - 1) + (0 - x) = -1 proves only that the domain is empty, "
             "which the pre-check exists to catch (§5.3)",
     "truth": ("true",),  # vacuously: the domain is empty
     # The pre-check finds the domain infeasible, so no Farkas certificate
     # is attempted; x - 5 is no sign form or product; no counter-point is
     # in the empty domain. E24's tagger, which has no pre-check, finds the
     # full set infeasible through the two domain items alone: 'range'.
     "if_emitted": ("admitted", T_RANGE, REASON_EMPTY)},
    # Sign certificates
    {"id": "sign_false_quadratic",
     "key": ("x^2 - x - 1 > 0", "[0, 1]"),
     "cert": _sos("-5/4", [("1", "x - 1/2", 2)]),
     "rejects_because": "c0 = -5/4 is not > 0",
     "note": "ring_equal holds: (x - 1/2)^2 - 5/4 = x^2 - x - 1",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _point("x^2 - x - 1 > 0 @ [0, 1]", "0^2 - 0 - 1 > 0", x="0"))},
    {"id": "sign_false_quadratic_forged",
     "key": ("x^2 - x - 1 > 0", "[0, 1]"),
     "cert": _sos("5/4", [("1", "x - 1/2", 2)]),
     "rejects_because": "ring_equal fails: the sum is x^2 - x + 3/2",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _point("x^2 - x - 1 > 0 @ [0, 1]", "0^2 - 0 - 1 > 0", x="0"))},
    {"id": "sign_forged_square",
     "key": ("x^2 - x + 1 > 0", "[0, 1]"),
     "cert": _sos("3/4", [("1", "x + 1/2", 2)]),
     "rejects_because": "ring_equal fails: the sum is x^2 + x + 1",
     "note": "a forged decomposition of a true claim",
     "truth": ("true",),
     "if_emitted": ("discharged", T_SIGN)},
    {"id": "sign_odd_power",
     "key": ("x^3 + 1 > 0", "[-2, 0]"),
     "cert": _sos("1", [("1", "x", 3)]),
     "rejects_because": "k = 3 is odd",
     "truth": ("false", {"x": "-2"}),
     "if_emitted": ("refused", _point("x^3 + 1 > 0 @ [-2, 0]", "(-2)^3 + 1 > 0", x="-2"))},
    {"id": "sign_negative_coefficient",
     "key": ("1 - x^2 > 0", "[-2, 2]"),
     "cert": _sos("1", [("-1", "x", 2)]),
     "rejects_because": "c1 = -1 is not > 0",
     "truth": ("false", {"x": "2"}),
     "if_emitted": ("refused", _point("1 - x^2 > 0 @ [-2, 2]", "1 - (-2)^2 > 0", x="-2"))},
    {"id": "sign_zero_constant_strict",
     "key": ("t^2 > 0", "[0, pi/2]"),
     "cert": _sos("0", [("1", "t", 2)]),
     "rejects_because": "c0 = 0 on a strict target (E20 is for >= only)",
     "truth": ("false", {"t": "0"}),
     # t = 0 is in [0, pi/2] because 0 <= pi/2 is discharged (linear)
     "if_emitted": ("refused", _point("t^2 > 0 @ [0, pi/2]", "0^2 > 0", t="0"))},
    # Sign product
    {"id": "product_forged_factorisation",
     "key": ("1 + x^3 # 0", "[0, 1]"),
     "cert": _product("1", [("1 + x", "# 0", _RANGE_LO_NZ),
                            ("x^2 + x + 1", "# 0",
                             _sos("3/4", [("1", "x + 1/2", 2)], ">"))], "#"),
     "rejects_because": "ring_equal fails: (1 + x)(x^2 + x + 1) is "
                        "x^3 + 2*x^2 + 2*x + 1",
     "note": "both factors' certificates are valid: only the product is "
             "wrong",
     "truth": ("true",),
     "if_emitted": ("discharged", T_PRODUCT)},
    {"id": "product_nonstrict_target",
     "key": ("x^2 >= 0", "[-1, 1]"),
     "cert": _product("1", [("x", ">", _farkas({GOAL: "1", LO(0): "1"})),
                            ("x", ">", _farkas({GOAL: "1", LO(0): "1"}))]),
     "rejects_because": "sign product never closes a non-strict target",
     "truth": ("true",),
     "if_emitted": ("discharged", T_SIGN)},
    {"id": "product_parity",
     "key": ("x^2 - 1 > 0", "(-1, 1)"),
     "cert": _product("1", [("x - 1", "<", _farkas({GOAL: "1", HI(0): "1"})),
                            ("x + 1", ">", _farkas({GOAL: "1", LO(0): "1"}))]),
     "rejects_because": "one '<' factor and content +1 give a negative "
                        "product for a positive target",
     "note": "both children are valid on (-1, 1): the parity rule alone "
             "stops a false claim",
     "truth": ("false", {"x": "0"}),
     # candidates: the open ends give -1 + 1 = 0 and 1 - 1 = 0, so x = 0
     "if_emitted": ("refused", _point("x^2 - 1 > 0 @ (-1, 1)", "0^2 - 1 > 0", x="0"))},
    {"id": "product_child_at_closed_end",
     "key": ("1 - x^2 > 0", "[-1, 1]"),
     "cert": _product("1", [("1 - x", ">", _farkas({GOAL: "1", HI(0): "1"})),
                            ("1 + x", ">", _farkas({GOAL: "1", LO(0): "1"}))]),
     "rejects_because": "the child 1 - x > 0 @ [-1, 1]: (x - 1) + (1 - x) = "
                        "0 with no strict constraint",
     "note": "§5.3's d_asin factorisation on the closed interval, where it "
             "is false; accepted on the open one (DISCHARGE_CHECKER_"
             "ACCEPTS product_open_interval)",
     "truth": ("false", {"x": "1"}),
     "if_emitted": ("refused", _point("1 - x^2 > 0 @ [-1, 1]", "1 - (-1)^2 > 0", x="-1"))},
    # Cite
    {"id": "cite_pi_pos_for_e_const",
     "key": ("e_const > 0", "true"),
     "cert": _cite("pi_pos", {}, []),
     "rejects_because": "the conclusion pi > 0 does not imply e_const > 0",
     "truth": ("true",),
     "if_emitted": ("discharged", T_LINEAR_E)},
    {"id": "cite_wrong_instance",
     "key": ("sqrt 3 # 0", "true"),
     "cert": _cite("sqrt_pos", {"a": "2"}, [("2 > 0", NORM_NUM_LEAF)]),
     "rejects_because": "the conclusion sqrt 2 > 0 does not imply "
                        "sqrt 3 # 0",
     "truth": ("true",),
     "if_emitted": ("discharged", T_SQRT_POS)},
    {"id": "cite_hypothesis_unproved",
     "key": ("sqrt x # 0", "[0, 1]"),
     "cert": _cite("sqrt_pos", {"a": "x"}, [("x > 0", _RANGE_LO)]),
     "rejects_because": "the hypothesis x > 0 @ [0, 1]: (0 - x) + (x - 0) "
                        "= 0 with no strict constraint",
     "truth": ("false", {"x": "0"}),
     # decided_false_sqrt_at_end's key (E35 (3))
     "if_emitted": ("refused", _point("sqrt x # 0 @ [0, 1]", "0 # 0",
                                      entries=("sqrt_zero",), x="0"))},
    {"id": "cite_hypothesis_missing",
     "key": ("sqrt 3 # 0", "true"),
     "cert": _cite("sqrt_pos", {"a": "3"}, []),
     "rejects_because": "sqrt_pos has one hypothesis and no child is given",
     "truth": ("true",),
     "if_emitted": ("discharged", T_SQRT_POS)},
    {"id": "cite_not_syntactic",
     "key": ("pi/2 >= 0", "true"),
     "cert": _cite("pi_pos", {}, []),
     "rejects_because": "pi > 0 gives pi # 0, pi >= 0 and 0 <= pi, not "
                        "pi/2 >= 0 (TAG_RULES' syntactic implication)",
     "truth": ("true",),
     "if_emitted": ("discharged", T_LINEAR_PI)},
    {"id": "cite_equation_entry",
     "key": ("sqrt 4 # 0", "true"),
     "cert": _cite("sqrt_sq", {"u": "2"}, [("2 >= 0", NORM_NUM_LEAF)]),
     "rejects_because": "sqrt_sq is an equation, not an ordering or "
                        "NonZero statement",
     "truth": ("true",),
     # TAG_RULES: sqrt 4 is opaque to FM, no sign form, content 1, and
     # sqrt_pos with a := 4 has the literal hypothesis 4 > 0
     "if_emitted": ("discharged", T_SQRT_POS)},
    # Hyp
    {"id": "hyp_not_member",
     "key": ("x > 0", "x >= 0"),
     "cert": _member(0),
     "rejects_because": "x >= 0 is not x > 0, and a strict claim is no "
                        "weakening of a non-strict item",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _point("x > 0 @ x >= 0", "0 > 0", x="0"))},
    {"id": "hyp_chain_broken",
     "key": ("x < z", "x < y, w < z"),
     "cert": _chain(0, 1),
     "rejects_because": "the link y, w is not one tree",
     "truth": ("false", {"w": "-1", "x": "0", "y": "1", "z": "0"}),
     "if_emitted": ("refused", _point("x < z @ x < y, w < z", "0 < 0", w="-1",
                                      x="0", y="1", z="0"))},
    {"id": "hyp_interval_item",
     "key": ("x >= 0", "[0, 1]"),
     "cert": _member(0),
     "rejects_because": "an Interval item is a range, not a hypothesis",
     "truth": ("true",),
     "if_emitted": ("discharged", T_RANGE)},
    # Leaf
    {"id": "norm_num_leaf_not_literal",
     "key": ("x > 0", "(0, 1)"),
     "cert": NORM_NUM_LEAF,
     "rejects_because": "the proposition is not literal",
     "truth": ("true",),
     "if_emitted": ("discharged", T_RANGE)},
]

# The contrasts: certificates the checker must accept, each the nearest
# valid neighbour of a must-reject case or a form no proof exercises.
DISCHARGE_CHECKER_ACCEPTS = [
    {"id": "farkas_open_end", "key": ("x > 0", "(0, 1)"),
     "cert": _RANGE_LO, "tag": T_RANGE},
    {"id": "product_open_interval", "key": ("1 - x^2 > 0", "(-1, 1)"),
     "cert": _product("1", [("1 - x", ">", _farkas({GOAL: "1", HI(0): "1"})),
                            ("1 + x", ">", _farkas({GOAL: "1", LO(0): "1"}))]),
     "tag": T_PRODUCT},  # §5.3's d_asin case
    {"id": "product_two_negative", "key": ("x^2 - 1 > 0", "(-3, -1)"),
     "cert": _product("1", [("x - 1", "<", _farkas({GOAL: "1", HI(0): "1"})),
                            ("x + 1", "<", _farkas({GOAL: "1", HI(0): "1"}))]),
     "tag": T_PRODUCT},  # two '<' factors, content +1: positive
    {"id": "hyp_chain", "key": ("x < z", "x < y, y <= z"),
     "cert": _chain(0, 1), "tag": T_HYP},
    {"id": "hyp_chain_flipped", "key": ("0 <= x", "x > 0"),
     "cert": _chain(0), "tag": T_HYP},  # x > 0 read as 0 < x, weakened
    {"id": "hyp_nonzero", "key": ("x # 0", "x < 0"),
     "cert": _member(0), "tag": T_HYP},
    {"id": "sign_negative_sense", "key": ("-1 - x^2 # 0", "true"),
     "cert": _sos("1", [("1", "x", 2)], "<"), "tag": T_SIGN},
    {"id": "farkas_gamma_only", "key": ("x + 1 > 0", "x > 0"),
     "cert": _farkas({GOAL: "1", REL(0): "1"}), "tag": T_RANGE},
    {"id": "cite_with_range_hyp", "key": ("sqrt x # 0", "(0, 1)"),
     "cert": _cite("sqrt_pos", {"a": "x"}, [("x > 0", _RANGE_LO)]),
     "tag": T_SQRT_POS},
]

# ---------------------------------------------------------------------------
# 11d. Planted bugs and mutations after discharge
#
# The existing PLANTED_BUGS and DEFINEDNESS_MUTATIONS, re-traced by hand
# under DISCHARGE_RULE. 'admissions' is N per proof, omitted for a proof
# the mutation refuses; 'caught_by' replaces the pre-discharge list where
# given. A refused installation is (proof, "goal", "refused").
_D3 = {"P1.1": 3, "P1.1-fallback": 3, "P1.2": 3, "P1.2-alt": 3}
DISCHARGE_PLANTED_BUGS = {
    # the missing keys were discharged anyway: N does not move, the step
    # lists catch it as before
    "d_ln_emits_nothing": {"admissions": dict(_D3), "caught_by": "unchanged"},
    # the fallback's d_sqrt x > 0 moves to [0, pi^2/4], false at x = 0:
    # F3 refuses s1 (0 <= pi^2/4 decided by sign). With sqrt_zero (E35
    # (3)) field's 2*sqrt x # 0 on [0, pi^2/4] is refutable too (2*0 # 0),
    # but ftc emits deriv's side conditions before the check's divisors
    # (ARCHITECTURE.md §4), so x > 0 is the one named. P1.2's moved keys
    # are true on [0, 1] and discharged.
    "ftc_derivative_premise_on_closed": {
        "admissions": {"P1.1": 3, "P1.2": 3, "P1.2-alt": 3},
        "refused": {"P1.1-fallback": ("s1", _point("x > 0 @ [0, pi^2/4]",
                                                   "0 > 0", x="0"))},
        "caught_by": [
            ("P1.1", "s2", "D[t](2*sin t - 2*t*cos t) == sin t * (2*t)",
             "(0, pi/2)"),
            ("P1.1-fallback", "s1", "refused"),
            ("P1.2", "s2", "D[x](" + P1_2_F + ") == 1/(1 + x^3)", "(0, 1)"),
            ("P1.2-alt", "s2", "D[x](" + P1_2_F + ") == 1/(1 + x^3)",
             "(0, 1)")]},
    # Both drop_keys are discharged, so N no longer moves. The switch
    # replaces them by a key that stays admitted in each proof family, each
    # emitted once (s2, new, never re-emitted), so N still catches it.
    "tracker_drops_one": {
        "drop_keys": (
            ("sin t * (2*t) in C^0([0, pi/2])", "[0, pi/2]"),
            ("1/(1 + x^3) in C^0([0, 1])", "[0, 1]"),
            ("t >= 0", "[0, pi/2]"),
            ("1 + x^3 # 0", "[0, 1]"),
        ),
        "admissions": {"P1.1": 2, "P1.1-fallback": 3, "P1.2": 2,
                       "P1.2-alt": 2},
        "caught_by": [
            ("FINAL_TRACKER", "P1.1", ("t >= 0", "[0, pi/2]")),
            ("FINAL_TRACKER", "P1.1",
             ("sin t * (2*t) in C^0([0, pi/2])", "[0, pi/2]")),
            ("FINAL_TRACKER", "P1.2", ("1 + x^3 # 0", "[0, 1]")),
            ("FINAL_TRACKER", "P1.2", ("1/(1 + x^3) in C^0([0, 1])",
                                       "[0, 1]")),
            ("FINAL_TRACKER", "P1.2-alt", ("1 + x^3 # 0", "[0, 1]")),
            ("FINAL_TRACKER", "P1.2-alt", ("1/(1 + x^3) in C^0([0, 1])",
                                           "[0, 1]")),
            ("N", "P1.1"), ("N", "P1.2"), ("N", "P1.2-alt")]},
    "tracker_drops_reemitted": {"admissions": dict(_D3),
                                "caught_by": "unchanged"},
    # The seam is the untrusted search's sign facts; the trusted checker
    # reads entries.ENTRIES and is untouched. Without pi_pos the search has
    # no certificate for 0 <= pi/2 or pi/2 >= 0, and none for their
    # negations (so no F2): both stay ADMITTED, tagged none, REASON_NONE.
    # A search bug costs admissions, never a false discharge (E28).
    "pi_pos_not_in_constraint_set": {
        "admissions": {"P1.1": 4, "P1.1-fallback": 4, "P1.2": 3,
                       "P1.2-alt": 3},
        "retagged": {"P1.1": [("0 <= pi/2", "true", ADMITTED, T_NONE)],
                     "P1.1-fallback": [("pi/2 >= 0", "true", ADMITTED,
                                        T_NONE)]},
        "caught_by": [("P1.1", "goal", "0 <= pi/2", "tag"),
                      ("P1.1", "s1", "0 <= pi/2", "tag"),
                      ("P1.1", "s2", "0 <= pi/2", "tag"),
                      ("P1.1-fallback", "s2", "pi/2 >= 0", "tag"),
                      ("P1.1", "goal", "0 <= pi/2", "status"),
                      ("P1.1-fallback", "s2", "pi/2 >= 0", "status"),
                      ("N", "P1.1"), ("N", "P1.1-fallback")]},
}

# New planted bugs for the build to add, one per rule of the trusted
# checker whose loss could produce a false 'Proved', and one in the search.
# The seams are the architecture's to name (ARCHITECTURE.md §7); the
# data fixes only the mutation and what must catch it.
DISCHARGE_NEW_PLANTED_BUGS = {
    "farkas_ignores_strictness": {
        "mutation": "the Farkas check accepts k = 0 whatever the strictness",
        "caught_by": [("DISCHARGE_MUST_REJECT", "farkas_nonstrict_pair"),
                      ("PROPERTY", "farkas")]},
    "farkas_allows_negative_multiplier": {
        "mutation": "the Farkas check does not test the multipliers' sign",
        "caught_by": [("DISCHARGE_MUST_REJECT", "farkas_negative_multiplier"),
                      ("PROPERTY", "farkas")]},
    "farkas_swaps_interval_ends": {
        "mutation": "('dom', i, 'lo') is built from the interval's hi end "
                    "and ('dom', i, 'hi') from its lo end",
        # a range certificate using a lower end is then rejected where the
        # upper end is not a rational constant (P1.1's pi/2, the fallback's
        # pi^2/4). P1.2's [0, 1] is not caught: the swapped x - 1 >= 0 is a
        # stronger constraint, and -(1 + x) + (x - 1) = -2 still refutes the
        # negated goal (DATA_CHANGES, adjudicated)
        "caught_by": [("DISCHARGE_MUST_REJECT",
                       "farkas_constant_not_contradiction"),
                      ("N", "P1.1"), ("N", "P1.1-fallback"),
                      ("PROPERTY", "farkas")]},
    "farkas_closed_as_open": {
        "mutation": "a closed interval end is read as strict",
        "caught_by": [("DISCHARGE_MUST_REJECT", "farkas_nonstrict_pair"),
                      ("DISCHARGE_MUST_REJECT", "product_child_at_closed_end"),
                      ("PROPERTY", "farkas")]},
    "farkas_any_fact": {
        "mutation": "a ('fact', name) label is accepted for any ENTRIES name",
        # was farkas_non_fact_entry, which cannot isolate this mutation: its
        # combination, -pi/2 + (1/2)*sqrt a, is no constant, so it is rejected
        # whether or not the fact rule holds (DATA_CHANGES, adjudicated)
        "caught_by": [("DISCHARGE_MUST_REJECT", "farkas_schema_entry_as_fact")]},
    "farkas_no_goal_needed": {
        "mutation": "the ('goal',) multiplier may be absent",
        "caught_by": [("DISCHARGE_MUST_REJECT", "farkas_goal_unused")]},
    "sign_skips_ring": {
        "mutation": "the sign check does not run ring_equal",
        "caught_by": [("DISCHARGE_MUST_REJECT", "sign_false_quadratic_forged"),
                      ("DISCHARGE_MUST_REJECT", "sign_forged_square"),
                      ("PROPERTY", "sign")]},
    "sign_zero_constant_strict": {
        "mutation": "c0 = 0 is accepted on a strict target",
        "caught_by": [("DISCHARGE_MUST_REJECT", "sign_zero_constant_strict"),
                      ("PROPERTY", "sign")]},
    "sign_any_exponent": {
        "mutation": "odd exponents and non-positive coefficients are "
                    "accepted",
        "caught_by": [("DISCHARGE_MUST_REJECT", "sign_odd_power"),
                      ("DISCHARGE_MUST_REJECT", "sign_negative_coefficient"),
                      ("PROPERTY", "sign")]},
    "product_skips_parity": {
        "mutation": "the sign product ignores '<' factors",
        "caught_by": [("DISCHARGE_MUST_REJECT", "product_parity"),
                      ("PROPERTY", "sign product")]},
    "product_skips_children": {
        "mutation": "the sign product does not check its factors' "
                    "certificates",
        "caught_by": [("DISCHARGE_MUST_REJECT", "product_child_at_closed_end"),
                      ("PROPERTY", "sign product")]},
    "cite_skips_hypotheses": {
        "mutation": "a cite's hypotheses are not checked",
        "caught_by": [("DISCHARGE_MUST_REJECT", "cite_hypothesis_unproved"),
                      ("DISCHARGE_MUST_REJECT", "cite_hypothesis_missing")]},
    "search_scales_wrongly": {
        "mutation": "the untrusted search halves every Farkas multiplier of "
                    "a fact label",
        # 0 <= pi/2 and pi/2 >= 0 then sum to -pi/4: rejected, admitted
        # with REASON_REJECTED, tag unchanged; nothing is refuted
        "admissions": {"P1.1": 4, "P1.1-fallback": 4, "P1.2": 3,
                       "P1.2-alt": 3},
        "caught_by": [("P1.1", "goal", "0 <= pi/2", "status"),
                      ("P1.1-fallback", "s2", "pi/2 >= 0", "status"),
                      ("N", "P1.1"), ("N", "P1.1-fallback")]},
}

# DEFINEDNESS_MUTATIONS after discharge. Every mutation's admissions become
# _D3 (every obligation it removes or weakens in P1 was, or stays,
# discharged), except where given. caught_by: the pre-discharge list with
# the entries in 'drop' removed and those in 'add' added. Every other
# location still catches it, re-traced: a removed former's install-time
# refusal becomes an install, a removed key is missing from a list, and a
# case expected refused (DISCHARGE_DEFINEDNESS_CASES) now installs.
DISCHARGE_MUTATION_CHANGES = {
    # ln's removed keys were discharged, so N no longer moves
    "no_ln_former": {"drop": [("N", "P1.2"), ("N", "P1.2-alt")]},
    "no_sqrt_former": {"drop": [("N", "P1.1"), ("N", "P1.1-fallback")]},
    # Under ln u owes u >= 0, ln_false_on_goal_domain is refused either
    # way, by F3 at x = -1; only the message's key differs (x >= 0 @ x < 0),
    # so the suite must assert the message, not only the code.
    "ln_closed_at_0": {"note": "caught at ln_false_on_goal_domain by its "
                               "message"},
    # u > 0 for sqrt: t^2 > 0 @ [0, pi/2] and x > 0 @ [0, pi^2/4] are false
    # at 0, and F3 refuses both installations; P1.2's sqrt 3 owes 3 > 0,
    # literal, so P1.2 still completes with its 3 >= 0 keys changed
    "sqrt_open_at_0": {
        "admissions": {"P1.2": 3, "P1.2-alt": 3},
        "drop": [("P1.1", "goal", "t^2 >= 0", "[0, pi/2]"),
                 ("P1.1-fallback", "s1", "refused")],
        "add": [("P1.1", "goal", "refused"),
                ("P1.1-fallback", "goal", "refused")]},
    # charged at the goal's domain, R's x > 0 @ true is refuted by F3 at
    # x = 0 and the rewrite is refused; the cases still fail
    "rewrite_R_former_at_goal_domain": {"note": "caught_by unchanged: the "
                                                "MATCH_ACCEPTS rewrites are "
                                                "now refused (F3)"},
    "rewrite_R_former_on_ranges_only": {"note": "caught_by unchanged: "
                                                "x + y > 0 @ x in [1, 2] is "
                                                "refused at x = 1, y = -1"},
}

# ---------------------------------------------------------------------------
# 11e. The soundness property test (E34), for kernel/test_discharge.py

DISCHARGE_PROPERTY_TEST = (
    "The property. For each trusted checker (farkas, hyp, sign, sign "
    "product, cite, the norm_num leaf, and the dispatcher that applies the "
    "exact values first): whenever it accepts a (key, certificate) pair, "
    "the key's proposition holds at every sampled rational point of the "
    "key's domain at which the proposition's terms are defined, by exact "
    "evaluation. For each refutation (F1-F3): the refuted proposition is "
    "false at the named point (F3) or false outright (F1, F2), by an "
    "evaluation independent of the kernel's.",

    "Exact evaluation. fractions.Fraction throughout, the evaluator the "
    "test's own (never field.rational_value or the kernel's rewriting), so "
    "that a shared bug cannot hide. Variables take rational values. An atom "
    "the checker treats as opaque is evaluated honestly where exact "
    "evaluation exists (sqrt of a rational perfect square, the exact "
    "values' own points) and the point is otherwise skipped, except as "
    "follows. pi and e_const are replaced by random rationals with pi > 0 "
    "and e_const > 1: the Farkas, sign and product checkers know nothing "
    "of either constant beyond pi_pos and e_gt_one, so an accept must hold "
    "for every such value, the real ones among them (§5.3's argument for "
    "treating them as free). For the sign checker alone, every atom may "
    "also be given an independent random rational: its accept is a "
    "polynomial identity over atoms, so it must hold for any assignment.",

    "Undefined points. A point where a divisor evaluates to 0, a sqrt, ln, "
    "asin, acos, acosh or atanh argument is outside its natural domain "
    "(E26's table), or an atom cannot be evaluated exactly, is skipped, "
    "and skips are counted. Each run must report, per checker, at least 50 "
    "accepted certificates and 1000 evaluated (non-skipped) points; fewer "
    "fails the test, so it cannot pass vacuously.",

    "Generation. Keys: polynomials of degree <= 3 in one or two variables "
    "(x, y) with small rational coefficients, over domains made of one "
    "Interval (rational ends, each end open or closed at random, one end "
    "infinite with probability 1/8) and zero to two Γ relations v REL c; "
    "one key in eight mentions pi or e_const in a coefficient or an end. "
    "Certificates: (a) the search's own, (b) the search's with one field "
    "mutated at random (a multiplier's sign or value, a label's end or "
    "index, a square's term, coefficient or exponent, c0, a factor, a "
    "child, the sense), and (c) random well-formed certificates. Sampled "
    "points: the domain's closed ends with probability 1/4 each (open/closed "
    "errors live there), else uniform rationals inside it with "
    "denominators up to 12.",

    "Refutations. Every F3 refusal's point is checked in the domain and "
    "the proposition false there with the test's evaluator; every F1 or F2 "
    "refusal of a closed key is checked false with a math-module float "
    "evaluation at 1e-9 margin as a second, independent reading (the "
    "values involved are pi, e and literals).",

    "Reproducibility and failure. A fixed seed, printed; stdlib only "
    "(fractions, random, math), no SymPy (§15.5 keeps it out of kernel/). "
    "A failure prints the key, the certificate and the point. The test "
    "must fail under each of DISCHARGE_NEW_PLANTED_BUGS' checker mutations "
    "whose caught_by names PROPERTY, run through the same child-process "
    "seam mechanism as PLANTED_BUGS (ARCHITECTURE.md §7).",
)

# ---------------------------------------------------------------------------
# 11f. How the suite switches (E34)

DISCHARGE_SWITCH = (
    "Two commits, the suite green after each. (1) The trusted checker "
    "module and the untrusted search; DISCHARGE_NEW_ENTRIES pinned in "
    "entries.py at the positions it states (sqrt_zero immediately before "
    "sqrt_sq, cos_zero last), with DISCHARGE_E27_CHANGES applied to the asserted E27 "
    "cases in the same commit (E27 reads ENTRIES, so the two cannot land "
    "apart without a red suite; any suite count of ENTRIES goes from 14 to "
    "16); and kernel/test_discharge.py: "
    "DISCHARGE_MUST_REJECT, DISCHARGE_CHECKER_ACCEPTS and every certificate "
    "in DISCHARGE_EXPECTED, DISCHARGE_MATCH_ACCEPTS, DISCHARGE_OCCURRENCE_"
    "CASE, DISCHARGE_DEFINEDNESS_CASES, DISCHARGE_BAD_MOVES_ADDED and "
    "problems/stage0's DISCHARGE_EXPECTED, each handed to the checker "
    "directly; the search's own certificate for each of those keys, "
    "compared as DISCHARGE_RULE says; and DISCHARGE_PROPERTY_TEST. Nothing "
    "is wired into kernel._emit, so items 1-7 still assert the "
    "pre-discharge tables.",

    "(2) Wiring into kernel._emit, and in the same commit the suite "
    "asserts, for both data files: DISCHARGE_OBLIGATIONS in place of "
    "EXPECTED_OBLIGATIONS, DISCHARGE_FINAL_TRACKER for FINAL_TRACKER, "
    "DISCHARGE_ADMISSIONS and DISCHARGE_VERDICTS for ADMISSIONS and "
    "VERDICTS; each obligation's reason (REASON_REG for every remaining "
    "admission) and certificate (DISCHARGE_EXPECTED); the case changes "
    "(DISCHARGE_MATCH_ACCEPTS, DISCHARGE_OCCURRENCE_CASE, DISCHARGE_"
    "DEFINEDNESS_CASES, DISCHARGE_BAD_MOVES_CHANGED, DISCHARGE_BAD_MOVES_"
    "ADDED, DISCHARGE_UNDECIDED), every 'obligation-decided-false' refusal "
    "by its code and by its message filled from DECIDED_FALSE_MESSAGES; "
    "the planted bugs and mutations as DISCHARGE_PLANTED_BUGS, DISCHARGE_"
    "NEW_PLANTED_BUGS and DISCHARGE_MUTATION_CHANGES give them; "
    "REFUSAL_CODES_DISCHARGE in the refusal-code coverage check; and that "
    "EXACT_VALUE_ENTRIES is exactly the ENTRIES equations with no schema "
    "variable and no hypothesis. The no-none assertion over PROOFS runs and "
    "every E24 tag assertion stay as they are.",

    "The switch is one constant in proof_of_life.py, never in a kernel "
    "file, and no kernel file imports either data file (as now). The "
    "pre-discharge tables stay in both files as the stub phase's record and "
    "are no longer asserted; retiring them later is a DATA_CHANGES entry, "
    "not a silent deletion. ADMISSION_REASON ('discharge not built') is "
    "then no longer produced by the kernel.",
)

# ---------------------------------------------------------------------------
# 11g. The owner's answers (E35, discharge spec 2026-09-24, owner answers):
#      two §6.8 entries pinned now, and what they change in E27's cases

# E35 (3). Pinned for entries.py in NAMED_ENTRIES' shape, as problems/
# stage0's NEW_ENTRIES was for its four. Insertion positions in ENTRIES
# (discharge spec 2026-09-24, owner answers; the main session's choice for
# sqrt_zero): sqrt_zero IMMEDIATELY BEFORE sqrt_sq, so it becomes the
# first entry and E27 (a) names the direct move at sqrt 0; cos_zero
# appended at the end, after exp_one. cos_zero's position is immaterial:
# at cos b only it and cos_pi_half can count, never both at one subterm
# (their arguments normalise to 0 and to pi/2). Neither has a schema variable or a hypothesis,
# so a rewrite by either owes nothing (E1 steps 8 and 10: R is a literal),
# and each is an exact value (E31). Before them the fallback closed sqrt 0
# by sqrt_sq with u := 0 and ring removed 2*0*cos 0 (NAMED_ENTRIES' note);
# those routes still work, and no reference proof changes.
DISCHARGE_NEW_ENTRIES = {
    "cos_zero": {
        "statement": "cos 0 == 1",
        "schema": (),
        "lhs": "cos 0",
        "rhs": "1",
        "hyps": (),
        "use": "rewrite; exact value (E31)",
        "cite": "§6.8 table row 'cos 0' (the owner's decision, E35 (3))",
        "used_in": ("DISCHARGE_DEFINEDNESS_CASES tan_zero_true (cos 0 # 0 "
                    "reads 1 # 0)",
                    "DISCHARGE_E27_CHANGES (cos 0 refused in an answer)"),
    },
    "sqrt_zero": {
        "statement": "sqrt 0 == 0",
        "schema": (),
        "lhs": "sqrt 0",
        "rhs": "0",
        "hyps": (),
        "use": "rewrite; exact value (E31)",
        "cite": "§6.8 table row 'sqrt 0' (the owner's decision, E35 (3))",
        "used_in": ("DISCHARGE_BAD_MOVES_ADDED decided_false_sqrt_at_end "
                    "(sqrt x # 0 @ [0, 1] at x = 0 reads 0 # 0)",
                    "DISCHARGE_E27_CHANGES e27_sqrt_zero"),
    },
}

# What pinning the two entries changes in the E27 cases the suite asserts,
# applied in DISCHARGE_SWITCH's first commit, together with the entries.
# Traced against every reference proof, every accepted value and every
# e27 case: cos 0 and sqrt 0 occur in P1.1's and the fallback's goals
# (never in a closing value: both close with 2), in e27_goal_lhs_after_ftc
# and e27_goal_lhs_before_close's values, in sqrt_closed_end's goal (closed
# with 0) and in the limitation row below. Only the two entries marked
# change; e27_goal_lhs_after_ftc keeps sin(pi/2), which comes first in
# pre-order. No reference proof and no accepted answer is refused.
DISCHARGE_E27_CHANGES = {
    "EVALUATED_ACCEPTS_remove": ("e27_no_entry_in_force",),
    "BAD_MOVES_replace": {
        "e27_goal_lhs_before_close": {
            "e27": {"clause": "a", "at": "cos 0", "entry": "cos_zero",
                    "message": "cos 0 can still be evaluated (cos_zero)"},
            "why": "with cos_zero in force, (a) finds cos 0, the only "
                   "application left in the value, before (b)'s root "
                   "offence (2*(pi/2)*0 a zero summand), which it used to "
                   "name. The refusal code is unchanged",
        },
    },
    "BAD_MOVES_add": [
        {"id": "e27_cos_zero", "added": True,
         "goal": "cos 0 == ?A", "setup": [],
         "move": ("close", {"value": "cos 0", "check": "ring",
                            "facts": []}),
         "refusal": "close-not-evaluated",
         "e27": {"clause": "a", "at": "cos 0", "entry": "cos_zero",
                 "message": "cos 0 can still be evaluated (cos_zero)"},
         "evaluated": "1",
         "why": "refl passes (ring), cos is total so nothing is owed, and "
                "(a1) counts cos_zero at cos 0. It was the limitation "
                "e27_no_entry_in_force, accepted while no cos_zero was in "
                "force"},
        {"id": "e27_sqrt_zero", "added": True,
         "goal": "sqrt 0 == ?A", "setup": [],
         "move": ("close", {"value": "sqrt 0", "check": "ring",
                            "facts": []}),
         "refusal": "close-not-evaluated",
         "e27": {"clause": "a", "at": "sqrt 0", "entry": "sqrt_zero",
                 "message": "sqrt 0 can still be evaluated (sqrt_zero)"},
         "evaluated": "0",
         "why": "already refused before sqrt_zero, naming sqrt_sq ((a2) "
                "counts it at sqrt 0: 0 is 0*0, closed). Both count at "
                "sqrt 0 now, and sqrt_zero is named because it precedes "
                "sqrt_sq in ENTRIES (DISCHARGE_NEW_ENTRIES' insertion "
                "position): the direct move, owing nothing. The goal and "
                "the value owe sqrt 0's 0 >= 0, literal, discharged (E7)"},
    ],
}

# The hand re-check behind the ENTRIES positions (discharge spec 2026-09-24,
# owner answers). What reads ENTRIES in order, and what the new positions
# change:
DISCHARGE_ORDER_CHECK = (
    "E27 (a) is the only rule that reads ENTRIES in order (the first entry "
    "that counts at a subterm is named; subterms in pre-order). A new "
    "position changes a named entry only at a subterm where two entries "
    "count. sqrt_zero and sqrt_sq both count exactly at sqrt b with "
    "ring_nf(b) = 0: sqrt 0, and any sqrt of an argument normalising to 0 "
    "(sqrt(0^2), sqrt(x - x)). The only such case is e27_sqrt_zero, whose "
    "message becomes 'sqrt 0 can still be evaluated (sqrt_zero)'. No other "
    "e27 case, EVALUATED_ACCEPTS value or reference proof holds such a "
    "sqrt (the e27 sqrt cases are sqrt 4, sqrt(pi^2/4) and powers of "
    "sqrt 2 and sqrt 3; the fallback's sqrt 0 is a rewrite target, not a "
    "closing value). cos_zero shares no subterm with another counting "
    "entry. Everything else is order-free: E31 rewrites every occurrence "
    "to a fixed point and each exact value's left side is a distinct "
    "application with a distinct argument normal form, so the result, and "
    "the set of entries used, do not depend on the order (the cites list "
    "them in first-use order, and no obligation here uses two); rewrite "
    "names its entry; TAG_RULES' cite looks for an ordering conclusion, "
    "which neither new entry has; and the suite reads ENTRIES as a set "
    "(proof_of_life.py's entries checks), so moving sqrt_sq from first to "
    "second position changes no assertion. No other expectation changes.",
)


# ---------------------------------------------------------------------------
# 12. int_subst, specified before any code (int_subst spec 2026-09-24)
#
# WHAT.md "Start here" item 1: the move §6.4 states and §11.1 uses first,
# so that P1.1 starts from the sheet's own goal. DECISIONS E36-E44 give the
# design in brief with § references; INT_SUBST_RULE states it in full, one
# paragraph per point, as REWRITE_RULE and DISCHARGE_RULE do, so that every
# table below is a check of a stated rule and not fitted to an
# implementation. Written from DESIGN.md revision 10 (§5.1, §6.1, §6.4,
# §6.9, §8.1, §8.4-§8.6, §11.1, §15.2, §18 Q23), ARCHITECTURE.md, GRAMMAR.md
# and the data files, without reading kernel.py. Every string below was
# parsed with terms.py's parser and every piece of mathematics checked with
# SymPy in a scratch directory (VERIFIED, last entry).
#
# Discharge is wired, so only post-discharge expectations are written: no
# pre-discharge (stub) table exists for int_subst, and every admission's
# reason is DISCHARGE's REASON_REG. Nothing here is asserted until the build
# (INT_SUBST_SWITCH): the tables are kept out of PROOFS, REFUSAL_CODES,
# SOURCES and the DISCHARGE_* tables so the suite stays green (E44).

INT_SUBST_MOVE = "int_subst"
# The key sets (E36, E45, E48; owner answers 2026-09-24). 'mode' is
# optional and defaults to 'forward', so every forward case below is
# written without it; 'reverse' requires 'f', and 'f' in forward mode is
# bad-args. 'occurrence' is optional in both modes.
INT_SUBST_ARGS = ("var", "sub", "new_var", "lo", "hi", "check", "facts")
INT_SUBST_ARGS_REVERSE = INT_SUBST_ARGS + ("mode", "f")
INT_SUBST_OPTIONAL = ("mode", "occurrence")
INT_SUBST_MODES = ("forward", "reverse")

# New refusal codes, merged into the coverage check at the build, as
# REFUSAL_CODES_DISCHARGE was. Only the mismatch and check-failed carry a
# residual. A substitution under D[y] reuses rewrite's
# 'rewrite-under-D-needs-open-domain' (E48).
REFUSAL_CODES_INT_SUBST = {
    "int-subst-no-integral": "E36, E48: the goal holds no Int, or none at "
                             "the given occurrence (ftc-no-integral's "
                             "twin)",
    "int-subst-wrong-variable": "E36, E48: the selected Int does not bind "
                                "var, or with no occurrence no Int does "
                                "while some Int exists",
    "int-subst-ambiguous": "E48 (owner answers): no occurrence is given "
                           "and two or more Ints bind var",
    "int-subst-infinite-endpoint": "E36, §5.1: a limit of the selected "
                                   "integral is oo or -oo; sub(lo) == oo "
                                   "is not a term, and the improper case is "
                                   "int_improper's (ftc-infinite-endpoint's "
                                   "twin)",
    "int-subst-not-fresh": "E42, D11: new_var occurs in the current goal, "
                           "free or bound (var itself included)",
    "int-subst-scope": "E42, E48, GRAMMAR.md §5: a variable of sub, f, lo "
                       "or hi is not in scope at the position (new_var in "
                       "a limit included)",
    "int-subst-orientation-undecided": "E46 (owner answers): the new "
                                       "limits are not two literals, and "
                                       "discharge proves neither lo <= hi "
                                       "nor hi <= lo",
    "int-subst-endpoint-mismatch": "E39: an endpoint equation, after "
                                   "§6.8's exact values, fails by `check`. "
                                   "Carries the residual image - limit",
    "int-subst-check-failed": "E45 (owner answers), reverse mode: the "
                              "integrand is not f(g(x))*g'(x) by `check`. "
                              "Carries the residual body - f(g(x))*g'(x) "
                              "(ftc-check-failed's twin)",
}

# Their messages, asserted by filling the template with terms.show of the
# named parts, never as a literal printout (E27_MESSAGES' convention).
# {part} is 'the substitution', 'the new integrand', 'the lower limit' or
# 'the upper limit'; {name} the first out-of-scope variable in sorted order;
# {end} 'lower' or 'upper'; {image} the endpoint image as emitted, BEFORE
# the exact values; {limit} the limit it is owed equal to; {n} a numeral.
# 'int-subst-no-integral' has two templates, the second when an occurrence
# was given.
INT_SUBST_MESSAGES = {
    "int-subst-no-integral": "the goal holds no integral",
    "int-subst-no-integral/occurrence": "the goal holds no integral at "
                                        "occurrence {occurrence}",
    "int-subst-wrong-variable": "the integral is over {bound}, not {var}",
    "int-subst-wrong-variable/none": "no integral in the goal is over {var}",
    "int-subst-ambiguous": "{n} integrals are over {var}; give an "
                           "occurrence",
    "int-subst-infinite-endpoint": "int_subst needs finite limits, and "
                                   "{limit} is not (int_improper is the "
                                   "route)",
    "int-subst-not-fresh": "{new_var} already occurs in the goal; choose a "
                           "fresh variable",
    "int-subst-scope": "{part} {term} mentions {name}, which is not in "
                       "scope",
    "int-subst-orientation-undecided": "the order of {lo} and {hi} is not "
                                       "decided; state it in the goal's "
                                       "domain",
    "int-subst-endpoint-mismatch": "{image} == {limit} fails at the {end} "
                                   "limit",
    "int-subst-check-failed": "the integrand is not f(g(x))*g'(x) for "
                              "f := {f}",
}

# New sources, merged into SOURCES at the build.
S_SUBST_LO, S_SUBST_HI = "int_subst_lo", "int_subst_hi"
S_SUBST_C1, S_SUBST_C0 = "int_subst_phi_C1", "int_subst_f_C0"
S_SUBST_INT = "int_subst_integrand"
SOURCES_INT_SUBST = {
    S_SUBST_LO: "int_subst's lower endpoint equation (forward sub(lo) == a, "
                "reverse sub(a) == lo), decided in-step (§6.4, E39)",
    S_SUBST_HI: "int_subst's upper endpoint equation, likewise (§6.4, E39)",
    S_SUBST_C1: "int_subst premise: the substitution's map in C^1 on its "
                "closed range, phi on the new one (forward) or g on the old "
                "one (reverse) (§6.4, E38, E45)",
    S_SUBST_C0: "int_subst premise: the composed integrand f(phi(t)) or "
                "f(g(x)) in C^0 on that range (§6.4, §11.1's correction, "
                "E38, E45)",
    S_SUBST_INT: "int_subst reverse mode: body == f(g(x))*g'(x) on the old "
                 "range, decided in-step (E45)",
}
# The in-step checks' tags, merged into DISCHARGE_METHODS at the build: a
# discharged endpoint equation is tagged with its check and the entries it
# used (E39); reverse mode's integrand identity 'deriv+' + check, as ftc's
# premise is (E9, E45).
DISCHARGE_METHODS_INT_SUBST = {
    "ring": "§6.2 ring, run inside the int_subst step on an endpoint "
            "equation after §6.8's exact values (E39)",
    "field": "§6.2 field with the step's facts, likewise (E39)",
}
T_RING = ("ring", ())
T_RING_LN_ONE = ("ring", ("ln_one",))
T_RING_LN_E = ("ring", ("ln_e",))
T_RING_COS_PI_HALF = ("ring", ("cos_pi_half",))
T_RING_COS_ZERO = ("ring", ("cos_zero",))
# E49: the linear method citing the sqrt atoms' sign fact
T_LINEAR_SQRT = ("linear", ("sqrt_nonneg",))


def SQRT(u):
    """E49's Farkas label for the sign fact of the atom sqrt u."""
    return ("fact", "sqrt_nonneg", u)


INT_SUBST_RULE = (
    "The rule (§6.4), two modes and one flip. Forward: phi in C^1([c, d]) "
    "and f(phi(t)) in C^0([c, d]) give Int[x = phi(c) .. phi(d)] f == "
    "Int[t = c .. d] f(phi(t))*phi'(t). Reverse (E45): g in C^1([a, b]), "
    "f(g(x)) in C^0([a, b]) and h == f(g(x))*g'(x) on [a, b] give "
    "Int[x = a .. b] h == Int[u = g(a) .. g(b)] f. Flip (E46, §5.1): "
    "Int[t = c .. d] k == Int[t = d .. c] -k. The move reads each left to "
    "right at one integral of the goal, selected by position (E48), and "
    "replaces it there, leaving the rest of the goal, the rhs ?A included, "
    "unchanged. In what follows the selected integral is "
    "Int[var = a .. b] body, P is its position domain, and body' is the new "
    "integrand before any flip: F*phi' (forward, F := body[var := sub]) or "
    "f (reverse).",

    "1. The common step() checks (ARCHITECTURE.md §4): the state is "
    "minted, the goal is open, the move is one of the five (rewrite, fact, "
    "ftc, close, int_subst), and args has exactly the mode's keys "
    "(INT_SUBST_ARGS for forward, with 'mode' optional; "
    "INT_SUBST_ARGS_REVERSE for reverse), plus 'occurrence' optionally, "
    "each of the right type, else 'bad-args': mode is 'forward' or "
    "'reverse'; var and new_var are str, each naming a variable "
    "(parse_term gives a Var, so pi, e_const, sin and e are refused); sub, "
    "lo, hi and f are Terms holding no MVar and no oo (close's rule for "
    "its value); occurrence is an int >= 0, not a bool; check is 'ring' "
    "or 'field'; facts is a list, and 'ring' with a fact is bad-args "
    "(ftc's rule). Any other key, a phi' among them, is bad-args (E41), "
    "and so is 'f' in forward mode. Fact slots are resolved next (E17).",

    "2. Selection (E48). The Integral nodes of the goal's non-?A side "
    "(both sides, lhs first, when there is no ?A) are enumerated in "
    "REWRITE_RULE's pre-order. With occurrence k: the k-th, else "
    "'int-subst-no-integral' ('/occurrence' template); its binder must be "
    "var, else 'int-subst-wrong-variable'. With none: the Ints binding "
    "var; exactly one is selected; none refuses 'int-subst-wrong-variable' "
    "('/none' template) if the side holds any Int, else "
    "'int-subst-no-integral'; two or more refuse 'int-subst-ambiguous'. P "
    "is the goal's domain G plus the E4 range of each Int whose body holds "
    "the selected one, outermost first (REWRITE_RULE step 7).",

    "3. Neither of the selected integral's limits a, b may be infinite, "
    "else 'int-subst-infinite-endpoint' (E36; as E9 for ftc).",

    "4. Freshness (E42): new_var occurs nowhere in the current goal (fv or "
    "bv of either side, or of the domain), else 'int-subst-not-fresh'. "
    "Since var is bound in the goal, new_var == var is refused here.",

    "5. Scope (E42, E48), with S the names in scope at the position (fv "
    "of the goal and the binders of the enclosing Ints): forward, fv(sub) "
    "within S + {new_var}; reverse, fv(sub) within S + {var}, then fv(f) "
    "within S + {new_var}; both, fv(lo) and fv(hi) within S. Checked in "
    "that order, else 'int-subst-scope' naming the part and the first "
    "offending name.",

    "6. Under D[y] (E48, REWRITE_RULE step 9): if the selected Int lies "
    "below a D[y] and y occurs free in its limits or body, in sub, f, lo "
    "or hi, or in a limit of an Int between the D[y] and the position, "
    "the step is refused 'rewrite-under-D-needs-open-domain'.",

    "7. Syntax, before anything is emitted, each by terms.subst (trusted, "
    "capture-avoiding; its refusals 'subst-under-D' (D10) and "
    "'rpow-literal-exponent' (D17) come here). Forward: F := body[var := "
    "sub], and the images sub[new_var := lo] and sub[new_var := hi]. "
    "Reverse: Fg := f[new_var := sub], and the images sub[var := a] and "
    "sub[var := b].",

    "8. Ranges and the new orientation. Reverse only, first: I := E4's "
    "range of (var, a, b), owing a <= b at P (orient) when the ends are "
    "not two literals, since the premises use I (a false one refuses by "
    "F2, as for ftc). Both: lo's and hi's formers at P (E6, E26; they lie "
    "outside the new Int's scope). Then E46 on (lo, hi): two rational "
    "literals are ordered by norm_num, nothing is owed, the limits are "
    "kept and I' = [min, max]; otherwise lo <= hi at P is put to "
    "DISCHARGE_RULE steps (3)-(5), and if discharged it is emitted "
    "(orient), the limits are kept and I' = [lo, hi]; otherwise hi <= lo "
    "at P likewise, and if discharged it is emitted (orient), the new "
    "integral will be flipped and I' = [hi, lo]; otherwise the step is "
    "refused 'int-subst-orientation-undecided'. A candidate that is not "
    "discharged is never emitted, so it is never refuted. D denotes P+I' "
    "in forward mode and P+I in reverse: the premises' domain.",

    "9. The substitution's formers at D, source former: forward, sub's; "
    "reverse, sub's and then Fg's, which is f's definedness on the image "
    "stated over the old range (E45). phi (or g) must be defined on the "
    "whole closed range, both ends included, which is also what makes the "
    "endpoint images defined (E39).",

    "10. The derivative on the closed range (E38): forward phi' := "
    "deriv(sub, new_var, D), reverse g' := deriv(sub, var, D). Its trace "
    "and output are the step's `trace` and `output`, as ftc's are, and its "
    "side conditions are emitted at D. deriv's refusals ('deriv-no-rule', "
    "'Int-or-D-not-normalisable') refuse the step.",

    "11. Reverse only: the integrand check (E45). body == Mul(Fg, g') is "
    "decided at D by `check` (ring, or field with the facts, whose "
    "divisors (field_div), facts' hypotheses (fact_hyp) and facts' inst "
    "formers (former) are emitted at D). A failure refuses "
    "'int-subst-check-failed' with residual body - Fg*g' (E14). Success "
    "emits that equation with discharged_by ('deriv+' + check, the facts' "
    "entries), certificate None, source int_subst_integrand.",

    "12. Endpoint equations (E39), lower then upper, keyed at P (E5): "
    "forward sub[new_var := lo] == a and sub[new_var := hi] == b; reverse "
    "sub[var := a] == lo and sub[var := b] == hi. Each is rewritten with "
    "§6.8's exact values (E31's rewrite, trusted) and decided by `check`, "
    "whose divisors and facts' obligations are emitted at P. A failure "
    "refuses 'int-subst-endpoint-mismatch' with residual lhs - rhs of the "
    "rewritten equation. Success emits the equation as written, with "
    "discharged_by (check, the exact-value entries used then the facts' "
    "entries), certificate None, source int_subst_lo or int_subst_hi. "
    "Never admitted, never refuted (ARCHITECTURE.md §5 order step 1), and "
    "E7's Int-or-D refusal is not needed, the check's ring having refused "
    "any Int or D node (E26 (b)).",

    "13. Premises (E38, E45), ADMITTED ('reg', ()), REASON_REG: forward "
    "Reg(sub, 1, D) (int_subst_phi_C1) and Reg(F, 0, D) (int_subst_f_C0); "
    "reverse Reg(sub, 1, D) and Reg(Fg, 0, D).",

    "14. The new integral: Integral(new_var, lo, hi, body') when the limits "
    "were kept (reversed, if literal and reversed, E40), or "
    "Integral(new_var, hi, lo, Neg(body')) when flipped (E46). It replaces "
    "the selected Int at its position; nothing else in the goal changes. "
    "Its formers are charged as installation charges a term: its limits at "
    "P, its body at P plus its own E4 range, with the orientation whenever "
    "a key uses that range (already owed by step 8 when it is not literal, "
    "so it merges). This is where the composed integrand's formers "
    "(§11.1's t^2 >= 0) and phi''s own (the divisor of 1/(2*sqrt t)) are "
    "charged, and, in reverse mode, f's on the new range. Then check_goal "
    "on the new goal (D11 and shadowing: the backstop behind step 4).",

    "15. Emission order, for the step's `emitted` list (compared as a set, "
    "KEYING) and for which refusal comes first: steps 8, 9, 10, 11, 12 "
    "(lower, upper), 13, 14. Every emission goes through kernel._emit and "
    "DISCHARGE_RULE; a refused step emits nothing and changes nothing "
    "(E13). In forward mode the old range enters no key, so neither it nor "
    "its orientation is owed (E38).",

    "16. What int_subst never does: it does not compute the image of the "
    "substitution's map (§6.4's reason for the composed C^0 premise, and "
    "E45's for reverse mode), does not require it monotone (§6.4, 'Do not "
    "weaken it'), does not tidy phi' or g' (E41), flips only on a "
    "discharged order (E46), and does not touch the rhs, so ?A and E19's "
    "original goal are unchanged (E42).",

    "17. Soundness at a position (E48). The step proves Int_old == "
    "Int_new at P under every key it emits (at P, P+I or P+I'). Replacing "
    "an equal subterm at a position is REWRITE_RULE step 5's congruence "
    "(E16's cong) with domain P: under an enclosing Int the range domain "
    "is enough (§6.1), and under a D[y] step 6 enforces step 9.",
)

# --- P1.1 from the sheet's goal ---------------------------------------------
#
# The sheet's goal is the fallback's goal (§11 heading, §8.1). s1 is
# int_subst; s2-s7 are the existing P1.1 route (PROOFS['P1.1'] s1-s6) with
# the same args, on a goal whose integrand carries deriv's 2*t^1*1 where
# P1_1_GOAL has §11.1's 2*t (E41).
P1_1_SHEET_GOAL = P1_1_FALLBACK_GOAL
P1_1_SHEET_S1 = "Int[t = 0 .. pi/2] sin(sqrt(t^2))*(2*t^1*1) == ?A"
P1_1_SHEET_S2 = "Int[t = 0 .. pi/2] sin t * (2*t^1*1) == ?A"
_P11 = {s["id"]: s for s in PROOFS["P1.1"]["steps"]}

INT_SUBST_PROOFS = {
    "P1.1-sheet": {
        "fallback": False,
        "goal": P1_1_SHEET_GOAL,
        "steps": [
            {"id": "s1", "move": "int_subst",
             "args": {"var": "x", "sub": "t^2", "new_var": "t", "lo": "0",
                      "hi": "pi/2", "check": "ring", "facts": []},
             "goal_after": P1_1_SHEET_S1},
            {"id": "s2", "move": "rewrite", "args": _P11["s1"]["args"],
             "occurrences": 1, "goal_after": P1_1_SHEET_S2},
            {"id": "s3", "move": "ftc", "args": _P11["s2"]["args"],
             "goal_after": P1_1_AFTER_FTC},
            {"id": "s4", "move": "rewrite", "args": _P11["s3"]["args"],
             "occurrences": 1, "goal_after": _P11["s3"]["goal_after"]},
            {"id": "s5", "move": "rewrite", "args": _P11["s4"]["args"],
             "occurrences": 1, "goal_after": _P11["s4"]["goal_after"]},
            {"id": "s6", "move": "rewrite", "args": _P11["s5"]["args"],
             "occurrences": 1, "goal_after": _P11["s5"]["goal_after"]},
            {"id": "s7", "move": "close", "args": _P11["s6"]["args"],
             "goal_after": None},
        ],
        # the ORIGINAL goal instantiated (E19): the theorem WHAT.md's
        # 'P1.1 then starts from the sheet's own goal' asks for
        "theorem": "Int[x = 0 .. pi^2/4] sin(sqrt x) == 2",
    },
}
del _P11

# deriv inside int_subst (step 10) and inside ftc, in DERIV's shape. s1's
# domain is the closed [0, pi/2] (E38); t^2 owes nothing there. s3's F is
# P1.1's, so its trace and output are DERIV['P1.1']'s; only the integrand
# the check compares against differs, and ring equates them.
INT_SUBST_DERIV = {
    ("P1.1-sheet", "s1"): {
        "var": "t", "F": "t^2",
        "trace": [("d_pow_int", "t^2", ()), ("d_var", "t", ())],
        "output": "2*t^1*1",
        "emits": (),
    },
    ("P1.1-sheet", "s3"): DERIV["P1.1"],
}

# Per step, after discharge (6-tuples, OB_FIELDS; new read against the
# tracker before the step). Hand-derived:
#   goal: the fallback's installation exactly (sqrt x owes x >= 0 on the
#     range, range; the range's 0 <= pi^2/4 by sign, E20; pi^2/4's 4 # 0).
#   s1 (INT_SUBST_RULE): step 8, hi = pi/2 owes 2 # 0 (literal, norm_num);
#     I' = [0, pi/2] is not two literals, so 0 <= pi/2 (linear, pi_pos).
#     Step 9, t^2 has no former. Step 10, deriv emits nothing. Step 11,
#     0^2 == 0 and (pi/2)^2 == pi^2/4 by ring, no exact value used ((1/4)
#     pi^2 both sides). Step 12, the two Reg. Step 13, the new goal's
#     pi/2 (2 # 0 again, merged), and sqrt(t^2)'s t^2 >= 0 on [0, pi/2]
#     (sign, E20), which uses the range, so 0 <= pi/2 again (merged).
#     §11.1's five lines, plus 2 # 0, with §11.1's conjunction as two keys.
#   s2-s7: P1.1's s1-s6, with the integrand's 2*t^1*1 in ftc's two keys
#     that mention f.
INT_SUBST_OBLIGATIONS = {
    "P1.1-sheet": {
        "goal": [
            ("4 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
            ("x >= 0", "[0, pi^2/4]", (S_FORMER,), DISCHARGED, T_RANGE,
             True),
            ("0 <= pi^2/4", "true", (S_ORIENT,), DISCHARGED, T_SIGN, True),
        ],
        "s1": [
            ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
            ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI,
             True),
            ("0^2 == 0", "true", (S_SUBST_LO,), DISCHARGED, T_RING, True),
            ("(pi/2)^2 == pi^2/4", "true", (S_SUBST_HI,), DISCHARGED, T_RING,
             True),
            ("t^2 in C^1([0, pi/2])", "[0, pi/2]", (S_SUBST_C1,), ADMITTED,
             T_REG, True),
            ("sin(sqrt(t^2)) in C^0([0, pi/2])", "[0, pi/2]", (S_SUBST_C0,),
             ADMITTED, T_REG, True),
            ("t^2 >= 0", "[0, pi/2]", (S_FORMER,), DISCHARGED, T_SIGN, True),
        ],
        "s2": [
            ("t >= 0", "[0, pi/2]", (S_SQRT_SQ,), DISCHARGED, T_RANGE, True),
            ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI,
             False),
        ],
        "s3": [
            ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI,
             False),
            ("2*sin t - 2*t*cos t in C^0([0, pi/2])", "[0, pi/2]",
             (S_FTC_C0F,), ADMITTED, T_REG, True),
            ("2*sin t - 2*t*cos t in C^1((0, pi/2))", "(0, pi/2)",
             (S_FTC_C1F,), ADMITTED, T_REG, True),
            ("D[t](2*sin t - 2*t*cos t) == sin t * (2*t^1*1)", "(0, pi/2)",
             (S_FTC_D,), DISCHARGED, T_DERIV_RING, True),
            ("sin t * (2*t^1*1) in C^0([0, pi/2])", "[0, pi/2]",
             (S_FTC_C0f,), ADMITTED, T_REG, True),
            ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False),
        ],
        "s4": [],
        "s5": [],
        "s6": [],
        "s7": [],
    },
}

# Certificates of the keys a §5.3 method discharges (DISCHARGE_EXPECTED's
# shape and helpers). The two endpoint equations have none (in-step).
INT_SUBST_EXPECTED = {
    "P1.1-sheet": {
        ("x >= 0", "[0, pi^2/4]"): (T_RANGE, _RANGE_LO),
        ("0 <= pi^2/4", "true"): (T_SIGN, _PI_SQ),
        ("0 <= pi/2", "true"): (T_LINEAR_PI, _PI_HALF),
        ("t^2 >= 0", "[0, pi/2]"): (T_SIGN, _sos("0", [("1", "t", 2)])),
        ("t >= 0", "[0, pi/2]"): (T_RANGE, _RANGE_LO),
    },
}

# Written out by hand, in emission order (compared as a set).
INT_SUBST_FINAL_TRACKER = {
    "P1.1-sheet": [
        ("4 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("x >= 0", "[0, pi^2/4]", DISCHARGED, T_RANGE),
        ("0 <= pi^2/4", "true", DISCHARGED, T_SIGN),
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("0 <= pi/2", "true", DISCHARGED, T_LINEAR_PI),
        ("0^2 == 0", "true", DISCHARGED, T_RING),
        ("(pi/2)^2 == pi^2/4", "true", DISCHARGED, T_RING),
        ("t^2 in C^1([0, pi/2])", "[0, pi/2]", ADMITTED, T_REG),
        ("sin(sqrt(t^2)) in C^0([0, pi/2])", "[0, pi/2]", ADMITTED, T_REG),
        ("t^2 >= 0", "[0, pi/2]", DISCHARGED, T_SIGN),
        ("t >= 0", "[0, pi/2]", DISCHARGED, T_RANGE),
        ("2*sin t - 2*t*cos t in C^0([0, pi/2])", "[0, pi/2]", ADMITTED,
         T_REG),
        ("2*sin t - 2*t*cos t in C^1((0, pi/2))", "(0, pi/2)", ADMITTED,
         T_REG),
        ("D[t](2*sin t - 2*t*cos t) == sin t * (2*t^1*1)", "(0, pi/2)",
         DISCHARGED, T_DERIV_RING),
        ("sin t * (2*t^1*1) in C^0([0, pi/2])", "[0, pi/2]", ADMITTED,
         T_REG),
    ],
}

# N: the substitution's two regularity premises and ftc's three. §11.1
# ends 'Proved. 0 admissions'; that needs §6.9's regularity (WHAT.md stage
# 1 piece 2), which closes all five.
INT_SUBST_ADMISSIONS = {"P1.1-sheet": 5}
INT_SUBST_VERDICTS = {name: VERDICT.format(n=n)
                      for name, n in INT_SUBST_ADMISSIONS.items()}
INT_SUBST_ANSWERS = {"P1.1-sheet": "2"}
INT_SUBST_NUMERIC = {"P1.1-sheet": 2.0}

# --- Accepted moves ---------------------------------------------------------
#
# In MATCH_ACCEPTS' shape, after discharge: `goal_emits` is installation's
# list, `emits` the int_subst step's, `deriv` its step 10, and an optional
# `then` continues the proof, each step with its own list, to a verdict.
INT_SUBST_ACCEPTS = [
    {"id": "decreasing_literal_ends",
     "goal": "Int[x = 0 .. 1] 2*x == ?A",
     "goal_emits": [],  # 2*x owes nothing, and the range is literal
     "move": ("int_subst", {"var": "x", "sub": "1 - t", "new_var": "t",
                            "lo": "1", "hi": "0", "check": "ring",
                            "facts": []}),
     # E40: the new limits as given, reversed, which §5.1 reads as
     # -Int[t = 0 .. 1]; E4 orders the literal ends, so I' = [0, 1] and
     # nothing is owed for the orientation
     "goal_after": "Int[t = 1 .. 0] 2*(1 - t)*(0 + (0*t + (-1)*1)) == ?A",
     "deriv": {"var": "t", "F": "1 - t",
               "trace": [("d_add", "1 - t", ()), ("d_const", "1", ()),
                         ("route_neg", "-t", ()), ("d_mul", "-1*t", ()),
                         ("d_const", "-1", ()), ("d_var", "t", ())],
               "output": "0 + (0*t + (-1)*1)", "emits": ()},
     "emits": [
         ("1 - 1 == 0", "true", (S_SUBST_LO,), DISCHARGED, T_RING, True),
         ("1 - 0 == 1", "true", (S_SUBST_HI,), DISCHARGED, T_RING, True),
         ("1 - t in C^1([0, 1])", "[0, 1]", (S_SUBST_C1,), ADMITTED, T_REG,
          True),
         ("2*(1 - t) in C^0([0, 1])", "[0, 1]", (S_SUBST_C0,), ADMITTED,
          T_REG, True)],
     "then": [
         # ftc on a reversed literal range (the suite's own case, E4): the
         # premises on [0, 1] and (0, 1), the new goal F(b) - F(a) with
         # b = hi = 0 and a = lo = 1
         {"move": ("ftc", {"F": "t^2 - 2*t", "check": "ring", "facts": []}),
          "goal_after": "0^2 - 2*0 - (1^2 - 2*1) == ?A",
          "deriv": {"var": "t", "F": "t^2 - 2*t",
                    "trace": [("d_add", "t^2 - 2*t", ()),
                              ("d_pow_int", "t^2", ()), ("d_var", "t", ()),
                              ("route_neg", "-(2*t)", ()),
                              ("d_mul", "-1*(2*t)", ()),
                              ("d_const", "-1", ()), ("d_mul", "2*t", ()),
                              ("d_const", "2", ()), ("d_var", "t", ())],
                    "output": "2*t^1*1 + (0*(2*t) + (-1)*(0*t + 2*1))",
                    "emits": ()},
          "emits": [
              ("t^2 - 2*t in C^0([0, 1])", "[0, 1]", (S_FTC_C0F,), ADMITTED,
               T_REG, True),
              ("t^2 - 2*t in C^1((0, 1))", "(0, 1)", (S_FTC_C1F,), ADMITTED,
               T_REG, True),
              ("D[t](t^2 - 2*t) == 2*(1 - t)*(0 + (0*t + (-1)*1))", "(0, 1)",
               (S_FTC_D,), DISCHARGED, T_DERIV_RING, True),
              ("2*(1 - t)*(0 + (0*t + (-1)*1)) in C^0([0, 1])", "[0, 1]",
               (S_FTC_C0f,), ADMITTED, T_REG, True)]},
         {"move": ("close", {"value": "1", "check": "ring", "facts": []}),
          "goal_after": None, "emits": []},
     ],
     "report": VERDICT.format(n=5),
     "theorem": "Int[x = 0 .. 1] 2*x == 1",
     "why": "§5.1's reversed limits as normal output of a decreasing phi, "
            "handled by E4's literal ordering: the int_subst step owes no "
            "orientation, and ftc gives F(0) - F(1) = 0 - (1 - 2) = 1. "
            "SymPy: Int_1^0 2(1 - t)(-1) dt = 1 = Int_0^1 2x dx. The "
            "planted bug int_subst_sorts_new_limits turns the value into -1 "
            "and the close fails"},
    {"id": "non_monotone_accepted",
     "goal": "Int[x = 1 .. 1] x == ?A",
     "goal_emits": [],
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "-1", "hi": "1", "check": "ring",
                            "facts": []}),
     "goal_after": "Int[t = -1 .. 1] t^2*(2*t^1*1) == ?A",
     "deriv": INT_SUBST_DERIV[("P1.1-sheet", "s1")],
     "emits": [
         ("(-1)^2 == 1", "true", (S_SUBST_LO,), DISCHARGED, T_RING, True),
         ("1^2 == 1", "true", (S_SUBST_HI,), DISCHARGED, T_RING, True),
         ("t^2 in C^1([-1, 1])", "[-1, 1]", (S_SUBST_C1,), ADMITTED, T_REG,
          True),
         ("t^2 in C^0([-1, 1])", "[-1, 1]", (S_SUBST_C0,), ADMITTED, T_REG,
          True)],
     "why": "§6.4 keeps the no-monotonicity generality (and the review's "
            "'Do not weaken it'): t^2 folds [-1, 1] onto [0, 1], the "
            "endpoint interval is the point {1}, and the identity still "
            "holds, Int_1^1 x = 0 = Int_-1^1 2 t^3 dt (SymPy). Nothing is "
            "owed beyond the premises: x has no former. The twin that must "
            "refuse is INT_SUBST_BAD_MOVES non_monotone_divergent"},
    {"id": "ln_endpoints_by_exact_values",
     "goal": "Int[x = 0 .. 1] exp x == ?A",
     "goal_emits": [],
     "move": ("int_subst", {"var": "x", "sub": "ln t", "new_var": "t",
                            "lo": "1", "hi": "e_const", "check": "ring",
                            "facts": []}),
     "goal_after": "Int[t = 1 .. e_const] exp(ln t)*(1/t) == ?A",
     # d_ln on the closed range (E38), the same key as ln's former
     "deriv": {"var": "t", "F": "ln t",
               "trace": [("d_ln", "ln t", ("t > 0 @ [1, e_const]",)),
                         ("d_var", "t", ())],
               "output": "1/t", "emits": ("t > 0 @ [1, e_const]",)},
     "emits": [
         # step 8: e_const is not a literal, so the orientation is owed
         ("1 <= e_const", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_E, True),
         # step 9 (ln's former) and step 10 (d_ln), one key; step 13's
         # ln t again (merged)
         ("t > 0", "[1, e_const]", (S_FORMER, S_D_LN), DISCHARGED, T_RANGE,
          True),
         # step 11: E31's ln_one and ln_e make both literal, then ring
         ("ln 1 == 0", "true", (S_SUBST_LO,), DISCHARGED, T_RING_LN_ONE,
          True),
         ("ln e_const == 1", "true", (S_SUBST_HI,), DISCHARGED, T_RING_LN_E,
          True),
         ("ln t in C^1([1, e_const])", "[1, e_const]", (S_SUBST_C1,),
          ADMITTED, T_REG, True),
         ("exp(ln t) in C^0([1, e_const])", "[1, e_const]", (S_SUBST_C0,),
          ADMITTED, T_REG, True),
         # step 13: phi' = 1/t owes its divisor on the range
         ("t # 0", "[1, e_const]", (S_FORMER,), DISCHARGED, T_RANGE, True)],
     "certificates": {
         ("1 <= e_const", "true"): _farkas({GOAL: "1",
                                            FACT("e_gt_one"): "1"}),
         ("t > 0", "[1, e_const]"): _RANGE_LO,
         ("t # 0", "[1, e_const]"): _RANGE_LO_NZ},
     "why": "E39's exact values in the endpoint check: ln 1 and ln e_const "
            "are atoms to ring, and ln_one and ln_e make the equations 0 == "
            "0 and 1 == 1. SymPy: Int_1^e exp(ln t)/t dt = e - 1 = Int_0^1 "
            "exp x dx. The goal cannot be finished yet (no exp_ln entry "
            "rewrites exp(ln t)); the case pins the move only"},
    # --- owner answers 2026-09-24 ---------------------------------------
    # E46: a decreasing phi with symbolic ends, flipped. Was the refusal
    # decreasing_symbolic_ends ('obligation-decided-false' on pi/2 <= 0).
    {"id": "decreasing_symbolic_ends_flipped",
     "goal": "Int[x = 0 .. pi/2] cos x == ?A",
     # the limit pi/2 owes 2 # 0 (norm_num); cos is total
     "goal_emits": [("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
                     True)],
     "move": ("int_subst", {"var": "x", "sub": "pi/2 - t", "new_var": "t",
                            "lo": "pi/2", "hi": "0", "check": "ring",
                            "facts": []}),
     # step 8: pi/2 <= 0 is not discharged (FM with pi_pos finds its
     # negated goal feasible), 0 <= pi/2 is (linear, pi_pos): flipped
     "goal_after": "Int[t = 0 .. pi/2] -(cos(pi/2 - t)*(0 + (0*t + (-1)*1)))"
                   " == ?A",
     "deriv": {"var": "t", "F": "pi/2 - t",
               "trace": [("d_add", "pi/2 - t", ()), ("d_const", "pi/2", ()),
                         ("route_neg", "-t", ()), ("d_mul", "-1*t", ()),
                         ("d_const", "-1", ()), ("d_var", "t", ())],
               "output": "0 + (0*t + (-1)*1)", "emits": ()},
     "emits": [
         # lo's pi/2 (step 8), sub's pi/2 (step 9, closed: true), and the
         # new goal's limit and body (step 14): one key, not new
         ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False),
         ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI, True),
         ("pi/2 - pi/2 == 0", "true", (S_SUBST_LO,), DISCHARGED, T_RING,
          True),
         ("pi/2 - 0 == pi/2", "true", (S_SUBST_HI,), DISCHARGED, T_RING,
          True),
         ("pi/2 - t in C^1([0, pi/2])", "[0, pi/2]", (S_SUBST_C1,),
          ADMITTED, T_REG, True),
         ("cos(pi/2 - t) in C^0([0, pi/2])", "[0, pi/2]", (S_SUBST_C0,),
          ADMITTED, T_REG, True)],
     "certificates": {("0 <= pi/2", "true"): _PI_HALF},
     "why": "E46: §5.1's reversed integral, flipped to an oriented one. "
            "Int_{pi/2}^0 cos(pi/2 - t)(-1) dt = Int_0^{pi/2} "
            "-(cos(pi/2 - t)(-1)) dt = 1 = Int_0^{pi/2} cos x dx (SymPy). "
            "The key pi/2 <= 0 is never emitted, so nothing is refuted"},
    # E46: §5.1's canonical case, x = cos(theta) over [pi/2, 0], on the
    # owner's example. The move is accepted; the goal cannot be finished
    # yet (it needs pyth and a sign fact for cos on [0, pi/2]).
    {"id": "cos_theta_canonical",
     "goal": "Int[x = 0 .. 1] sqrt(1 - x^2) == ?A",
     # E26's known gap: 1 - x^2 >= 0 is non-strict, so sign product does not
     # close it (TAG_RULES), FM sees x^2 as opaque, and it is true, so F3
     # finds no point: admitted, tagged none (STAGE0.md S8's degeneracy)
     "goal_emits": [("1 - x^2 >= 0", "[0, 1]", (S_FORMER,), ADMITTED,
                     T_NONE, True)],
     "goal_reasons": {("1 - x^2 >= 0", "[0, 1]"): REASON_NONE},
     "move": ("int_subst", {"var": "x", "sub": "cos theta",
                            "new_var": "theta", "lo": "pi/2", "hi": "0",
                            "check": "ring", "facts": []}),
     "goal_after": "Int[theta = 0 .. pi/2] "
                   "-(sqrt(1 - (cos theta)^2)*(-sin theta * 1)) == ?A",
     "deriv": {"var": "theta", "F": "cos theta",
               "trace": [("d_cos", "cos theta", ()),
                         ("d_var", "theta", ())],
               "output": "-sin theta * 1", "emits": ()},
     "emits": [
         ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI, True),
         # the exact values in the endpoint check (E39)
         ("cos(pi/2) == 0", "true", (S_SUBST_LO,), DISCHARGED,
          T_RING_COS_PI_HALF, True),
         ("cos 0 == 1", "true", (S_SUBST_HI,), DISCHARGED, T_RING_COS_ZERO,
          True),
         ("cos theta in C^1([0, pi/2])", "[0, pi/2]", (S_SUBST_C1,),
          ADMITTED, T_REG, True),
         ("sqrt(1 - (cos theta)^2) in C^0([0, pi/2])", "[0, pi/2]",
          (S_SUBST_C0,), ADMITTED, T_REG, True),
         # the composed integrand's sqrt (step 14): cos theta is an opaque
         # atom, and F3's only candidate in the range is theta = 0, where
         # with cos_zero it reads 1 - 1^2 >= 0, true (1 is not shown to lie
         # in [0, pi/2] with pi_pos alone). Admitted, tagged none
         ("1 - (cos theta)^2 >= 0", "[0, pi/2]", (S_FORMER,), ADMITTED,
          T_NONE, True)],
     "certificates": {("0 <= pi/2", "true"): _PI_HALF},
     "reasons": {("1 - (cos theta)^2 >= 0", "[0, pi/2]"): REASON_NONE},
     "why": "§5.1's canonical reversed output, now accepted by E46's flip. "
            "The two none admissions are true and are the design's known "
            "gaps, not this move's: a non-strict polynomial sign (E26's "
            "note on sign product) and a cos atom. SymPy: Int_{pi/2}^0 "
            "sqrt(1 - cos^2)(-sin) = Int_0^{pi/2} sin^2 = pi/4 = Int_0^1 "
            "sqrt(1 - x^2)"},
    # the same substitution on an integrand that owes nothing, to a verdict
    {"id": "cos_theta_full",
     "goal": "Int[x = 0 .. 1] x == ?A",
     "goal_emits": [],
     "move": ("int_subst", {"var": "x", "sub": "cos theta",
                            "new_var": "theta", "lo": "pi/2", "hi": "0",
                            "check": "ring", "facts": []}),
     "goal_after": "Int[theta = 0 .. pi/2] -(cos theta * (-sin theta * 1))"
                   " == ?A",
     "deriv": {"var": "theta", "F": "cos theta",
               "trace": [("d_cos", "cos theta", ()),
                         ("d_var", "theta", ())],
               "output": "-sin theta * 1", "emits": ()},
     "emits": [
         ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI, True),
         ("cos(pi/2) == 0", "true", (S_SUBST_LO,), DISCHARGED,
          T_RING_COS_PI_HALF, True),
         ("cos 0 == 1", "true", (S_SUBST_HI,), DISCHARGED, T_RING_COS_ZERO,
          True),
         ("cos theta in C^1([0, pi/2])", "[0, pi/2]", (S_SUBST_C1,),
          ADMITTED, T_REG, True),
         ("cos theta in C^0([0, pi/2])", "[0, pi/2]", (S_SUBST_C0,),
          ADMITTED, T_REG, True)],
     "certificates": {("0 <= pi/2", "true"): _PI_HALF},
     "then": [
         {"move": ("ftc", {"F": "(sin theta)^2/2", "check": "ring",
                           "facts": []}),
          "goal_after": "(sin(pi/2))^2/2 - (sin 0)^2/2 == ?A",
          "deriv": {"var": "theta", "F": "(sin theta)^2/2",
                    "trace": [("route_div", "(sin theta)^2/2", ("2 # 0",)),
                              ("d_mul", "(sin theta)^2*(1/2)", ()),
                              ("d_pow_int", "(sin theta)^2", ()),
                              ("d_sin", "sin theta", ()),
                              ("d_var", "theta", ()),
                              ("d_const", "1/2", ())],
                    "output": ("2*(sin theta)^1*(cos theta * 1)*(1/2)"
                               " + (sin theta)^2*0"),
                    "emits": ("2 # 0",)},
          "emits": [
              ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI,
               False),
              ("2 # 0", "true", (S_FORMER, S_ROUTE_DIV), DISCHARGED,
               T_NORM_NUM, False),
              ("(sin theta)^2/2 in C^0([0, pi/2])", "[0, pi/2]",
               (S_FTC_C0F,), ADMITTED, T_REG, True),
              ("(sin theta)^2/2 in C^1((0, pi/2))", "(0, pi/2)",
               (S_FTC_C1F,), ADMITTED, T_REG, True),
              ("D[theta]((sin theta)^2/2) == -(cos theta * (-sin theta * 1))",
               "(0, pi/2)", (S_FTC_D,), DISCHARGED, T_DERIV_RING, True),
              ("-(cos theta * (-sin theta * 1)) in C^0([0, pi/2])",
               "[0, pi/2]", (S_FTC_C0f,), ADMITTED, T_REG, True)]},
         {"move": ("rewrite", {"entry": "sin_pi_half", "inst": {},
                               "at": "sin(pi/2)"}),
          "goal_after": "1^2/2 - (sin 0)^2/2 == ?A", "emits": []},
         {"move": ("rewrite", {"entry": "sin_zero", "inst": {},
                               "at": "sin 0"}),
          "goal_after": "1^2/2 - 0^2/2 == ?A", "emits": []},
         {"move": ("close", {"value": "1/2", "check": "ring", "facts": []}),
          "goal_after": None,
          "emits": [("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
                     False)]},
     ],
     "report": VERDICT.format(n=5),
     "theorem": "Int[x = 0 .. 1] x == 1/2",
     "why": "x = cos theta, decreasing with symbolic ends, to a verdict: "
            "the flip gives Int_0^{pi/2} sin(theta)cos(theta) = 1/2 = "
            "Int_0^1 x (SymPy). The planted bug int_subst_no_orientation "
            "keeps Int[theta = pi/2 .. 0], and ftc then owes pi/2 <= 0, "
            "refused by F2"},
    # E48: position. The sum's second integral (the owner's 'occurrence
    # 2'), which is occurrence 1 in E2's 0-based index.
    {"id": "sum_second_occurrence",
     "goal": "(Int[x = 0 .. 1] 2*x) + (Int[x = 0 .. pi^2/4] sin(sqrt x))"
             " == ?A",
     # the second Int's installation keys, exactly P1.1-sheet's; the first
     # owes nothing
     "goal_emits": list(INT_SUBST_OBLIGATIONS["P1.1-sheet"]["goal"]),
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "0", "hi": "pi/2", "check": "ring",
                            "facts": [], "occurrence": 1}),
     "goal_after": "(Int[x = 0 .. 1] 2*x)"
                   " + (Int[t = 0 .. pi/2] sin(sqrt(t^2))*(2*t^1*1)) == ?A",
     "deriv": INT_SUBST_DERIV[("P1.1-sheet", "s1")],
     # P is the goal's domain, true (a sum is not a binder): the emissions
     # are P1.1-sheet's s1, key for key
     "emits": list(INT_SUBST_OBLIGATIONS["P1.1-sheet"]["s1"]),
     "why": "E48's selector: occurrence 1 is the second Int in pre-order. "
            "The first stays over x beside the new one over t (sibling "
            "binders, as OCCURRENCE_CASE has). Without the occurrence the "
            "move is refused 'int-subst-ambiguous' (INT_SUBST_BAD_MOVES "
            "ambiguous_default)"},
    # E48: a position below D[y] where step 9 holds vacuously
    {"id": "under_D_constant_integral",
     "goal": "D[y](y*(Int[x = 0 .. 1] 2*x)) == ?A",
     "goal_emits": [],
     "move": ("int_subst", {"var": "x", "sub": "1 - t", "new_var": "t",
                            "lo": "1", "hi": "0", "check": "ring",
                            "facts": []}),
     "goal_after": "D[y](y*(Int[t = 1 .. 0] 2*(1 - t)*(0 + (0*t + (-1)*1))))"
                   " == ?A",
     "deriv": {"var": "t", "F": "1 - t",
               "trace": [("d_add", "1 - t", ()), ("d_const", "1", ()),
                         ("route_neg", "-t", ()), ("d_mul", "-1*t", ()),
                         ("d_const", "-1", ()), ("d_var", "t", ())],
               "output": "0 + (0*t + (-1)*1)", "emits": ()},
     # decreasing_literal_ends' four keys: y occurs in nothing the step reads
     "emits": [
         ("1 - 1 == 0", "true", (S_SUBST_LO,), DISCHARGED, T_RING, True),
         ("1 - 0 == 1", "true", (S_SUBST_HI,), DISCHARGED, T_RING, True),
         ("1 - t in C^1([0, 1])", "[0, 1]", (S_SUBST_C1,), ADMITTED, T_REG,
          True),
         ("2*(1 - t) in C^0([0, 1])", "[0, 1]", (S_SUBST_C0,), ADMITTED,
          T_REG, True)],
     "why": "E48's D test passes: y occurs in none of the Int's limits and "
            "body, sub, lo or hi, so no emitted key mentions y and step 9 "
            "holds vacuously; the integral is a constant in y and the "
            "equality holds for every y. The twin that must refuse is "
            "INT_SUBST_BAD_MOVES under_D_body_mentions_y"},
    # E45: reverse mode with a non-monotone g, accepted
    {"id": "reverse_non_monotone",
     "goal": "Int[x = -1 .. 1] 2*x^3 == ?A",
     "goal_emits": [],
     "move": ("int_subst", {"mode": "reverse", "var": "x", "sub": "x^2",
                            "new_var": "u", "lo": "1", "hi": "1", "f": "u",
                            "check": "ring", "facts": []}),
     "goal_after": "Int[u = 1 .. 1] u == ?A",
     "deriv": {"var": "x", "F": "x^2",
               "trace": [("d_pow_int", "x^2", ()), ("d_var", "x", ())],
               "output": "2*x^1*1", "emits": ()},
     "emits": [
         # step 11: 2*x^3 == x^2*(2*x^1*1) on [-1, 1] by ring
         ("2*x^3 == x^2*(2*x^1*1)", "[-1, 1]", (S_SUBST_INT,), DISCHARGED,
          T_DERIV_RING, True),
         ("(-1)^2 == 1", "true", (S_SUBST_LO,), DISCHARGED, T_RING, True),
         ("1^2 == 1", "true", (S_SUBST_HI,), DISCHARGED, T_RING, True),
         ("x^2 in C^1([-1, 1])", "[-1, 1]", (S_SUBST_C1,), ADMITTED, T_REG,
          True),
         # f(g(x)) = u[u := x^2]: f's continuity on the image [0, 1],
         # stated over the old range (E45)
         ("x^2 in C^0([-1, 1])", "[-1, 1]", (S_SUBST_C0,), ADMITTED, T_REG,
          True)],
     "why": "E45's image argument: x^2 maps [-1, 1] onto [0, 1], the new "
            "limits are both 1, and the premise is stated on f(g(x)) over "
            "[-1, 1], not on an interval of u, so no monotonicity is "
            "needed. Int_-1^1 2x^3 = 0 = Int_1^1 u (SymPy). The twin that "
            "must refuse is holpy_probe_reverse"},
]

# --- Must-refuse ------------------------------------------------------------
#
# In BAD_MOVES' shape. `message` is INT_SUBST_MESSAGES' template filled
# (a dict of its fields, terms as GRAMMAR.md strings shown after parsing),
# or DECIDED_FALSE_MESSAGES' (via _point / _negation), or E27_MESSAGES'
# (`e27`, as the E27 BAD_MOVES cases). Every refused step emits nothing.
INT_SUBST_BAD_MOVES = [
    # E42: freshness and scope
    {"id": "not_fresh_free",
     "goal": "Int[x = 0 .. 1] x*y == ?A @ y > 0", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "y^2", "new_var": "y",
                            "lo": "0", "hi": "1", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-not-fresh",
     "message": ("int-subst-not-fresh", {"new_var": "y"}),
     "why": "y is free in the goal (its domain and integrand). Accepted, "
            "the new goal would bind y and keep it free, and check_goal's "
            "D11 would refuse it last (the planted bug "
            "int_subst_skips_freshness shows that backstop)"},
    {"id": "not_fresh_same_variable",
     "goal": "Int[x = 0 .. 1] 2*x == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "2*x", "new_var": "x",
                            "lo": "0", "hi": "1/2", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-not-fresh",
     "message": ("int-subst-not-fresh", {"new_var": "x"}),
     "why": "x is the binder being replaced; a rename is not a move (E16's "
            "argument). Mathematically sound (Int_0^{1/2} 2(2x)*2 dx = 1), "
            "so this refusal is about naming, and it comes before the "
            "scope check that would otherwise pass"},
    {"id": "not_fresh_bound_in_body",
     "goal": "Int[x = 0 .. 1] (Int[t = 0 .. 1] x*t) == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "0", "hi": "1", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-not-fresh",
     "message": ("int-subst-not-fresh", {"new_var": "t"}),
     "why": "t is bound inside the body. Substituting t^2 there is the "
            "capture case: terms.subst would rename the inner binder, "
            "which is sound but silently changes the learner's names, so "
            "freshness refuses first"},
    {"id": "scope_old_variable",
     "goal": "Int[x = 0 .. 1] 2*x == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "x*t", "new_var": "t",
                            "lo": "0", "hi": "1", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-scope",
     "message": ("int-subst-scope", {"part": "the substitution",
                                     "term": "x*t", "name": "x"}),
     "why": "x is bound by the integral being replaced; after the move it "
            "would be free, a name the goal never had"},
    {"id": "scope_new_variable_in_limit",
     "goal": "Int[x = 0 .. 1] 2*x == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t", "new_var": "t",
                            "lo": "t - t", "hi": "1", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-scope",
     "message": ("int-subst-scope", {"part": "the lower limit",
                                     "term": "t - t", "name": "t"}),
     "why": "GRAMMAR.md §5: a bound variable may not occur in its own "
            "endpoints, even where ring would cancel it"},
    # E36: the shape of the goal and the args
    {"id": "no_integral_under_D",
     "goal": "D[y](Int[x = 0 .. y] x) == ?A @ 0 <= y", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "0", "hi": "sqrt y", "check": "ring",
                            "facts": []}),
     # owner answers (E48): was 'int-subst-no-integral', when only the
     # top-level lhs was reached. The Int is now selected where it is, and
     # below D[y] its upper limit mentions y (so do hi's sqrt y and the
     # range [0, y]), so step 6 refuses it as rewrite's step 9 would
     "refusal": "rewrite-under-D-needs-open-domain",
     "why": "the task's substitution under D[y], now reached by the "
            "selector: the step would emit keys on the closed ranges "
            "[0, y] and [0, sqrt y], not open in y (§6.1 rev 9, E11). The "
            "goal installs: x owes nothing, so no key uses [0, y]"},
    {"id": "wrong_variable",
     "goal": P1_1_SHEET_GOAL, "setup": [],
     "move": ("int_subst", {"var": "y", "sub": "t^2", "new_var": "t",
                            "lo": "0", "hi": "pi/2", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-wrong-variable",
     # owner answers (E48): with no occurrence, the '/none' template
     "message": ("int-subst-wrong-variable/none", {"var": "y"}),
     "why": "the learner named a variable no integral binds"},
    {"id": "infinite_endpoint",
     "goal": "Int[x = 1 .. oo] exp(-x) == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t + 1", "new_var": "t",
                            "lo": "0", "hi": "1", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-infinite-endpoint",
     "message": ("int-subst-infinite-endpoint", {"limit": "oo"}),
     "why": "sub(hi) == oo is not a term (§5.1); an improper integral is "
            "int_improper's, as for ftc (E9). Refused before anything is "
            "read from the args' limits"},
    {"id": "phi_prime_supplied",
     "goal": P1_1_SHEET_GOAL, "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "0", "hi": "pi/2", "check": "ring",
                            "facts": [], "dsub": "t"}),
     "refusal": "bad-args",
     "why": "the task's 'wrong phi'': not applicable, because phi' is "
            "deriv's output and never an argument (E41). The move's key "
            "set is exact, so a supplied phi', right or wrong, is bad-args"},
    # E39: the endpoints
    {"id": "endpoints_do_not_map",
     "goal": P1_1_SHEET_GOAL, "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "0", "hi": "pi", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-endpoint-mismatch",
     "message": ("int-subst-endpoint-mismatch",
                 {"image": "pi^2", "limit": "pi^2/4", "end": "upper"}),
     "residual": "pi^2 - pi^2/4",
     "compare": ("ring", ()),
     "why": "ring leaves (3/4)*pi^2. Before it the step's other emissions "
            "hold (0 <= pi linear with pi_pos; 0^2 == 0), so the mismatch "
            "is the refusal"},
    {"id": "sin_guess_from_8_1",
     "goal": P1_1_SHEET_GOAL, "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "sin t", "new_var": "t",
                            "lo": "0", "hi": "pi/2", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-endpoint-mismatch",
     "message": ("int-subst-endpoint-mismatch",
                 {"image": "sin(pi/2)", "limit": "pi^2/4", "end": "upper"}),
     # after sin_pi_half (E39): 1 == pi^2/4
     "residual": "1 - pi^2/4",
     "compare": ("ring", ()),
     "why": "DESIGN.md §8.1's 'your guess', shown there as '✓ legal'. The "
            "lower end holds by sin_zero, and the upper reads 1 == pi^2/4 "
            "after sin_pi_half, false; no t has sin t = pi^2/4 (> 1). "
            "DESIGN_DEFECTS records it"},
    # E38, E43: definedness on the new range, decided false
    {"id": "phi_undefined_on_new_range",
     "goal": "Int[x = 0 .. 1] exp x == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "ln t", "new_var": "t",
                            "lo": "0", "hi": "1", "check": "ring",
                            "facts": []}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("t > 0 @ [0, 1]", "0 > 0", t="0"),
     "why": "step 9: ln t owes t > 0 on [0, 1], false at the closed lower "
            "end (F3's first candidate). It comes before the endpoint "
            "check, whose ln 0 == 0 is not decided by anything. The twin "
            "over [1, e_const] is INT_SUBST_ACCEPTS "
            "ln_endpoints_by_exact_values"},
    {"id": "non_monotone_divergent",
     "goal": "Int[x = 1 .. 1] 1/x == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "-1", "hi": "1", "check": "ring",
                            "facts": []}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     # regularity build 2026-09-25, adjudicated (DATA_CHANGES): step 13's
     # C^0 premise 1/t^2 in C^0([-1, 1]) is emitted before step 14's formers
     # (INT_SUBST_RULE step 15) and is refuted by E63 through its div side
     "message": _reg_undefined("1/t^2 in C^0([-1, 1])", "t^2 # 0 @ [-1, 1]",
                               _point("t^2 # 0 @ [-1, 1]", "0^2 # 0",
                                      t="0")),
     "was": "_point('t^2 # 0 @ [-1, 1]', '0^2 # 0', t='0'), the new "
            "integrand's divisor at step 14, before regularity",
     "why": "§6.4's own example of why the C^0 premise is on the composed "
            "integrand: the endpoint interval is {1}, so f = 1/x is fine "
            "there, but (1/t^2)*(2*t) has a pole at 0 in [-1, 1] and "
            "Int_-1^1 2/t diverges. Step 13 charges the new integrand's "
            "divisor t^2 # 0 on [-1, 1]: F3 passes the ends -1 and 1 and "
            "refutes at the midpoint 0 (decided_false_pole's pattern). "
            "Installation owes x # 0 @ [1, 1] (range, discharged). This is "
            "HolPy's first probe (§4.2), in forward form, and §17's "
            "'non-monotone int_subst' must-refuse"},
    # E42: substitution into D, GRAMMAR.md §5's rule, reached through a move
    {"id": "subst_under_D_of_the_variable",
     "goal": "Int[x = 0 .. 1] D[x](x^2) == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "0", "hi": "1", "check": "ring",
                            "facts": []}),
     "refusal": "subst-under-D",
     "why": "(D[x] x^2)[x := t^2] is 2 t^2, but no term of the grammar "
            "writes it by pushing the substitution inside, and the naive "
            "D[x]((t^2)^2) is 0 (SymPy); D10 refuses every y = x case. The "
            "first move to reach REFUSAL_CODES' 'subst-under-D' "
            "('unreachable in P1')"},
    {"id": "subst_under_D_capture",
     "goal": "Int[x = 0 .. 1] D[y](x*y) == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "y*t", "new_var": "t",
                            "lo": "0", "hi": "1", "check": "ring",
                            "facts": []}),
     "refusal": "subst-under-D",
     "why": "y is free in the goal (D10), so y*t is in scope (E42), but "
            "substituting it under D[y] would capture: (D[y](x*y))[x := "
            "y*t] is y*t, while D[y](y*t*y) is 2*y*t (SymPy). D10's "
            "second clause needs y not free in the substituted term"},
    # E43: an Int in phi is refused by deriv
    {"id": "sub_holds_Int",
     "goal": "Int[x = 0 .. 1] 2*x == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "Int[s = 0 .. t] s",
                            "new_var": "t", "lo": "0", "hi": "1",
                            "check": "ring", "facts": []}),
     "refusal": "deriv-no-rule",
     "why": "E26 (b) through deriv (E12): the Int has t free in its limit, "
            "so d_const does not apply and no §6.3 rule does. Steps 8 and "
            "9 emit nothing (s owes nothing), and the step is refused at "
            "step 10 before any endpoint check"},
    # E42: E19 unchanged
    {"id": "close_with_new_variable",
     "goal": P1_1_SHEET_GOAL,
     "state": ("P1.1-sheet", "s6"),
     "move": ("close", {"value": "t - t + 2", "check": "ring", "facts": []}),
     "refusal": "close-not-evaluated",
     "e27": {"clause": "b", "at": "t - t + 2",
             "message": "t - t + 2 is unreduced literal arithmetic"},
     "why": "P1.1's close_bound_variable_ring_true is refused "
            "'close-scope-bound-variable' because t is bound in its "
            "original goal. Here the original goal is the sheet's, which "
            "binds only x, so E19 passes, ring proves the close, and the "
            "theorem Int[x = 0 .. pi^2/4] sin(sqrt x) == t - t + 2 would be "
            "true for every t, so nothing unsound is at stake. E27 (b2) "
            "refuses the form: the maximal sum's normal form has 1 "
            "monomial against 3"},
    # --- owner answers 2026-09-24 ---------------------------------------
    # E48: selection
    {"id": "no_integral_anywhere",
     "goal": "sin 1 + 1 == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "0", "hi": "1", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-no-integral",
     "message": ("int-subst-no-integral", {}),
     "why": "no Int node on the non-?A side, so nothing to select"},
    {"id": "ambiguous_default",
     "goal": "(Int[x = 0 .. 1] 2*x) + (Int[x = 0 .. pi^2/4] sin(sqrt x))"
             " == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "0", "hi": "pi/2", "check": "ring",
                            "facts": []}),
     "refusal": "int-subst-ambiguous",
     "message": ("int-subst-ambiguous", {"n": "2", "var": "x"}),
     "why": "E48's default is exactly one Int binding var, not E2's every "
            "occurrence: the two integrals have different limits, and one "
            "set of args fits one integral's endpoint equations. The "
            "accepted twin is INT_SUBST_ACCEPTS sum_second_occurrence"},
    {"id": "occurrence_out_of_range",
     "goal": "(Int[x = 0 .. 1] 2*x) + (Int[x = 0 .. pi^2/4] sin(sqrt x))"
             " == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "0", "hi": "pi/2", "check": "ring",
                            "facts": [], "occurrence": 2}),
     "refusal": "int-subst-no-integral",
     "message": ("int-subst-no-integral/occurrence", {"occurrence": "2"}),
     "why": "the goal has two Ints, occurrences 0 and 1 (E2's index), as "
            "rewrite's out-of-range index refuses (REWRITE_RULE's "
            "arguments)"},
    # E48: under D[y], as rewrite's step 9
    {"id": "under_D_body_mentions_y",
     "goal": "D[y](Int[x = 0 .. 1] x*y) == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "1 - t", "new_var": "t",
                            "lo": "1", "hi": "0", "check": "ring",
                            "facts": []}),
     "refusal": "rewrite-under-D-needs-open-domain",
     "why": "y occurs in the body, so the composed-integrand premise "
            "(1 - t)*y in C^0([0, 1]) mentions y, and a regularity "
            "judgement is not an open condition in y: step 9 (a) cannot be "
            "met. Conservative, as E11 (b) is (Leibniz would allow it). The "
            "accepted twin is INT_SUBST_ACCEPTS under_D_constant_integral"},
    # E46: neither order decided
    {"id": "orientation_undecided",
     "goal": "Int[x = 0 .. 1] 2*x == ?A @ y # 0", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "y*t", "new_var": "t",
                            "lo": "0", "hi": "1/y", "check": "field",
                            "facts": []}),
     "refusal": "int-subst-orientation-undecided",
     "message": ("int-subst-orientation-undecided", {"lo": "0",
                                                     "hi": "1/y"}),
     "why": "step 8: hi's 1/y owes y # 0 @ y # 0, discharged by hyp; then "
            "neither 0 <= 1/y nor 1/y <= 0 is discharged (inv(y) is an "
            "opaque atom, and a NonZero item gives no Farkas label), since "
            "the substitution is increasing for y > 0 and decreasing for "
            "y < 0. The endpoint equations would hold (y*0 == 0 by ring, "
            "y*(1/y) == 1 by field at y # 0). Stating @ y > 0 is the "
            "learner's move. Under E4 alone this orientation would have "
            "been admitted, tagged none"},
    # E45: reverse mode
    {"id": "reverse_g_undefined",
     "goal": "Int[x = 0 .. 1] 2*x == ?A", "setup": [],
     "move": ("int_subst", {"mode": "reverse", "var": "x", "sub": "ln x",
                            "new_var": "u", "lo": "0", "hi": "0", "f": "u",
                            "check": "ring", "facts": []}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("x > 0 @ [0, 1]", "0 > 0", x="0"),
     "why": "step 9: g = ln x owes x > 0 on the old range [0, 1], false at "
            "the closed lower end, before the integrand check or the "
            "endpoints are read"},
    {"id": "holpy_probe_reverse",
     "goal": "Int[x = -1 .. 1] x^2 == ?A", "setup": [],
     "move": ("int_subst", {"mode": "reverse", "var": "x", "sub": "x^2",
                            "new_var": "u", "lo": "1", "hi": "1",
                            "f": "sqrt u/2", "check": "ring", "facts": []}),
     "refusal": "int-subst-check-failed",
     "message": ("int-subst-check-failed", {"f": "sqrt u/2"}),
     "residual": "x^2 - (sqrt(x^2)/2)*(2*x^1*1)",
     "compare": ("ring", ()),
     "why": "HolPy's first probe (§4.2): Int_-1^1 x^2 by u = x^2, whose "
            "new limits 1 .. 1 give 0 against the true 2/3. Steps 8-10 "
            "hold (f(g(x)) = sqrt(x^2)/2 owes 2 # 0 and x^2 >= 0 on "
            "[-1, 1], both discharged), and the check fails: x^2 is not "
            "x*sqrt(x^2), which is -x^2 for x < 0, and no fact makes "
            "sqrt(x^2) equal to x. With the check skipped the move would "
            "prove the false 2/3 == 0 (planted bug "
            "int_subst_reverse_skips_check)"},
    {"id": "reverse_f_mentions_old_variable",
     "goal": "Int[x = 0 .. 1] x*exp(x^2) == ?A", "setup": [],
     "move": ("int_subst", {"mode": "reverse", "var": "x", "sub": "x^2",
                            "new_var": "u", "lo": "0", "hi": "1",
                            "f": "x*u", "check": "ring", "facts": []}),
     "refusal": "int-subst-scope",
     "message": ("int-subst-scope", {"part": "the new integrand",
                                     "term": "x*u", "name": "x"}),
     "why": "E42: f is a term in new_var; x would be free in the new goal"},
    {"id": "f_in_forward_mode",
     "goal": P1_1_SHEET_GOAL, "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "t^2", "new_var": "t",
                            "lo": "0", "hi": "pi/2", "check": "ring",
                            "facts": [], "f": "t"}),
     "refusal": "bad-args",
     "why": "E45: 'f' belongs to reverse mode; forward mode's new integrand "
            "is built by the kernel (E41)"},
]

# --- Planted bugs for the build to add --------------------------------------
#
# One per rule of the move whose loss could produce a false 'Proved' or a
# wrong goal. The seams are the architecture's to name (ARCHITECTURE.md
# §7); the data fixes the mutation and what must catch it. caught_by
# locations: (proof, step, key, dom) for a list, (proof, step, 'goal_after')
# or (proof, step, 'refused'), ('INT_SUBST_BAD_MOVES' | 'INT_SUBST_ACCEPTS',
# id) for a case whose outcome changes, and ('S0', ...) for problems/stage0
# section 12. N where it moves.
INT_SUBST_PLANTED_BUGS = {
    "int_subst_skips_endpoint_check": {
        "mutation": "both endpoint equations are recorded discharged "
                    "without running the exact values or the check",
        "caught_by": [("INT_SUBST_BAD_MOVES", "endpoints_do_not_map"),
                      ("INT_SUBST_BAD_MOVES", "sin_guess_from_8_1"),
                      ("S0", "SUB1-W1")]},
    "int_subst_drops_phi_prime": {
        "mutation": "the new integrand is F alone, without phi' (the "
                    "forgotten dx)",
        # P1.1-sheet: s2 then gives sin t, and s3's check fails against
        # deriv(F) = 2 t sin t ('ftc-check-failed')
        "caught_by": [("P1.1-sheet", "s1", "goal_after"),
                      ("P1.1-sheet", "s3", "refused"),
                      ("INT_SUBST_ACCEPTS", "decreasing_literal_ends"),
                      ("S0", "SUB1", "s1", "goal_after")]},
    "int_subst_deriv_on_open": {
        "mutation": "deriv's side conditions are emitted on the open "
                    "interval instead of the closed range",
        # S2 via sqrt u: d_sqrt's u > 0 moves to (0, 1) and is discharged;
        # the step then fails at the upper endpoint, sqrt 1 == 1, which ring
        # cannot decide, so the code changes. ln: d_ln's key moves to
        # (1, e_const), a new key, and t > 0 @ [1, e_const] loses d_ln
        "caught_by": [("S0", "S2-SUB-W1"),
                      ("INT_SUBST_ACCEPTS", "ln_endpoints_by_exact_values")]},
    "int_subst_C0_on_original_integrand": {
        "mutation": "the forward C^0 premise is f on the old range, "
                    "Reg(body, 0, P + [a, b]), revision 1's statement that "
                    "§11.1 corrects",
        "caught_by": [("P1.1-sheet", "s1", "sin(sqrt(t^2)) in "
                       "C^0([0, pi/2])", "[0, pi/2]"),
                      ("S0", "SUB1", "s1", "(1 - t^2)*sqrt(1 - (1 - t^2)) in "
                       "C^0([0, 1])", "[0, 1]")]},
    # owner answers: the orientation now decides the form (E46)
    "int_subst_no_orientation": {
        "mutation": "step 8's orientation is neither decided nor emitted, "
                    "and the given limits are always kept",
        # decreasing_symbolic_ends_flipped keeps Int[t = pi/2 .. 0] and
        # loses 0 <= pi/2; cos_theta_full's ftc then owes pi/2 <= 0 and is
        # refused by F2; orientation_undecided is accepted. In P1.1-sheet
        # the orientation is still emitted by step 14 (t^2 >= 0 uses the
        # range), so it is not caught there
        "caught_by": [("INT_SUBST_ACCEPTS", "decreasing_symbolic_ends_flipped"),
                      ("INT_SUBST_ACCEPTS", "cos_theta_full"),
                      ("INT_SUBST_BAD_MOVES", "orientation_undecided")]},
    "int_subst_flips_without_decision": {
        "mutation": "the new integral is flipped whenever lo <= hi is not "
                    "discharged, without discharging hi <= lo",
        "caught_by": [("INT_SUBST_BAD_MOVES", "orientation_undecided")]},
    "int_subst_skips_freshness": {
        "mutation": "step 4 is skipped",
        # not_fresh_free then reaches check_goal ('D11-bound-and-free');
        # not_fresh_same_variable is accepted (sound, E42);
        # not_fresh_bound_in_body is accepted with the inner binder renamed
        # or refused by check_goal; each differs from int-subst-not-fresh
        "caught_by": [("INT_SUBST_BAD_MOVES", "not_fresh_free"),
                      ("INT_SUBST_BAD_MOVES", "not_fresh_same_variable"),
                      ("INT_SUBST_BAD_MOVES", "not_fresh_bound_in_body")]},
    "int_subst_sorts_new_limits": {
        "mutation": "the new integral's literal limits are ordered, "
                    "Int[t = min .. max], instead of kept as given",
        # a decreasing phi loses its sign: SUB1 reaches -4/15 and its close
        # with 4/15 fails; decreasing_literal_ends reaches -1
        "caught_by": [("INT_SUBST_ACCEPTS", "decreasing_literal_ends"),
                      ("S0", "SUB1", "s1", "goal_after"),
                      ("S0", "SUB1", "s4", "refused")]},
    # owner answers: position (E48)
    "int_subst_occurrence_ignored": {
        "mutation": "the first Int binding var is taken whatever the "
                    "occurrence",
        "caught_by": [("INT_SUBST_ACCEPTS", "sum_second_occurrence"),
                      ("INT_SUBST_BAD_MOVES", "occurrence_out_of_range")]},
    "int_subst_under_D_unchecked": {
        "mutation": "step 6 is skipped",
        "caught_by": [("INT_SUBST_BAD_MOVES", "under_D_body_mentions_y"),
                      ("INT_SUBST_BAD_MOVES", "no_integral_under_D")]},
    # owner answers: reverse mode (E45)
    "int_subst_reverse_skips_check": {
        "mutation": "reverse mode's integrand check is recorded without "
                    "running it",
        # holpy_probe_reverse is then accepted, a proof of the false
        # Int_-1^1 x^2 == Int_1^1 ... (2/3 against 0)
        "caught_by": [("INT_SUBST_BAD_MOVES", "holpy_probe_reverse"),
                      ("S0", "S2R-W1")]},
    "int_subst_reverse_premise_on_new_range": {
        "mutation": "reverse mode states f in C^0 on the interval between "
                    "the new limits instead of f(g(x)) in C^0([a, b])",
        "caught_by": [("INT_SUBST_ACCEPTS", "reverse_non_monotone"),
                      ("S0", "S2R", "s1", "exp(x^2)/2 in C^0([0, 1])",
                       "[0, 1]")]},
    # owner answers: the sqrt sign fact (E49), a trusted checker rule
    "sqrt_fact_strict": {
        "mutation": "the Farkas checker reads a ('fact', 'sqrt_nonneg', u) "
                    "label as sqrt u > 0",
        "caught_by": [("SQRT_FACT_MUST_REJECT", "sqrt_fact_nonstrict_pair"),
                      ("PROPERTY", "farkas")]},
}

# --- The sqrt sign fact (E49, owner answers 2026-09-24) --------------------
#
# Pinned for entries.py in NAMED_ENTRIES' shape, appended after cos_zero
# (ENTRIES goes from 16 to 17 entries). Its position is immaterial: E27 (a)
# reads only equation entries, E31 only equations with no schema variable,
# and TAG_RULES' cite looks for an ordering conclusion, which only a key
# sqrt u >= 0 or 0 <= sqrt u would match (none exists in the data).
SQRT_NONNEG_ENTRY = {
    "sqrt_nonneg": {
        "statement": "sqrt a >= 0 @ a >= 0",
        "schema": ("a",),
        "hyps": ("a >= 0",),
        "use": "sign fact: joins the linear method's constraint set for each "
               "sqrt atom of a key (E49), as pi_pos does for pi; also a "
               "cite entry",
        "cite": "§6.8's sign-fact row, by the owner's decision (E49); the "
                "square root's range, Rocq's sqrt_pos in Stdlib.Reals",
        "used_in": ("problems/stage0 SUB2 (1 + sqrt x # 0 @ [0, 4], "
                    "1 + sqrt(t^2) # 0 @ [0, 2])",),
    },
}

SQRT_FACT_RULE = (
    "Amends DISCHARGE_RULE's 'constraint set' and 'Farkas certificate' "
    "paragraphs, and TAG_RULES' range/linear paragraph, at the build. A "
    "label ('fact', 'sqrt_nonneg', u), u a term, is in a key's constraint "
    "set exactly when an atom sqrt w occurs in the key's proposition or "
    "domain with ring_nf(w) = ring_nf(u) (the atom identity of §6.2); its "
    "constraint is (sqrt u, not strict), meaning sqrt u >= 0. The search "
    "and the tagger add one such constraint per distinct sqrt atom of the "
    "key, beside the named constants' sign facts, and a certificate using "
    "one with a positive multiplier cites 'sqrt_nonneg', after pi_pos and "
    "e_gt_one. The suite compares such a label by ring_nf of u.",

    "Its hypothesis. sqrt_nonneg owes a >= 0, and the checker asks no "
    "child certificate for it. DISCHARGE_RULE's trust split says an "
    "accepted certificate proves the obligation at every point of its "
    "domain where its terms are defined, definedness being carried by the "
    "separate former keys (E6, E26). At such a point every sqrt atom of "
    "the key is defined, so its argument is >= 0 and the atom is >= 0: the "
    "hypothesis is the atom's own definedness, which the sqrt former "
    "already charged, u >= 0, at the position where that sqrt entered. "
    "That is why the label needs the atom to occur in the key: a sqrt "
    "that does not occur is no term of the key, and nothing makes it "
    "defined there.",

    "Why a label and not a Γ item or a cite. A cite needs the conclusion "
    "to imply the proposition syntactically (TAG_RULES), and sqrt u >= 0 "
    "implies 1 + sqrt u # 0 only through arithmetic; the Farkas "
    "combination is that arithmetic, checked.",
)

# Every key in either data file holding a sqrt atom, re-derived by hand
# under SQRT_FACT_RULE: NONE changes tag, certificate, status or outcome.
# The fact adds one non-strict constraint s >= 0 per atom. It can close a
# target only if the negated target plus a positive multiple of s >= 0 sums
# to a negative constant, or to 0 with a strict constraint used, and in
# every key below s appears with the sign that needs s > 0 or s # 0.
SQRT_FACT_CHANGES = {
    ("2*sqrt x # 0", "(0, pi^2/4)"): "as 2s > 0, the negated goal -2s >= 0 "
        "plus 2(s >= 0) sums to 0 with nothing strict; as 2s < 0, the "
        "negated goal 2s >= 0 is consistent with s >= 0. Still sign product "
        "with sqrt_pos (P1.1-fallback)",
    ("sqrt 3 # 0", "true"): "the same shape, s # 0: still cite sqrt_pos "
        "(P1.2, P1.2-alt)",
    ("3*sqrt 3 # 0", "true"): "the same: still sign product (P1.2)",
    ("1 + ((2*x - 1)/sqrt 3)^2 # 0", "(0, 1)"): "sqrt 3 occurs only inside "
        "inv(sqrt 3); the target's monomials are x^2*inv(sqrt 3)^2 and the "
        "like, which s >= 0 does not touch: still sign (P1.2)",
    ("sqrt 4 # 0", "true"): "DISCHARGE_MUST_REJECT's if_emitted outcome: "
        "still cite sqrt_pos, 4 > 0 literal",
    ("sqrt a # 0", "[0, 1]"): "DISCHARGE_MUST_REJECT "
        "farkas_schema_entry_as_fact's key and if_emitted: s >= 0 cannot "
        "give s # 0, and F3 still refutes at a = 0 with sqrt_zero",
    ("sqrt x # 0", "[0, 1]"): "DISCHARGE_BAD_MOVES_ADDED "
        "decided_false_sqrt_at_end and the must-reject cases on it: still "
        "refused at x = 0, since no certificate comes first",
    ("sqrt x # 0", "(0, 1)"): "DISCHARGE_CHECKER_ACCEPTS: its certificate "
        "is unchanged and still accepted; the search's first certificate "
        "is still the cite",
    "every other key": "holds no sqrt atom (t^2 >= 0, x >= 0, 1 - x >= 0 "
        "and the like are sqrt formers' own keys, whose propositions are "
        "the argument, not the atom), so its constraint set is unchanged; "
        "Reg keys and in-step equations are not searched",
}

# The checker's new label called directly, in DISCHARGE_MUST_REJECT's and
# DISCHARGE_CHECKER_ACCEPTS' shape (truth: ('true',) or ('false', point)).
SQRT_FACT_MUST_REJECT = [
    {"id": "sqrt_fact_nonstrict_pair",
     "key": ("sqrt x > 0", "[0, 1]"),
     "certificate": _farkas({GOAL: "1", SQRT("x"): "1"}),
     "expected": "rejected",
     "rejects_because": "the combination sums to 0 and both constraints "
                        "are non-strict (-sqrt x >= 0 and sqrt x >= 0)",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _point("sqrt x > 0 @ [0, 1]", "0 > 0",
                                      entries=("sqrt_zero",), x="0"))},
    {"id": "sqrt_fact_absent_atom",
     "key": ("1 + x > 0", "[0, 1]"),
     "certificate": _farkas({GOAL: "1", SQRT("x"): "1"}),
     "expected": "rejected",
     "rejects_because": "no sqrt x occurs in the key, so the label is not "
                        "in its constraint set",
     "truth": ("true",),
     "if_emitted": ("discharged", T_RANGE)},
]
SQRT_FACT_CHECKER_ACCEPTS = [
    {"id": "sqrt_fact_one_plus_sqrt",
     "key": ("1 + sqrt x # 0", "[0, 4]"),
     "certificate": _farkas({GOAL: "1", SQRT("x"): "1"}, ">"),
     "tag": T_LINEAR_SQRT,
     "why": "(-(1 + sqrt x), non-strict) + (sqrt x, non-strict) = -1 < 0"},
    {"id": "sqrt_fact_atom_by_normal_form",
     "key": ("1 + sqrt(t^2) # 0", "[0, 2]"),
     "certificate": _farkas({GOAL: "1", SQRT("t^2"): "1"}, ">"),
     "tag": T_LINEAR_SQRT,
     "why": "the atom sqrt(t^2) is matched by ring_nf of its argument"},
]

# Three existing seams whose code int_subst also runs, re-traced on the new
# proofs (E44). The other P1 seams do not run against INT_SUBST_PROOFS.
INT_SUBST_SEAMS = {
    # the sheet's installation loses x >= 0 @ [0, pi^2/4] and, with no key
    # using the old range, its orientation; s1 loses t^2 >= 0 @ [0, pi/2]
    # but keeps 0 <= pi/2 (step 8 owes it for the premises). All were
    # discharged, so N does not move.
    "no_sqrt_former": {
        "admissions": {"P1.1-sheet": 5},
        "caught_by": [("P1.1-sheet", "goal", "x >= 0", "[0, pi^2/4]"),
                      ("P1.1-sheet", "goal", "0 <= pi^2/4", "true"),
                      ("P1.1-sheet", "s1", "t^2 >= 0", "[0, pi/2]"),
                      ("S0", "SUB1", "goal", "1 - x >= 0", "[0, 1]"),
                      ("S0", "SUB1", "s1", "1 - (1 - t^2) >= 0", "[0, 1]")]},
    # without pi_pos the search has no certificate for 0 <= pi/2 nor for
    # its negation: admitted ('none', ()), REASON_NONE, wherever emitted
    "pi_pos_not_in_constraint_set": {
        # E46: [0, pi/2] is not literal, so s1 must decide the new range's
        # order; without pi's sign neither 0 <= pi/2 nor pi/2 <= 0 is
        # proved, and s1 is refused int-subst-orientation-undecided rather
        # than admitting 0 <= pi/2 (DATA_CHANGES, adjudicated)
        "caught_by": [("P1.1-sheet", "s1", "refused")]},
    # deriv's APP_RULES seam, reached through int_subst's step 10
    "d_ln_emits_nothing": {
        "admissions": {"P1.1-sheet": 5},
        "caught_by": [("INT_SUBST_ACCEPTS", "ln_endpoints_by_exact_values",
                       "t > 0", "[1, e_const]", "sources")]},
}

INT_SUBST_SWITCH = (
    "One commit, the suite green before and after. Kernel: int_subst in "
    "kernel.py as INT_SUBST_RULE states it, both modes, the selector and "
    "the flip; step()'s move list five long, its StepRecord carrying "
    "deriv's trace and output as ftc's does; loader.py's shape check "
    "learns both key sets and 'occurrence'. entries.py gains "
    "SQRT_NONNEG_ENTRY after cos_zero; discharge.py's Farkas checker, "
    "search.py and tagger.py read SQRT_FACT_RULE's label (the owner's "
    "answer 5, E49). Data merged by the suite, not by editing the tables "
    "above: REFUSAL_CODES_INT_SUBST into the refusal-code coverage check "
    "(each code is reached by an INT_SUBST_BAD_MOVES or stage-0 case), "
    "SOURCES_INT_SUBST into SOURCES, DISCHARGE_METHODS_INT_SUBST into "
    "DISCHARGE_METHODS, and any suite count of ENTRIES from 16 to 17.",

    "Suite: a new item asserts INT_SUBST_PROOFS as items 1-2 assert "
    "PROOFS (goal_after trees, per-step INT_SUBST_OBLIGATIONS with "
    "sources, status, tag, new, reason and certificate against "
    "INT_SUBST_EXPECTED, deriv against INT_SUBST_DERIV, the final "
    "tracker, N, the verdict, the theorem, no admission tagged none, and "
    "a math-module check of INT_SUBST_NUMERIC); every INT_SUBST_ACCEPTS "
    "case with its continuation, its certificates and its reasons (two "
    "admissions tagged none in cos_theta_canonical are expected, outside "
    "the no-none check, as OCCURRENCE_CASE's is); every "
    "INT_SUBST_BAD_MOVES case by code, by message filled from its "
    "template, and by residual under `compare`; SQRT_FACT_MUST_REJECT and "
    "SQRT_FACT_CHECKER_ACCEPTS through test_discharge.py, and a sqrt "
    "family in DISCHARGE_PROPERTY_TEST's Farkas generator (keys holding "
    "sqrt of a linear polynomial, sampled at points where it is a rational "
    "square, the rest skipped and counted) so that sqrt_fact_strict is "
    "caught by PROPERTY; INT_SUBST_PLANTED_BUGS and INT_SUBST_SEAMS in "
    "child processes by the existing mechanism; and problems/stage0's "
    "section 12 under item 7's machinery with its own floor (stage1/ holds "
    "exactly the files INT_SUBST_PROOF_FILES names).",

    "Unchanged: PROOFS, ROUTE, FALLBACKS, PLANTED_BUGS, "
    "DEFINEDNESS_MUTATIONS and every DISCHARGE_* table (SQRT_FACT_CHANGES: "
    "no existing expectation moves); no existing child runs P1.1-sheet. "
    "By the owner's answer (E47), P1.1-sheet joins PROOFS and "
    "ROUTE['P1.1'] in a follow-up after the build, with the existing "
    "seams re-traced against it then.",
)

# The data cross-checks itself when imported, as section 11 does.
for _p, _rows in INT_SUBST_FINAL_TRACKER.items():
    _keys = [(r[0], r[1]) for r in _rows]
    assert len(set(_keys)) == len(_keys), _p
    _steps = INT_SUBST_OBLIGATIONS[_p]
    assert [s["id"] for s in INT_SUBST_PROOFS[_p]["steps"]] == \
        [k for k in _steps if k != "goal"], _p
    _seen = set()
    for _sid, _obs in _steps.items():
        for _ob in _obs:
            _fin = [r for r in _rows if (r[0], r[1]) == (_ob[0], _ob[1])]
            assert _fin and _fin[0][2] == _ob[3] and _fin[0][3] == _ob[4], \
                (_p, _sid, _ob)
            assert _ob[5] == ((_ob[0], _ob[1]) not in _seen), (_p, _sid, _ob)
        _seen |= {(o[0], o[1]) for o in _obs}
    assert _seen == set(_keys), _p
    assert sum(r[2] == ADMITTED for r in _rows) == INT_SUBST_ADMISSIONS[_p]
    assert all(r[3] == T_REG for r in _rows if r[2] == ADMITTED), _p
    for (_k, (_tag, _cert)) in INT_SUBST_EXPECTED[_p].items():
        _r = [r for r in _rows if (r[0], r[1]) == _k]
        assert _r and _r[0][2] == DISCHARGED and _r[0][3] == _tag, (_p, _k)
# P1.1-sheet's installation is the fallback's, after discharge
assert INT_SUBST_OBLIGATIONS["P1.1-sheet"]["goal"] == \
    DISCHARGE_OBLIGATIONS["P1.1-fallback"]["goal"]
assert set(REFUSAL_CODES_INT_SUBST) <= {
    c["refusal"] for c in INT_SUBST_BAD_MOVES}
del _p, _rows, _keys, _steps, _seen, _sid, _obs, _ob, _fin, _k, _tag, _cert, _r


# ---------------------------------------------------------------------------
# 12b. The int_subst review (int_subst review 2026-09-24)
#
# The skeptic of the int_subst build (ed40695) found no false int_subst
# step, but found that F3 never tries a root of a key's own polynomial (E50),
# and three rules no case isolates (three mutations that passed the whole
# suite). Written as a spec before any code, as section 11 and 12 were:
# the tables below are STAGED, and each says the table it joins when the
# build lands (REVIEW_SWITCH), so the committed suite stays green meanwhile.
# Every outcome was derived by hand from INT_SUBST_RULE, DISCHARGE_RULE and
# the amended COUNTERPOINT_CANDIDATES, and checked with SymPy (VERIFIED,
# last entry).

ROOT_TEST_BOUND = 10 ** 6  # E50: as the tagger's rational root factoriser

# E50's cases. Refusals are in BAD_MOVES' shape; the undecided one in
# DISCHARGE_UNDECIDED's. For each, the candidate walk for the key's one
# variable is written out: (1) the domain's rational bounds, (2) the
# midpoint, (3) 0, 1, -1, (4) the new roots.
F3_ROOTS_CASES = [
    # The skeptic's reproducer. It now stops at its first step: int_subst's
    # step 9 charges sub's former 2*t - 5 # 0 on [0, 4] (E25: nonzero),
    # which no method closes (2*t - 5 changes sign; E18's content split
    # leaves t - 5/2 # 0, itself none), and F3 walks t = 0, 4, 2, 1 (all
    # true), -1 (outside [0, 4]), then the root 5/2 of the target 2*t - 5.
    # The installation's keys (x^2 + 1 # 0 by sign, 5/3's 3 # 0) hold.
    {"id": "f3_root_int_subst_pole",
     "goal": "Int[x = -1 .. 5/3] 1/(x^2 + 1) == ?A", "setup": [],
     "move": ("int_subst", {"var": "x", "sub": "5/(2*t - 5)", "new_var": "t",
                            "lo": "0", "hi": "4", "check": "field",
                            "facts": []}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("2*t - 5 # 0 @ [0, 4]", "2*(5/2) - 5 # 0", t="5/2"),
     "was": "accepted, and the skeptic's continuation (ftc F := "
            "-atan((2*t - 5)/5), atan_odd, close -atan(3/5) - atan 1) "
            "reported 'Proved modulo 9 admissions' for a false value",
     "why": "phi = 5/(2t - 5) has a pole at t = 5/2 inside [0, 4], so it is "
            "not C^1 there and the substitution is invalid: the integral "
            "is atan(5/3) + pi/4 = 1.8158..., the reported value "
            "-atan(3/5) - pi/4 = -1.3258... (SymPy). Both ends map "
            "(5/(2*0 - 5) = -1, 5/(2*4 - 5) = 5/3), so only the former "
            "stood between the move and the false theorem"},
    # The same defect with ftc alone: F's former x - 5/2 # 0 on [0, 4],
    # emitted at ftc's (ii) before anything else it emits (the range is
    # literal, so there is no orientation first). Walk: 0, 4, 2, 1, -1,
    # then the root 5/2.
    {"id": "f3_root_ftc_antiderivative_pole",
     "goal": "Int[x = 0 .. 4] -1/(1 + (x - 5/2)^2) == ?A", "setup": [],
     "move": ("ftc", {"F": "atan(1/(x - 5/2))", "check": "field",
                      "facts": []}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("x - 5/2 # 0 @ [0, 4]", "5/2 - 5/2 # 0", x="5/2"),
     "was": "accepted, the goal becoming atan(1/(4 - 5/2)) - atan(1/(0 - "
            "5/2)) == ?A, which closes to the false atan(2/3) + atan(2/5)",
     "why": "F = atan(1/(x - 5/2)) has F' = the integrand except at 5/2, "
            "where F jumps by pi; the true value is -(atan(3/2) + "
            "atan(5/2)) = -2.1730..., the ftc value 0.9685... (SymPy). "
            "The integrand itself is continuous, so installation owes "
            "nothing false; the pole is F's"},
    # A root on the closed range, at installation. Walk: 0, 3, 3/2, 1, -1,
    # then the root 2.
    {"id": "f3_root_closed_range",
     "goal": "Int[t = 0 .. 3] 1/(t - 2) == ?A", "setup": [],
     "move": ("install", {}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("t - 2 # 0 @ [0, 3]", "2 - 2 # 0", t="2"),
     "was": "installed, t - 2 # 0 @ [0, 3] admitted tagged none",
     "why": "the FTC-across-a-pole trap with the pole at an interior "
            "rational point that is neither an end nor the midpoint"},
]
# The undecided twin: an irrational pole stays admitted none.
F3_ROOTS_UNDECIDED = [
    {"id": "f3_irrational_pole_undecided",
     "goal": "Int[t = 0 .. 2] 1/(t^2 - 2) == ?A",
     "goal_emits": [
         ("t^2 - 2 # 0", "[0, 2]", (S_FORMER,), ADMITTED, T_NONE, True)],
     "reasons": {("t^2 - 2 # 0", "[0, 2]"): REASON_NONE},
     "why": "false at t = sqrt 2, which is irrational: the rational root "
            "test on t^2 - 2 tries 1, -1, 2, -2, none a root, and the walk "
            "0, 2, 1, -1 finds t^2 - 2 # 0 true at each point in [0, 2]. "
            "No method closes it (t^2 opaque to FM, no sign form, no "
            "rational factor). E50's stated limit; Sturm sequences would "
            "decide it (DESIGN_DEFECTS)"},
]

# What E50 changes in the expectations already in this file, applied in the
# build commit with the code (REVIEW_SWITCH). The roots come after every
# existing candidate, so a key refused before is refused at the same first
# point with the same message; a key discharged before is unchanged
# (discharge runs before refutation). Only a false key with no refuting
# point among the old candidates can change, and every such key in both data
# files was re-traced:
F3_ROOTS_CHANGES = {
    "DISCHARGE_UNDECIDED_remove": ("undecided_false_unbounded_candidates",),
    # x - 5 # 0 @ [0, oo): walk 0, 1, -1 (outside), then the root 5
    "DISCHARGE_BAD_MOVES_ADDED_add": [
        {"id": "decided_false_root_on_unbounded_range",
         "goal": "Int[x = 0 .. oo] 1/(x - 5) == ?A",
         "setup": [], "move": ("install", {}),
         "refusal": OBLIGATION_DECIDED_FALSE,
         "message": _point("x - 5 # 0 @ [0, oo)", "5 - 5 # 0", x="5"),
         "why": "E50: was DISCHARGE_UNDECIDED's "
                "undecided_false_unbounded_candidates, the false key the "
                "bounded search missed; 5 is the root of its target"}],
    # the false-but-undecided example becomes the irrational pole
    "DISCHARGE_UNDECIDED_add": ["F3_ROOTS_UNDECIDED f3_irrational_pole_undecided"],
    "unchanged, re-traced": (
        "cos 1 # 0 (DISCHARGE_UNDECIDED): closed, so F3 does not apply",
        "(x + pi)/(x + pi) - 1 # 0 @ [1, 2] (DISCHARGE_BAD_MOVES_ADDED "
        "field_zero_divisor_opaque): its target holds pi and inv(x + pi), "
        "so no piece is a polynomial in x alone",
        "x <= 5 @ [0, oo) (DISCHARGE_MUST_REJECT farkas_infinite_end, "
        "if_emitted admitted none): the root 5 of 5 - x reads 5 <= 5, true "
        "(a non-strict target is not falsified at its own root); 6 is "
        "still no candidate",
        "1 - x^2 >= 0 @ [0, 1] and 1 - (cos theta)^2 >= 0 @ [0, pi/2] "
        "(INT_SUBST_ACCEPTS cos_theta_canonical): the first is true, its "
        "roots 1 and -1 are already candidates; the second holds an atom",
        "0 <= pi/2 and pi/2 >= 0 under pi_pos_not_in_constraint_set: "
        "closed",
        "every refusal message in either file (DISCHARGE_*, "
        "INT_SUBST_BAD_MOVES, stage 0's S2-SUB-W1, the planted-bug and "
        "mutation refusals): each key is univariate or, for x < z @ x < y, "
        "w < z, has no univariate piece, and its first refuting point "
        "precedes any root, so no message changes",
        "every key the pre-discharge tables list: no longer asserted",
    ),
    "prose": ("DESIGN_DEFECTS' §5.4 entry and DISCHARGE_UNDECIDED's "
              "comment use x - 5 # 0 @ [0, oo) as the false-but-undecided "
              "example; after the build it is t^2 - 2 # 0 @ [0, 2]"),
}

# The skeptic's three test gaps: behaviour already built, which no case
# isolated, each shown by a mutation that passed all 565 checks
# (m_no_sub_formers, m_reverse_no_old_orient, m_sqrt_fact_any_u). They
# join INT_SUBST_ACCEPTS, INT_SUBST_BAD_MOVES and SQRT_FACT_MUST_REJECT.
REVIEW_ACCEPTS = [
    # the body does not mention x, so step 14 charges no former of phi,
    # and t > 0 @ [1, e_const]'s 'former' source comes from step 9 alone
    # (d_ln's side condition is the same key, with its own source)
    {"id": "forward_constant_body_partial_phi",
     "goal": "Int[x = 0 .. 1] 1 == ?A",
     "goal_emits": [],
     "move": ("int_subst", {"var": "x", "sub": "ln t", "new_var": "t",
                            "lo": "1", "hi": "e_const", "check": "ring",
                            "facts": []}),
     "goal_after": "Int[t = 1 .. e_const] 1*(1/t) == ?A",
     "deriv": {"var": "t", "F": "ln t",
               "trace": [("d_ln", "ln t", ("t > 0 @ [1, e_const]",)),
                         ("d_var", "t", ())],
               "output": "1/t", "emits": ("t > 0 @ [1, e_const]",)},
     "emits": [
         ("1 <= e_const", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_E, True),
         ("t > 0", "[1, e_const]", (S_FORMER, S_D_LN), DISCHARGED, T_RANGE,
          True),
         ("ln 1 == 0", "true", (S_SUBST_LO,), DISCHARGED, T_RING_LN_ONE,
          True),
         ("ln e_const == 1", "true", (S_SUBST_HI,), DISCHARGED, T_RING_LN_E,
          True),
         ("ln t in C^1([1, e_const])", "[1, e_const]", (S_SUBST_C1,),
          ADMITTED, T_REG, True),
         # F = 1 has no free variable, so the interval is named (D13)
         ("1 in C^0(t in [1, e_const])", "t in [1, e_const]", (S_SUBST_C0,),
          ADMITTED, T_REG, True),
         ("t # 0", "[1, e_const]", (S_FORMER,), DISCHARGED, T_RANGE, True)],
     "certificates": {
         ("1 <= e_const", "true"): _farkas({GOAL: "1",
                                            FACT("e_gt_one"): "1"}),
         ("t > 0", "[1, e_const]"): _RANGE_LO,
         ("t # 0", "[1, e_const]"): _RANGE_LO_NZ},
     "why": "pins INT_SUBST_RULE step 9 by its source: with it skipped the "
            "key is still emitted, by d_ln, and ln_endpoints_by_exact_values "
            "and phi_undefined_on_new_range keep their outcome, because the "
            "first recharges ln t in step 14 and the second is refused by "
            "d_ln's key. Int_0^1 1 = 1 = Int_1^e 1/t (SymPy)"},
    # reverse mode owes the old range's orientation when it is symbolic
    {"id": "reverse_symbolic_old_range_oriented",
     "goal": "Int[x = 0 .. pi/2] 2*x == ?A",
     "goal_emits": [("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
                     True)],
     "move": ("int_subst", {"mode": "reverse", "var": "x", "sub": "x^2",
                            "new_var": "u", "lo": "0", "hi": "pi^2/4",
                            "f": "1", "check": "ring", "facts": []}),
     "goal_after": "Int[u = 0 .. pi^2/4] 1 == ?A",
     "deriv": {"var": "x", "F": "x^2",
               "trace": [("d_pow_int", "x^2", ()), ("d_var", "x", ())],
               "output": "2*x^1*1", "emits": ()},
     "emits": [
         # step 8, reverse: I = [0, pi/2] owes its order (the premises use I)
         ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI, True),
         # hi's pi^2/4, then the new range's order, decided by sign (E46)
         ("4 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("0 <= pi^2/4", "true", (S_ORIENT,), DISCHARGED, T_SIGN, True),
         ("2*x == 1*(2*x^1*1)", "[0, pi/2]", (S_SUBST_INT,), DISCHARGED,
          T_DERIV_RING, True),
         ("0^2 == 0", "true", (S_SUBST_LO,), DISCHARGED, T_RING, True),
         ("(pi/2)^2 == pi^2/4", "true", (S_SUBST_HI,), DISCHARGED, T_RING,
          True),
         ("x^2 in C^1([0, pi/2])", "[0, pi/2]", (S_SUBST_C1,), ADMITTED,
          T_REG, True),
         ("1 in C^0(x in [0, pi/2])", "x in [0, pi/2]", (S_SUBST_C0,),
          ADMITTED, T_REG, True)],
     "certificates": {("0 <= pi/2", "true"): _PI_HALF,
                      ("0 <= pi^2/4", "true"): _PI_SQ},
     "why": "pins step 8's reverse-mode orientation of the old range, "
            "which no case with literal old limits reaches. Int_0^{pi/2} "
            "2x = pi^2/4 = Int_0^{pi^2/4} 1 (SymPy)"},
]
REVIEW_BAD_MOVES = [
    {"id": "reverse_symbolic_old_range_reversed",
     "goal": "Int[x = pi/2 .. 0] 2*x == ?A", "setup": [],
     "move": ("int_subst", {"mode": "reverse", "var": "x", "sub": "x^2",
                            "new_var": "u", "lo": "pi^2/4", "hi": "0",
                            "f": "1", "check": "ring", "facts": []}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _negation("pi/2 <= 0", "pi/2 > 0", T_LINEAR_PI),
     "why": "step 8, reverse: the old range [pi/2, 0] owes pi/2 <= 0, and "
            "F2 decides it false, as for ftc on the same goal (E4). The "
            "goal installs, since 2*x owes nothing and no key uses the "
            "range. The substitution itself is valid (Int_{pi/2}^0 2x = "
            "-pi^2/4 = Int_{pi^2/4}^0 1, SymPy): E46 flips only the NEW "
            "range, and a goal whose own integral is reversed with symbolic "
            "limits cannot be used by any move that reads its range"},
]
REVIEW_SQRT_FACT_MUST_REJECT = [
    {"id": "sqrt_fact_label_for_absent_atom",
     "key": ("1 + sqrt x # 0", "[0, 4]"),
     "certificate": _farkas({GOAL: "1", SQRT("x"): "1", SQRT("x + 1"): "1"},
                            ">"),
     "expected": "rejected",
     "rejects_because": "sqrt(x + 1) occurs nowhere in the key, so its "
                        "label is not in the constraint set (the checker's "
                        "'unknown-label'), although the key does hold the "
                        "atom sqrt x",
     "truth": ("true",),
     "if_emitted": ("discharged", T_LINEAR_SQRT),
     "why": "isolates SQRT_FACT_RULE's membership test: sqrt_fact_absent_atom's "
            "key holds no sqrt atom at all, so a check that accepts any "
            "label once some sqrt atom is present passes it. The test is "
            "defensive: an absent atom's constraint can never cancel, so "
            "without it this certificate is still rejected, but by the "
            "combination rule, and the reason code shows which rule acted"},
]

# Planted bugs for the build, as INT_SUBST_PLANTED_BUGS' shape.
REVIEW_PLANTED_BUGS = {
    "f3_no_root_candidates": {
        "mutation": "COUNTERPOINT_CANDIDATES' (4) is not walked",
        "caught_by": [("F3_ROOTS_CASES", "f3_root_int_subst_pole"),
                      ("F3_ROOTS_CASES", "f3_root_ftc_antiderivative_pole"),
                      ("F3_ROOTS_CASES", "f3_root_closed_range"),
                      ("DISCHARGE_BAD_MOVES_ADDED",
                       "decided_false_root_on_unbounded_range")]},
    "int_subst_no_sub_formers": {
        "mutation": "INT_SUBST_RULE step 9 charges nothing (the skeptic's "
                    "m_no_sub_formers)",
        "caught_by": [("INT_SUBST_ACCEPTS", "forward_constant_body_partial_phi",
                       "t > 0", "[1, e_const]", "sources")]},
    "int_subst_reverse_no_old_orient": {
        "mutation": "step 8 does not owe the old range's order in reverse "
                    "mode (the skeptic's m_reverse_no_old_orient)",
        "caught_by": [("INT_SUBST_ACCEPTS", "reverse_symbolic_old_range_oriented"),
                      ("INT_SUBST_BAD_MOVES",
                       "reverse_symbolic_old_range_reversed")]},
    "sqrt_fact_any_u": {
        "mutation": "a sqrt label is accepted for any u once the key holds "
                    "some sqrt atom (the skeptic's m_sqrt_fact_any_u)",
        "caught_by": [("SQRT_FACT_MUST_REJECT",
                       "sqrt_fact_label_for_absent_atom")]},
}

REVIEW_SWITCH = (
    "One commit, with the code: the F3 search (refute.py, untrusted) walks "
    "COUNTERPOINT_CANDIDATES (4) with ROOT_TEST_BOUND; the suite asserts "
    "F3_ROOTS_CASES beside DISCHARGE_BAD_MOVES_ADDED and F3_ROOTS_UNDECIDED "
    "beside DISCHARGE_UNDECIDED, applies F3_ROOTS_CHANGES to those two "
    "tables, and gains REVIEW_PLANTED_BUGS' f3_no_root_candidates; "
    "DISCHARGE_PROPERTY_TEST's refutation re-check covers the new "
    "refusals as it covers every F3 refusal, and its generator gains "
    "univariate # 0 keys with a rational root inside the range.",
    "The three gap cases need no code: REVIEW_ACCEPTS joins "
    "INT_SUBST_ACCEPTS, REVIEW_BAD_MOVES joins INT_SUBST_BAD_MOVES, and "
    "REVIEW_SQRT_FACT_MUST_REJECT joins SQRT_FACT_MUST_REJECT (its reason "
    "code 'unknown-label' in test_discharge.py's map), with the other "
    "three REVIEW_PLANTED_BUGS as child-process mutations. They may land "
    "in the same commit or before it.",
)


# ---------------------------------------------------------------------------
# 13. Consolidation, specified before any code (consolidation spec
#     2026-09-24)
#
# WHAT.md "Start here" item 1: int_flip (the owner's decision), P1.1-sheet
# joining PROOFS (E47's follow-up), the sign product on non-strict goals,
# and the entries that let Int_0^1 sqrt(1 - x^2) finish by x := cos theta
# (problems/stage0 section 13, QC1). DECISIONS E51-E55 give the design in
# brief; the rule texts below state it in full. Written from DESIGN.md
# revision 10, ARCHITECTURE.md and the data files, without reading
# kernel.py, discharge.py or search.py to shape any list. Everything is
# STAGED: nothing here is asserted until the build (CONSOLIDATION_SWITCH),
# and the changes to asserted tables are listed, with their new values, in
# P1_1_SHEET_JOIN and CONSOLIDATION_CHANGES.

# --- 13a. int_flip (E51) ----------------------------------------------------

INT_FLIP_MOVE = "int_flip"
INT_FLIP_ARGS = ()                  # no required key
INT_FLIP_OPTIONAL = ("occurrence",)

REFUSAL_CODES_INT_FLIP = {
    "int-flip-no-integral": "E51: the goal holds no Int, or none at the "
                            "given occurrence",
    "int-flip-ambiguous": "E51: no occurrence is given and the goal holds "
                          "two or more Ints",
}
INT_FLIP_MESSAGES = {
    "int-flip-no-integral": "the goal holds no integral",
    "int-flip-no-integral/occurrence": "the goal holds no integral at "
                                       "occurrence {occurrence}",
    "int-flip-ambiguous": "{n} integrals in the goal; give an occurrence",
}

INT_FLIP_RULE = (
    "The rule (§5.1, the definition of a reversed integral, with "
    "pointwise linearity): Int[x = a .. b] f == Int[x = b .. a] -(f), for "
    "every a and b. It is the identity E46 already composes into "
    "int_subst's flipped form, so the rule table gains a move and no new "
    "theorem. It holds whatever the order of a and b, so the step owes no "
    "orientation of its own and has no premise (E51).",

    "1. The common step() checks; args has no key but an optional "
    "'occurrence' (an int >= 0, not a bool), else 'bad-args'.",

    "2. Selection, as int_subst's (E48) without a variable: with "
    "occurrence k, the k-th Integral node of the goal's non-?A side (both "
    "sides, lhs first, when there is no ?A) in REWRITE_RULE's pre-order, "
    "else 'int-flip-no-integral' ('/occurrence'); with none, the side "
    "must hold exactly one Integral node, else 'int-flip-no-integral' "
    "(none) or 'int-flip-ambiguous' (two or more). P is the position "
    "domain (REWRITE_RULE step 7).",

    "3. Under D[y]: if the selected Int lies below a D[y] and y occurs free "
    "in its limits or body, or in a limit of an Int between the D[y] and "
    "the position, the step is refused "
    "'rewrite-under-D-needs-open-domain' (E48's test, for the keys step 4 "
    "may charge on the new closed range).",

    "4. The new Int, Integral(x, b, a, Neg(f)), replaces the selected one "
    "at its position. Its formers are charged as a new term's are: its "
    "limits at P, its body at P plus its own E4 range, with that range's "
    "orientation b <= a when a key uses it and the ends are not two "
    "literals, decided by E56 (owner's answers): the order discharge "
    "proves builds the range, so flipping an oriented symbolic integral "
    "whose body owes a former is accepted (INT_FLIP_ACCEPTS "
    "flip_oriented_symbolic_with_former). Then "
    "check_goal. Nothing else is emitted; a refused step changes nothing "
    "(E13).",
)

# The full proof the owner asked for: a goal with reversed symbolic limits,
# flipped so ftc runs. Installation: pi/2 owes 2 # 0; 2*x owes nothing, so
# no key uses the reversed range and nothing false is owed (E4).
INT_FLIP_ACCEPTS = [
    {"id": "flip_reversed_symbolic_to_value",
     "goal": "Int[x = pi/2 .. 0] 2*x == ?A",
     "goal_emits": [("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
                     True)],
     "move": ("int_flip", {}),
     "goal_after": "Int[x = 0 .. pi/2] -(2*x) == ?A",
     # the new limits' pi/2 again; -(2*x) owes nothing, so no key uses
     # [0, pi/2] and no orientation is owed here
     "emits": [("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False)],
     "then": [
         {"move": ("ftc", {"F": "-x^2", "check": "ring", "facts": []}),
          "goal_after": "-(pi/2)^2 - (-0^2) == ?A",
          "deriv": {"var": "x", "F": "-x^2",
                    "trace": [("route_neg", "-x^2", ()),
                              ("d_mul", "-1*x^2", ()), ("d_const", "-1", ()),
                              ("d_pow_int", "x^2", ()), ("d_var", "x", ())],
                    "output": "0*x^2 + (-1)*(2*x^1*1)", "emits": ()},
          "emits": [
              ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI,
               True),
              ("-x^2 in C^0([0, pi/2])", "[0, pi/2]", (S_FTC_C0F,), ADMITTED,
               T_REG, True),
              ("-x^2 in C^1((0, pi/2))", "(0, pi/2)", (S_FTC_C1F,), ADMITTED,
               T_REG, True),
              ("D[x](-x^2) == -(2*x)", "(0, pi/2)", (S_FTC_D,), DISCHARGED,
               T_DERIV_RING, True),
              ("-(2*x) in C^0([0, pi/2])", "[0, pi/2]", (S_FTC_C0f,),
               ADMITTED, T_REG, True),
              ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False)],
          "certificates": {("0 <= pi/2", "true"): _PI_HALF}},
         {"move": ("close", {"value": "-pi^2/4", "check": "ring",
                             "facts": []}),
          "goal_after": None,
          "emits": [("4 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
                     True)]},
     ],
     "report": VERDICT.format(n=3),
     "theorem": "Int[x = pi/2 .. 0] 2*x == -pi^2/4",
     "why": "after the flip ftc's range is [0, pi/2]. Int_{pi/2}^0 2x = "
            "-pi^2/4 (SymPy); -(pi/2)^2 - (-0^2) is -pi^2/4 by ring. (Owner's "
            "answers, E56: ftc now reaches the same value without the flip, "
            "E56_ACCEPTS reversed_symbolic_by_ftc_linear; the flip stays a "
            "move of its own)"},
    {"id": "flip_sum_second_occurrence",
     "goal": "(Int[x = 0 .. 1] 2*x) + (Int[x = pi/2 .. 0] 2*x) == ?A",
     "goal_emits": [("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
                     True)],
     "move": ("int_flip", {"occurrence": 1}),
     "goal_after": "(Int[x = 0 .. 1] 2*x) + (Int[x = 0 .. pi/2] -(2*x))"
                   " == ?A",
     "emits": [("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False)],
     "why": "E51's selector: the second Int in pre-order; the first is "
            "untouched"},
    # owner's answers (E56): was INT_FLIP_BAD_MOVES, refused by F2 on
    # pi/2 <= 0. The new range pi/2 .. 0 is built from the proved order
    # 0 <= pi/2, [0, pi/2], so sqrt x's former is installation's key again
    {"id": "flip_oriented_symbolic_with_former",
     "goal": "Int[x = 0 .. pi/2] sqrt x == ?A",
     "goal_emits": [
         ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("x >= 0", "[0, pi/2]", (S_FORMER,), DISCHARGED, T_RANGE, True),
         ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI, True)],
     "move": ("int_flip", {}),
     "goal_after": "Int[x = pi/2 .. 0] -(sqrt x) == ?A",
     "emits": [
         ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False),
         ("x >= 0", "[0, pi/2]", (S_FORMER,), DISCHARGED, T_RANGE, False),
         ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI, False)],
     "certificates": {("x >= 0", "[0, pi/2]"): _RANGE_LO,
                      ("0 <= pi/2", "true"): _PI_HALF},
     "why": "E56: the reversed symbolic range is usable, since its order "
            "0 <= pi/2 is proved; nothing new is owed"},
]
INT_FLIP_BAD_MOVES = [
    {"id": "flip_no_integral",
     "goal": "sin 1 + 1 == ?A", "setup": [], "move": ("int_flip", {}),
     "refusal": "int-flip-no-integral",
     "message": ("int-flip-no-integral", {})},
    {"id": "flip_ambiguous",
     "goal": "(Int[x = 0 .. 1] 2*x) + (Int[x = pi/2 .. 0] 2*x) == ?A",
     "setup": [], "move": ("int_flip", {}),
     "refusal": "int-flip-ambiguous",
     "message": ("int-flip-ambiguous", {"n": "2"})},
    {"id": "flip_occurrence_out_of_range",
     "goal": "(Int[x = 0 .. 1] 2*x) + (Int[x = pi/2 .. 0] 2*x) == ?A",
     "setup": [], "move": ("int_flip", {"occurrence": 2}),
     "refusal": "int-flip-no-integral",
     "message": ("int-flip-no-integral/occurrence", {"occurrence": "2"})},
    {"id": "flip_under_D",
     "goal": "D[y](Int[x = 0 .. y] x) == ?A @ 0 <= y", "setup": [],
     "move": ("int_flip", {}),
     "refusal": "rewrite-under-D-needs-open-domain",
     "why": "y is a limit of the Int below D[y]: the new range [y, 0] is "
            "closed in y (§6.1 rev 9, E11, E48)"},
    {"id": "flip_extra_arg",
     "goal": "Int[x = pi/2 .. 0] 2*x == ?A", "setup": [],
     "move": ("int_flip", {"var": "x"}),
     "refusal": "bad-args"},
]

# --- 13b. P1.1-sheet joins PROOFS (E52) -------------------------------------
#
# The re-trace of every child that runs PROOFS against P1.1-sheet, by hand.
# 'N' is its admission count under the mutation (None: the proof is
# refused, and left out of admissions, as the data writes a refused proof);
# 'add' are the caught_by locations it adds (none needed where N and the
# lists are unchanged). P1.1-sheet runs after P1.1 in PROOFS' order.
_SHEET = "P1.1-sheet"
P1_1_SHEET_TRACES = {
    # PLANTED_BUGS, as DISCHARGE_PLANTED_BUGS re-traces them
    "d_ln_emits_nothing": {"N": 5, "add": []},       # no ln
    "ftc_derivative_premise_on_closed": {
        "N": 5,
        # ftc's premise moves to [0, pi/2]; F's deriv emits nothing and
        # ring's check nothing, and int_subst does not call the seam
        "add": [(_SHEET, "s3", "D[t](2*sin t - 2*t*cos t) == "
                 "sin t * (2*t^1*1)", "(0, pi/2)")]},
    "tracker_drops_one": {
        "N": 5,  # the dropped t >= 0 @ [0, pi/2] (s2) is discharged
        "add": [("FINAL_TRACKER", _SHEET, ("t >= 0", "[0, pi/2]"))]},
    # the single drop of 0 <= pi/2 is spent in P1.1's installation, which
    # runs first in the same child
    "tracker_drops_reemitted": {"N": 5, "add": []},
    # owner's answers, correcting this spec: with E53 built, 0 <= pi/2
    # (pi/2 = (1/2)*pi) is discharged by the sign product's content split,
    # its factor pi > 0 by cite pi_pos (ENTRIES, which the seam leaves), so
    # s1 decides its order and nothing is admitted; the key is retagged
    "pi_pos_not_in_constraint_set": {
        "N": 5,
        "add": [(_SHEET, "s1", "0 <= pi/2", "tag"),
                (_SHEET, "s2", "0 <= pi/2", "tag"),
                (_SHEET, "s3", "0 <= pi/2", "tag")],
        "retagged": [("0 <= pi/2", "true", DISCHARGED,
                      ("sign product", ("pi_pos",)))]},
    # DISCHARGE_NEW_PLANTED_BUGS
    "farkas_ignores_strictness": {"N": 5, "add": []},
    "farkas_allows_negative_multiplier": {"N": 5, "add": []},
    # x >= 0 @ [0, pi^2/4] and t >= 0 @ [0, pi/2] lose their lower-end
    # certificates (the swapped label gives v - hi, not a constant with
    # pi): admitted REASON_REJECTED, tag range; F3 finds no point (0 holds,
    # 1 is not shown inside, -1 is outside)
    "farkas_swaps_interval_ends": {
        "N": 7,
        "add": [("N", _SHEET), (_SHEET, "goal", "x >= 0", "status"),
                (_SHEET, "s2", "t >= 0", "status")]},
    "farkas_closed_as_open": {"N": 5, "add": []},
    "farkas_any_fact": {"N": 5, "add": []},
    "farkas_no_goal_needed": {"N": 5, "add": []},
    "sign_skips_ring": {"N": 5, "add": []},
    "sign_zero_constant_strict": {"N": 5, "add": []},
    "sign_any_exponent": {"N": 5, "add": []},
    "product_skips_parity": {"N": 5, "add": []},   # no product in the sheet
    "product_skips_children": {"N": 5, "add": []},
    "cite_skips_hypotheses": {"N": 5, "add": []},  # no cite in the sheet
    # 0 <= pi/2's certificate is halved and rejected, so s1 decides no order
    "search_scales_wrongly": {
        "N": None, "add": [(_SHEET, "s1", "refused")],
        # E56's one code (owner's answers)
        "refused": ("s1", ("orientation-undecided",
                           {"lo": "0", "hi": "pi/2"}))},
    # DEFINEDNESS_MUTATIONS: every one not named is N 5, no change (the
    # sheet holds no ln, tan, asin, acos, acosh or atanh; no ring, field or
    # norm_num input holds an Int or D node; rewrite's R = t has no former;
    # its limit formers 4 # 0 and 2 # 0 are closed, so their domain is true
    # whatever _encloses says)
    "no_sqrt_former": {
        "N": 5,
        "add": [(_SHEET, "goal", "x >= 0", "[0, pi^2/4]"),
                (_SHEET, "goal", "0 <= pi^2/4", "true"),
                (_SHEET, "s1", "t^2 >= 0", "[0, pi/2]")]},
    # sqrt x owes x > 0 on [0, pi^2/4], false at x = 0
    "sqrt_open_at_0": {"N": None, "add": [(_SHEET, "goal", "refused")]},
}
P1_1_SHEET_JOIN = {
    "PROOFS": INT_SUBST_PROOFS["P1.1-sheet"],
    "ROUTE": {"P1.1": "P1.1-sheet"},       # E47: the sheet's goal is the route
    "ECHO": ECHO["P1.1-fallback"],          # the same goal
    "ANSWERS": "2",
    "NUMERIC": 2.0,
    "DERIV": DERIV["P1.1"],                 # ftc's F (s3); s1's is INT_SUBST_DERIV's
    "DISCHARGE_OBLIGATIONS": INT_SUBST_OBLIGATIONS["P1.1-sheet"],
    "DISCHARGE_FINAL_TRACKER": INT_SUBST_FINAL_TRACKER["P1.1-sheet"],
    "DISCHARGE_EXPECTED": INT_SUBST_EXPECTED["P1.1-sheet"],
    "DISCHARGE_ADMISSIONS": 5,
    # the default N of every planted bug and mutation whose admissions the
    # data does not give (the suite's _D3) gains the sheet at 5
    "default_N": 5,
    "INT_SUBST_PROOFS": "loses 'P1.1-sheet'; the int_subst children run it "
                        "from PROOFS",
    "traces": P1_1_SHEET_TRACES,
}

# --- 13c. The sign product on non-strict goals (E53) -----------------------

T_PRODUCT_COS = ("sign product", ("cos_le_one", "cos_ge_neg_one"))
SIGN_PRODUCT_NONSTRICT_RULE = (
    "Amends DISCHARGE_RULE's 'Sign product certificate' paragraph and "
    "TAG_RULES' 'sign product' paragraph at the build. A non-strict key "
    "(target g >= 0, DISCHARGE_RULE's Targets) is now accepted: a "
    "certificate {'method': 'sign product', 'sense': None, 'content': c, "
    "'factors': ((f1, r1, cert1), ...)} with rj one of '>', '<', '>=', "
    "'<='. The checker checks, beside the existing ring_equal(g, c * f1 * "
    "... * fn) and c != 0: (a) for a strict target every rj is strict "
    "(unchanged); for a non-strict one any of the four; (b) parity: "
    "sign(c) times (-1) to the number of '<' and '<=' factors is +1; (c) "
    "each fj's sub-obligation, fj rj 0 at the key's domain, holds by its "
    "own certificate. A # 0 key is unchanged (every rj '# 0').",

    "Soundness. At a point of the domain where the terms are defined, "
    "each factor has its certified sign, so the product c*f1*...*fn has "
    "sign(c) times the factors' signs: non-negative when (b) holds and at "
    "least one factor may be 0, positive when every factor is strict. "
    "A strict factor is allowed under a non-strict target (it only "
    "strengthens), and a non-strict one is not allowed under a strict "
    "target (a factor that is 0 makes the product 0).",

    "The search. For a non-strict target it tries sign product after "
    "range/linear and sign, as TAG_RULES orders the methods, with the "
    "same untrusted rational root factoriser, each factor normalised to a "
    "positive leading coefficient and the content taking the sign; each "
    "factor's relation is tried strict first ('>' then '<'), then "
    "non-strict ('>=' then '<='), and the first that its own search "
    "certifies is used. 1 - x^2 on [0, 1] factors as -(x - 1)(x + 1): "
    "x - 1 <= 0 (not < 0: it is 0 at 1) by the upper end, x + 1 > 0 by the "
    "lower end, parity (-1)(-1) = +1.",
    "Content split (TAG_RULES (i)) under a non-strict target: a content of "
    "-1 is not split off, because the one factor's goal would restate the "
    "key; the sign is carried by the content in the product certificate "
    "(-(x - 1)(x + 1) for 1 - x^2 >= 0). Strict targets are unchanged. "
    "(Resolved by the consolidation build; recorded by the main session.)",
)
_ONE_MINUS_X2 = _product("-1", [("x - 1", "<=", _farkas({GOAL: "1",
                                                         HI(0): "1"})),
                                ("x + 1", ">", _RANGE_LO)])
SIGN_PRODUCT_CHECKER_ACCEPTS = [
    {"id": "product_nonstrict_search_form",
     "key": ("1 - x^2 >= 0", "[0, 1]"), "certificate": _ONE_MINUS_X2,
     "tag": T_PRODUCT,
     "why": "the search's own: -(x - 1)(x + 1), parity +1"},
    {"id": "product_nonstrict_owner_form",
     "key": ("1 - x^2 >= 0", "[0, 1]"),
     "certificate": _product("1", [("1 - x", ">=", _farkas({GOAL: "1",
                                                           HI(0): "1"})),
                                   ("1 + x", ">", _RANGE_LO)]),
     "tag": T_PRODUCT,
     "why": "(1 - x)(1 + x), each factor >= 0, as WHAT.md writes it"},
]
SIGN_PRODUCT_MUST_REJECT = [
    {"id": "product_nonstrict_factor_changes_sign",
     "key": ("1 - x^2 >= 0", "[0, 2]"),
     "certificate": _product("-1", [("x - 1", "<=", _farkas({GOAL: "1",
                                                            HI(0): "1"})),
                                    ("x + 1", ">", _RANGE_LO)]),
     "expected": "rejected",
     "rejects_because": "x - 1 <= 0 is false on [0, 2]: its certificate "
                        "sums to (x - 1) + (2 - x) = 1 (child-rejected/"
                        "positive-constant)",
     "truth": ("false", {"x": "2"}),
     "if_emitted": ("refused", _point("1 - x^2 >= 0 @ [0, 2]",
                                      "1 - 2^2 >= 0", x="2"))},
    {"id": "product_nonstrict_parity",
     "key": ("x^2 - 1 >= 0", "[0, 1]"),
     "certificate": _product("1", [("x - 1", "<=", _farkas({GOAL: "1",
                                                           HI(0): "1"})),
                                   ("x + 1", ">", _RANGE_LO)]),
     "expected": "rejected",
     "rejects_because": "the identity holds and both children do, but one "
                        "'<=' factor under content 1 gives parity -1 "
                        "('parity')",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _point("x^2 - 1 >= 0 @ [0, 1]",
                                      "0^2 - 1 >= 0", x="0"))},
    {"id": "product_nonstrict_factor_under_strict_target",
     "key": ("1 - x^2 > 0", "[0, 1]"), "certificate": _ONE_MINUS_X2,
     "expected": "rejected",
     "rejects_because": "a '<=' factor under a strict target: x - 1 is 0 "
                        "at 1, and so is the product ('bad-relation')",
     "truth": ("false", {"x": "1"}),
     "if_emitted": ("refused", _point("1 - x^2 > 0 @ [0, 1]",
                                      "1 - 1^2 > 0", x="1"))},
]

# --- 13d. The entries (E54) ------------------------------------------------

# Pinned for entries.py in NAMED_ENTRIES' shape, appended after sqrt_nonneg
# in this order (ENTRIES: 17 -> 23).
CONSOLIDATION_ENTRIES = {
    "pyth": {
        "statement": "(sin u)^2 + (cos u)^2 == 1",
        "schema": ("u",), "hyps": (),
        "use": "the identity as the owner states it; the parent of "
               "pyth_cos. Corrected by the consolidation review: rewrite "
               "CAN use it, at a subterm tree-equal to (sin b)^2 + (cos b)^2 "
               "(a non-App left side is matched as a tree), turning it into "
               "1, soundly for every real b, and E57 refuses a b holding an "
               "Int or D node, which the rewrite would erase; field cannot "
               "(a fact must be a^k == r). pyth_cos is the form both use at "
               "(cos b)^2",
        "cite": "§6.2 ('sin²x + cos²x ≐ 1 ... needs the named identity "
                "pyth'), §6.8; Rocq's sin2_cos2",
        "used_in": ("the record; pyth_cos",)},
    "pyth_cos": {
        "statement": "(cos u)^2 == 1 - (sin u)^2",
        "schema": ("u",), "hyps": (),
        "use": "pyth solved for (cos u)^2: a rewrite at (cos b)^2 (a tree "
               "match, REWRITE_RULE step 3) and a field fact in §6.2's "
               "a^k == r shape, r free of the fact's atom. Its statement "
               "minus pyth's is a ring identity ((c^2 - (1 - s^2)) - ((s^2 "
               "+ c^2) - 1) = 0), so it adds no trust beyond pyth",
        "cite": "pyth, by ring",
        "used_in": ("problems/stage0 QC1 s2 (rewrite), s4-s5 (fact)",)},
    "sin_nonneg_on": {
        "statement": "sin u >= 0 @ u >= 0, u <= pi",
        "schema": ("u",), "hyps": ("u >= 0", "u <= pi"),
        "use": "cite (§5.3 method 6): closes sin b >= 0 (or 0 <= sin b) at a "
               "domain where b >= 0 and b <= pi are certified",
        "cite": "§6.8's sign facts; Rocq's sin_ge_0",
        "used_in": ("problems/stage0 QC1 s3 (sqrt_sq's sin theta >= 0)",)},
    "cos_nonneg_on": {
        "statement": "cos u >= 0 @ u >= 0, u <= pi/2",
        "schema": ("u",), "hyps": ("u >= 0", "u <= pi/2"),
        "use": "cite, as sin_nonneg_on: the owner's cos sign fact, which "
               "x := sin theta's sqrt_sq needs (QC1 by x := cos theta needs "
               "sin_nonneg_on instead)",
        "cite": "§6.8's sign facts; Rocq's cos_ge_0",
        "used_in": ("CONSOLIDATION_CHECKER_ACCEPTS cite_cos_nonneg",)},
    "cos_le_one": {
        "statement": "cos u <= 1",
        "schema": ("u",), "hyps": (),
        "use": "an atom sign fact read by the linear method for each cos "
               "atom (ATOM_FACT_RULE), and a cite entry",
        "cite": "Rocq's COS_bound",
        "used_in": ("QC1 s1: cos theta - 1 <= 0",)},
    "cos_ge_neg_one": {
        "statement": "cos u >= -1",
        "schema": ("u",), "hyps": (),
        "use": "likewise",
        "cite": "Rocq's COS_bound",
        "used_in": ("QC1 s1: cos theta + 1 >= 0",)},
}

ATOM_FACT_RULE = (
    "Generalises SQRT_FACT_RULE (E49) at the build: a Farkas label "
    "('fact', name, u) is in a key's constraint set exactly when name is "
    "one of ATOM_FACTS and an atom h(w) of that fact's head h occurs in "
    "the key's proposition or domain with ring_nf(w) = ring_nf(u); its "
    "constraint is the fact's statement at u, read as a target is "
    "(non-strict). No child certificate: sqrt_nonneg's hypothesis is its "
    "atom's definedness (E49), and cos_le_one and cos_ge_neg_one have "
    "none, cos being total. The search adds one constraint per fact per "
    "distinct atom; cites are ordered pi_pos, e_gt_one, sqrt_nonneg, "
    "cos_le_one, cos_ge_neg_one.",

    "Facts whose hypotheses are not their atom's definedness "
    "(sin_nonneg_on, cos_nonneg_on) are NOT labels: a Farkas certificate "
    "has no children, and the hypotheses u >= 0, u <= pi are real "
    "conditions on the argument. They reach the kernel through cite, whose "
    "children certify each instantiated hypothesis at the key's domain "
    "(DISCHARGE_RULE, Cite certificate), unchanged.",

    "E27 (a) and E31. pyth counts at a subterm tree-equal to (sin b)^2 + "
    "(cos b)^2 (a value holding it is unevaluated: it is 1). pyth_cos is "
    "not an evaluation, and E27 (a) does not count it, as it does not "
    "count a rewrite that trades one atom for another; no value in the "
    "data holds (cos b)^2. The ordering entries are not equations. None of "
    "the six is an exact value (each has a schema variable).",
)
ATOM_FACTS = {
    "sqrt_nonneg": ("sqrt", "sqrt u >= 0"),
    "cos_le_one": ("cos", "1 - cos u >= 0"),
    "cos_ge_neg_one": ("cos", "cos u + 1 >= 0"),
}


def ATOM(name, u):
    """ATOM_FACT_RULE's label; SQRT(u) is ATOM('sqrt_nonneg', u)."""
    return ("fact", name, u)


T_CITE_SIN = ("cite", ("sin_nonneg_on", "pi_pos"))
CONSOLIDATION_CHECKER_ACCEPTS = [
    {"id": "linear_cos_le_one",
     "key": ("cos theta - 1 <= 0", "[0, pi/2]"),
     "certificate": _farkas({GOAL: "1", ATOM("cos_le_one", "theta"): "1"}),
     "tag": ("linear", ("cos_le_one",)),
     "why": "(cos theta - 1, strict) + (1 - cos theta) = 0 with a strict "
            "constraint"},
    {"id": "linear_cos_ge_neg_one",
     "key": ("cos theta + 1 >= 0", "[0, pi/2]"),
     "certificate": _farkas({GOAL: "1",
                             ATOM("cos_ge_neg_one", "theta"): "1"}),
     "tag": ("linear", ("cos_ge_neg_one",)),
     "why": "(-(cos theta + 1), strict) + (cos theta + 1) = 0, strict"},
    {"id": "cite_sin_nonneg",
     "key": ("sin theta >= 0", "[0, pi/2]"),
     "certificate": _cite("sin_nonneg_on", {"u": "theta"},
                          [("theta >= 0", _RANGE_LO),
                           ("theta <= pi", _farkas({GOAL: "1", HI(0): "1",
                                                    FACT("pi_pos"): "1/2"}))]),
     "tag": T_CITE_SIN,
     "why": "theta <= pi: (theta - pi, strict) + (pi/2 - theta) + "
            "(1/2)(pi, strict) = 0"},
    {"id": "cite_cos_nonneg",
     "key": ("cos theta >= 0", "[0, pi/2]"),
     "certificate": _cite("cos_nonneg_on", {"u": "theta"},
                          [("theta >= 0", _RANGE_LO),
                           ("theta <= pi/2", _farkas({GOAL: "1",
                                                      HI(0): "1"}))]),
     "tag": ("cite", ("cos_nonneg_on",)),
     "why": "theta <= pi/2 is the upper end: (theta - pi/2, strict) + "
            "(pi/2 - theta) = 0"},
]
CONSOLIDATION_MUST_REJECT = [
    {"id": "cos_fact_nonstrict_pair",
     "key": ("cos theta - 1 < 0", "[0, pi/2]"),
     "certificate": _farkas({GOAL: "1", ATOM("cos_le_one", "theta"): "1"}),
     "expected": "rejected",
     "rejects_because": "(-(cos theta - 1)) + (1 - cos theta) = 0 with "
                        "both non-strict ('zero-without-strict')",
     "truth": ("false", {"theta": "0"}),
     "if_emitted": ("refused", _point("cos theta - 1 < 0 @ [0, pi/2]",
                                      "1 - 1 < 0", entries=("cos_zero",),
                                      theta="0"))},
    {"id": "sin_fact_not_a_label",
     "key": ("sin theta >= 0", "[0, pi/2]"),
     "certificate": _farkas({GOAL: "1",
                             ATOM("sin_nonneg_on", "theta"): "1"}),
     "expected": "rejected",
     "rejects_because": "sin_nonneg_on has hypotheses that are not its "
                        "atom's definedness, so it is no label "
                        "('unknown-label'); cite is its route",
     "truth": ("true",),
     # if emitted, the search's own certificate closes theta <= pi by the
     # range alone, so no pi_pos cite (DATA_CHANGES, adjudicated)
     "if_emitted": ("discharged", ("cite", ("sin_nonneg_on",)))},
]

# Planted bugs for the build (INT_SUBST_PLANTED_BUGS' shape).
CONSOLIDATION_PLANTED_BUGS = {
    "int_flip_drops_negation": {
        "mutation": "int_flip builds Integral(x, b, a, f), without Neg",
        "caught_by": [("INT_FLIP_ACCEPTS", "flip_reversed_symbolic_to_value")]},
    "int_flip_under_D_unchecked": {
        "mutation": "int_flip's step 3 is skipped",
        "caught_by": [("INT_FLIP_BAD_MOVES", "flip_under_D")]},
    "product_nonstrict_factor_on_strict": {
        "mutation": "a non-strict factor is accepted under a strict target",
        "caught_by": [("SIGN_PRODUCT_MUST_REJECT",
                       "product_nonstrict_factor_under_strict_target"),
                      ("PROPERTY", "sign product")]},
    "cos_fact_strict": {
        "mutation": "an ATOM_FACTS label is read as strict",
        "caught_by": [("CONSOLIDATION_MUST_REJECT", "cos_fact_nonstrict_pair"),
                      ("PROPERTY", "farkas")]},
    "atom_fact_any_entry": {
        "mutation": "any ENTRIES ordering is accepted as an atom label",
        "caught_by": [("CONSOLIDATION_MUST_REJECT", "sin_fact_not_a_label")]},
}

# Every existing expectation items 3 and 4 change, with its new value.
# Everything else was re-traced unchanged: every non-strict key in either
# file is closed by hyp, range, linear or sign before sign product is tried,
# or has no factorisation (x <= 5 @ [0, oo), degree 1, whose content split
# leaves x - 5 <= 0, false at 6: still admitted none); the only keys holding
# a cos atom outside Reg judgements are cos(pi/2) # 0 (refused by F1 before
# any search), cos 0 # 0 (norm_num after cos_zero) and cos 1 # 0 (still
# undecided: 1 - c >= 0 and c + 1 >= 0 do not give c # 0); no key holds a
# sin atom outside Reg judgements; no value in the E27 cases holds (cos b)^2
# or (sin b)^2 + (cos b)^2.
CONSOLIDATION_CHANGES = {
    "DISCHARGE_MUST_REJECT product_nonstrict_target": {
        "rejects_because": "was 'non-strict-target'; now the target is "
                           "allowed and the child x > 0 @ [-1, 1] fails: "
                           "(-x) + (x + 1) = 1 (child-rejected/"
                           "positive-constant)",
        "if_emitted": "unchanged: ('discharged', T_SIGN), sign coming first"},
    "INT_SUBST_ACCEPTS cos_theta_canonical": {
        "goal_emits": [("1 - x^2 >= 0", "[0, 1]", (S_FORMER,), DISCHARGED,
                        T_PRODUCT, True)],
        "emits_change": ("1 - (cos theta)^2 >= 0", "[0, pi/2]", (S_FORMER,),
                         DISCHARGED, T_PRODUCT_COS, True),
        "certificates_add": {
            ("1 - x^2 >= 0", "[0, 1]"): _ONE_MINUS_X2,
            ("1 - (cos theta)^2 >= 0", "[0, pi/2]"): _product(
                "-1", [("cos theta - 1", "<=",
                        _farkas({GOAL: "1",
                                 ATOM("cos_le_one", "theta"): "1"})),
                       ("cos theta + 1", ">=",
                        _farkas({GOAL: "1",
                                 ATOM("cos_ge_neg_one", "theta"): "1"}))])},
        "goal_reasons": "removed", "reasons": "removed (no admission is "
                                              "tagged none any more)"},
    "INT_SUBST_BAD_MOVES and F3_ROOTS_CHANGES prose": (
        "cos_theta_canonical's two keys, listed as admitted none, are now "
        "discharged"),
    "TAG_RULES 'sign product'": (
        "'It closes >, < and # 0 goals only, never >= or <=' is superseded "
        "by SIGN_PRODUCT_NONSTRICT_RULE"),
    "entries.py ENTRIES count": "17 -> 23",
    # owner's answers: a change E53 makes that this spec first missed (found
    # while re-tracing E56). Under pi_pos_not_in_constraint_set the search
    # has no sign fact, but E53's content split closes pi/2's order and
    # sqrt_sq's pi/2 >= 0 as (1/2)*pi with pi > 0 by cite pi_pos, which the
    # trusted ENTRIES still hold. See E56_CHANGES for the combined values.
    "E53 under pi_pos_not_in_constraint_set": (
        "0 <= pi/2 (P1.1, P1.1-sheet) and pi/2 >= 0 (the fallback) are "
        "DISCHARGED ('sign product', ('pi_pos',)) with _product('1/2', "
        "[('pi', '>', _cite('pi_pos', {}, []))]), not admitted none; N "
        "stays 3 for P1.1 and the fallback and 5 for P1.1-sheet; the "
        "catches are the tags"),
}

CONSOLIDATION_SWITCH = (
    "One commit, the suite green before and after. Kernel: int_flip as "
    "INT_FLIP_RULE states it (move list six long); discharge.py's sign "
    "product checker and search.py/tagger.py as SIGN_PRODUCT_NONSTRICT_RULE; "
    "the atom labels as ATOM_FACT_RULE; entries.py gains "
    "CONSOLIDATION_ENTRIES after sqrt_nonneg; schema.py's E27 (a) reads "
    "pyth and skips pyth_cos (ATOM_FACT_RULE). With it, E56 (owner's "
    "answers, section 14): one orientation rule for every step that builds "
    "a range, the code 'orientation-undecided', E56_CHANGES applied to the "
    "tables it names, E56_ACCEPTS, E56_BAD_MOVES and E56_PLANTED_BUGS "
    "asserted like section 13's.",
    "Data merged by the suite at the switch, not by editing the tables "
    "above: P1_1_SHEET_JOIN into PROOFS and the DISCHARGE_* tables (the "
    "sheet leaving INT_SUBST_PROOFS), every planted bug's and mutation's "
    "admissions and caught_by as P1_1_SHEET_TRACES gives them for the "
    "sheet, CONSOLIDATION_CHANGES applied to the tables it names, "
    "REFUSAL_CODES_INT_FLIP into the coverage check.",
    "Suite: INT_FLIP_ACCEPTS with their continuations and INT_FLIP_BAD_MOVES "
    "as the int_subst cases are asserted; SIGN_PRODUCT_* and "
    "CONSOLIDATION_CHECKER_ACCEPTS / _MUST_REJECT through test_discharge.py "
    "(the reason codes named in each rejects_because); "
    "DISCHARGE_PROPERTY_TEST's sign product family gains non-strict keys "
    "and its Farkas family keys holding a cos atom (evaluated at 0, where "
    "cos_zero gives it exactly, and skipped elsewhere); "
    "CONSOLIDATION_PLANTED_BUGS in child processes; problems/stage0 "
    "section 13 (QC1, in kernel/problems/consolidation/) under item 7's "
    "machinery with a floor of its own.",
)

# The data cross-checks itself when imported.
assert set(REFUSAL_CODES_INT_FLIP) <= {c["refusal"] for c in INT_FLIP_BAD_MOVES}
for _name in list(DISCHARGE_PLANTED_BUGS) + list(DISCHARGE_NEW_PLANTED_BUGS):
    assert _name in P1_1_SHEET_TRACES or _name in PLANTED_BUGS, _name
for _name in (*PLANTED_BUGS, *DISCHARGE_NEW_PLANTED_BUGS):
    assert _name in P1_1_SHEET_TRACES, _name
del _name


# ---------------------------------------------------------------------------
# 14. Reversed ranges everywhere (consolidation spec 2026-09-24, owner
#     answers; E56)
#
# The owner accepted both of the consolidation spec's recommendations: E51's
# form, and one orientation rule for every step. DECISIONS E56 states the
# rule and its soundness. Staged like section 13 (CONSOLIDATION_SWITCH also
# carries this section): the committed suite stays green until the build.

# One code for every step (E56), replacing 'int-subst-orientation-undecided'.
REFUSAL_CODES_E56 = {
    "orientation-undecided": "E56 (owner's answers): an Int's limits are "
                             "not two literals and have no infinite end, "
                             "and discharge proves neither lo <= hi nor "
                             "hi <= lo at the Int's position domain; any "
                             "step that builds the range (installation, a "
                             "new goal, rewrite, ftc, int_subst, int_flip)",
}
E56_MESSAGES = {
    "orientation-undecided": "the order of {lo} and {hi} is not decided; "
                             "state it in the goal's domain",
}

E56_ACCEPTS = [
    # A reversed symbolic goal whose body owes a former, proved end to end
    # by ftc without int_flip. Installation: pi/2 owes 2 # 0; sqrt(t^2)
    # owes t^2 >= 0 on the range, whose order is decided first: pi/2 <= 0
    # is not discharged, 0 <= pi/2 is (linear, pi_pos), so the range is
    # [0, pi/2] and 0 <= pi/2 is emitted.
    {"id": "reversed_symbolic_with_former_by_ftc",
     "goal": "Int[t = pi/2 .. 0] sqrt(t^2) == ?A",
     "goal_emits": [
         ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("t^2 >= 0", "[0, pi/2]", (S_FORMER,), DISCHARGED, T_SIGN, True),
         ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI, True)],
     "move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "t"},
                          "at": "sqrt(t^2)"}),
     "goal_after": "Int[t = pi/2 .. 0] t == ?A",
     # the position domain holds the proved range [0, pi/2]
     "emits": [
         ("t >= 0", "[0, pi/2]", (S_SQRT_SQ,), DISCHARGED, T_RANGE, True),
         ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI, False)],
     "then": [
         # ftc: premises on [0, pi/2] and (0, pi/2); the new goal
         # F(b) - F(a) with b = 0 and a = pi/2, as written
         {"move": ("ftc", {"F": "t^2/2", "check": "ring", "facts": []}),
          "goal_after": "0^2/2 - (pi/2)^2/2 == ?A",
          "deriv": {"var": "t", "F": "t^2/2",
                    "trace": [("route_div", "t^2/2", ("2 # 0",)),
                              ("d_mul", "t^2*(1/2)", ()),
                              ("d_pow_int", "t^2", ()), ("d_var", "t", ()),
                              ("d_const", "1/2", ())],
                    "output": "2*t^1*1*(1/2) + t^2*0",
                    "emits": ("2 # 0",)},
          "emits": [
              ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI,
               False),
              ("2 # 0", "true", (S_FORMER, S_ROUTE_DIV), DISCHARGED,
               T_NORM_NUM, False),
              ("t^2/2 in C^0([0, pi/2])", "[0, pi/2]", (S_FTC_C0F,),
               ADMITTED, T_REG, True),
              ("t^2/2 in C^1((0, pi/2))", "(0, pi/2)", (S_FTC_C1F,),
               ADMITTED, T_REG, True),
              ("D[t](t^2/2) == t", "(0, pi/2)", (S_FTC_D,), DISCHARGED,
               T_DERIV_RING, True),
              ("t in C^0([0, pi/2])", "[0, pi/2]", (S_FTC_C0f,), ADMITTED,
               T_REG, True)]},
         {"move": ("close", {"value": "-pi^2/8", "check": "ring",
                             "facts": []}),
          "goal_after": None,
          "emits": [("8 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
                     True)]},
     ],
     "certificates": {("t^2 >= 0", "[0, pi/2]"): _sos("0", [("1", "t", 2)]),
                      ("0 <= pi/2", "true"): _PI_HALF,
                      ("t >= 0", "[0, pi/2]"): _RANGE_LO},
     "report": VERDICT.format(n=3),
     "theorem": "Int[t = pi/2 .. 0] sqrt(t^2) == -pi^2/8",
     "why": "was DISCHARGE_BAD_MOVES_ADDED decided_false_reversed_range, "
            "refused at installation on pi/2 <= 0 by F2. Int_{pi/2}^0 "
            "sqrt(t^2) dt = -pi^2/8 (SymPy): on [0, pi/2] sqrt(t^2) = t, "
            "and the reversed limits give the sign"},
    # the owner's other example, ftc alone
    {"id": "reversed_symbolic_by_ftc_linear",
     "goal": "Int[x = pi/2 .. 0] 2*x == ?A",
     "goal_emits": [("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
                     True)],
     "move": ("ftc", {"F": "x^2", "check": "ring", "facts": []}),
     "goal_after": "0^2 - (pi/2)^2 == ?A",
     "deriv": {"var": "x", "F": "x^2",
               "trace": [("d_pow_int", "x^2", ()), ("d_var", "x", ())],
               "output": "2*x^1*1", "emits": ()},
     "emits": [
         ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI, True),
         ("x^2 in C^0([0, pi/2])", "[0, pi/2]", (S_FTC_C0F,), ADMITTED,
          T_REG, True),
         ("x^2 in C^1((0, pi/2))", "(0, pi/2)", (S_FTC_C1F,), ADMITTED,
          T_REG, True),
         ("D[x](x^2) == 2*x", "(0, pi/2)", (S_FTC_D,), DISCHARGED,
          T_DERIV_RING, True),
         ("2*x in C^0([0, pi/2])", "[0, pi/2]", (S_FTC_C0f,), ADMITTED,
          T_REG, True),
         ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, False)],
     "then": [
         {"move": ("close", {"value": "-pi^2/4", "check": "ring",
                             "facts": []}),
          "goal_after": None,
          "emits": [("4 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
                     True)]}],
     "certificates": {("0 <= pi/2", "true"): _PI_HALF},
     "report": VERDICT.format(n=3),
     "theorem": "Int[x = pi/2 .. 0] 2*x == -pi^2/4",
     "why": "the same value as INT_FLIP_ACCEPTS "
            "flip_reversed_symbolic_to_value, without the flip: F(b) - F(a) "
            "= 0^2 - (pi/2)^2 holds for either order (E56)"},
]
E56_BAD_MOVES = [
    # neither order decided: y is free and the goal states nothing about it
    {"id": "orientation_undecided_install",
     "goal": "Int[t = 0 .. y] sqrt(t^2) == ?A", "setup": [],
     "move": ("install", {}),
     "refusal": "orientation-undecided",
     "message": ("orientation-undecided", {"lo": "0", "hi": "y"}),
     "why": "sqrt(t^2)'s former needs the range, and neither 0 <= y nor "
            "y <= 0 is discharged. Under E4 the step emitted 0 <= y, which "
            "F3 decided false at y = -1; E56 refutes neither candidate and "
            "asks the learner to state the order"},
    # F2's own case, which decided_false_reversed_range no longer is: a
    # closed ordering whose negation is proved (sqrt_sq with the wrong sign)
    {"id": "decided_false_closed_negation",
     "goal": "sqrt(pi^2/4) == ?A", "setup": [],
     "move": ("rewrite", {"entry": "sqrt_sq", "inst": {"u": "-(pi/2)"},
                          "at": "sqrt(pi^2/4)"}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _negation("-(pi/2) >= 0", "-(pi/2) < 0", T_LINEAR_PI),
     "why": "ring_nf((-(pi/2))^2) = pi^2/4 matches; the hypothesis "
            "-(pi/2) >= 0 is closed, no method proves it (E53's content "
            "split would need pi <= 0), and its negation is linear with "
            "pi_pos: (-(pi/2), non-strict) + (1/2)(pi, strict) = 0. "
            "Installation owes pi^2/4 >= 0 (sign) and 4 # 0"},
]

# E56's planted bugs (INT_SUBST_PLANTED_BUGS' shape).
E56_PLANTED_BUGS = {
    "orientation_tries_one_order": {
        "mutation": "only lo <= hi is tried (E4's old reading, without F2)",
        "caught_by": [("E56_ACCEPTS", "reversed_symbolic_with_former_by_ftc"),
                      ("E56_ACCEPTS", "reversed_symbolic_by_ftc_linear"),
                      ("INT_FLIP_ACCEPTS", "flip_oriented_symbolic_with_former")]},
    "orientation_order_unproved": {
        "mutation": "[hi, lo] is used whenever lo <= hi is not discharged, "
                    "without discharging hi <= lo",
        "caught_by": [("E56_BAD_MOVES", "orientation_undecided_install"),
                      ("DISCHARGE_BAD_MOVES_CHANGED",
                       "rewrite_under_D_through_Int")]},
}

# Every existing expectation E56 changes, with the old and the new values,
# and those E53 changes that the consolidation spec missed (found while
# re-tracing this). Unmutated runs: no admission count moves, because every
# orientation key any table lists was discharged (0 <= pi/2, 0 <= pi^2/4,
# 1 <= e_const, 0 <= x @ 0 <= x) and E56 emits the same key with the same
# certificate; only refusals that rested on a false or undecided order
# change.
E56_CHANGES = {
    "DISCHARGE_BAD_MOVES_ADDED decided_false_reversed_range": {
        "old": ("refused at installation, obligation-decided-false",
                _negation("pi/2 <= 0", "pi/2 > 0", T_LINEAR_PI)),
        "new": "installs; the case is replaced by E56_ACCEPTS "
               "reversed_symbolic_with_former_by_ftc (its goal, proved to "
               "-pi^2/8) and, as F2's example, by E56_BAD_MOVES "
               "decided_false_closed_negation"},
    "DISCHARGE_BAD_MOVES_CHANGED rewrite_under_D_through_Int": {
        "old": ("refused at installation, obligation-decided-false",
                _point("0 <= x", "0 <= -1", x="-1")),
        "new": ("refused at installation, orientation-undecided",
                ("orientation-undecided", {"lo": "0", "hi": "x"}))},
    "REVIEW_BAD_MOVES reverse_symbolic_old_range_reversed": {
        "old": ("refused, obligation-decided-false",
                _negation("pi/2 <= 0", "pi/2 > 0", T_LINEAR_PI)),
        # step 8 reverse: I is [0, pi/2] (0 <= pi/2 proved); hi's pi^2/4
        # owes 4 # 0; the new limits pi^2/4 .. 0 are reversed, 0 <= pi^2/4
        # is proved (sign), so int_subst flips (E46)
        "new": {"goal_emits": [("2 # 0", "true", (S_FORMER,), DISCHARGED,
                                T_NORM_NUM, True)],
                "goal_after": "Int[u = 0 .. pi^2/4] -1 == ?A",
                "emits": [
                    ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED,
                     T_LINEAR_PI, True),
                    ("4 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
                     True),
                    ("0 <= pi^2/4", "true", (S_ORIENT,), DISCHARGED, T_SIGN,
                     True),
                    ("2*x == 1*(2*x^1*1)", "[0, pi/2]", (S_SUBST_INT,),
                     DISCHARGED, T_DERIV_RING, True),
                    ("(pi/2)^2 == pi^2/4", "true", (S_SUBST_LO,), DISCHARGED,
                     T_RING, True),
                    ("0^2 == 0", "true", (S_SUBST_HI,), DISCHARGED, T_RING,
                     True),
                    ("x^2 in C^1([0, pi/2])", "[0, pi/2]", (S_SUBST_C1,),
                     ADMITTED, T_REG, True),
                    ("1 in C^0(x in [0, pi/2])", "x in [0, pi/2]",
                     (S_SUBST_C0,), ADMITTED, T_REG, True)],
                "certificates": {("0 <= pi/2", "true"): _PI_HALF,
                                 ("0 <= pi^2/4", "true"): _PI_SQ},
                "moves_to": "INT_SUBST_ACCEPTS"}},
    "REVIEW_PLANTED_BUGS int_subst_reverse_no_old_orient caught_by": {
        "old": ("INT_SUBST_BAD_MOVES", "reverse_symbolic_old_range_reversed"),
        "new": ("INT_SUBST_ACCEPTS", "reverse_symbolic_old_range_reversed")},
    "INT_SUBST_BAD_MOVES orientation_undecided": {
        "old": ("int-subst-orientation-undecided",
                ("int-subst-orientation-undecided", {"lo": "0", "hi": "1/y"})),
        "new": ("orientation-undecided",
                ("orientation-undecided", {"lo": "0", "hi": "1/y"}))},
    "REFUSAL_CODES_INT_SUBST / INT_SUBST_MESSAGES": {
        "old": "'int-subst-orientation-undecided'",
        "new": "removed; REFUSAL_CODES_E56's 'orientation-undecided', same "
               "template"},
    # E53 (consolidation), under the pi_pos seam: the content split closes
    # pi/2's sign by cite pi_pos, which the seam does not remove
    "DISCHARGE_PLANTED_BUGS pi_pos_not_in_constraint_set": {
        "old": {"admissions": {"P1.1": 4, "P1.1-fallback": 4, "P1.2": 3,
                               "P1.2-alt": 3},
                "retagged": "0 <= pi/2 (P1.1) and pi/2 >= 0 (fallback) "
                            "ADMITTED ('none', ())",
                "caught_by": "tags at P1.1 goal, s1, s2 and fallback s2; "
                             "statuses at P1.1 goal and fallback s2; N for "
                             "P1.1 and the fallback"},
        "new": {"admissions": {"P1.1": 3, "P1.1-fallback": 3, "P1.2": 3,
                               "P1.2-alt": 3, "P1.1-sheet": 5},
                "retagged": {
                    "P1.1": [("0 <= pi/2", "true", DISCHARGED,
                              ("sign product", ("pi_pos",)))],
                    "P1.1-fallback": [("pi/2 >= 0", "true", DISCHARGED,
                                       ("sign product", ("pi_pos",)))]},
                "certificate": _product("1/2", [("pi", ">",
                                                 _cite("pi_pos", {}, []))]),
                "caught_by": [("P1.1", "goal", "0 <= pi/2", "tag"),
                              ("P1.1", "s1", "0 <= pi/2", "tag"),
                              ("P1.1", "s2", "0 <= pi/2", "tag"),
                              ("P1.1-fallback", "s2", "pi/2 >= 0", "tag")],
                "note": "were E56 to land without E53, P1.1 would instead "
                        "be refused at installation, orientation-undecided"}},
    "INT_SUBST_SEAMS pi_pos_not_in_constraint_set": {
        "old": {"caught_by": [("P1.1-sheet", "s1", "refused")]},
        "new": {"admissions": {"P1.1-sheet": 5},
                "caught_by": [("P1.1-sheet", "s1", "0 <= pi/2", "tag"),
                              ("P1.1-sheet", "s2", "0 <= pi/2", "tag"),
                              ("P1.1-sheet", "s3", "0 <= pi/2", "tag")],
                "retagged": {"P1.1-sheet": [("0 <= pi/2", "true", DISCHARGED,
                                             ("sign product", ("pi_pos",)))]}}},
    # E56: search_scales_wrongly's 0 <= pi/2 certificate is rejected and no
    # later method is tried (E28); pi/2 <= 0 has none; so P1.1 cannot
    # decide its range's order at installation
    "DISCHARGE_NEW_PLANTED_BUGS search_scales_wrongly": {
        "old": {"admissions": {"P1.1": 4, "P1.1-fallback": 4, "P1.2": 3,
                               "P1.2-alt": 3},
                "caught_by": [("P1.1", "goal", "0 <= pi/2", "status"),
                              ("P1.1-fallback", "s2", "pi/2 >= 0", "status"),
                              ("N", "P1.1"), ("N", "P1.1-fallback")]},
        "new": {"admissions": {"P1.1-fallback": 4, "P1.2": 3, "P1.2-alt": 3},
                "refused": {"P1.1": ("goal", ("orientation-undecided",
                                              {"lo": "0", "hi": "pi/2"})),
                            "P1.1-sheet": ("s1", ("orientation-undecided",
                                                  {"lo": "0", "hi": "pi/2"}))},
                "caught_by": [("P1.1", "goal", "refused"),
                              ("P1.1-fallback", "s2", "pi/2 >= 0", "status"),
                              ("N", "P1.1-fallback")]}},
    "P1_1_SHEET_TRACES": "pi_pos_not_in_constraint_set now N 5 with tag "
                         "catches (E53); search_scales_wrongly's refusal "
                         "code orientation-undecided (already amended in "
                         "place)",
    "INT_FLIP (section 13, staged)": "flip_oriented_symbolic_with_former "
                                     "moved from INT_FLIP_BAD_MOVES to "
                                     "INT_FLIP_ACCEPTS (amended in place)",
    "unchanged, re-traced": (
        "every P1, stage-0 and int_subst proof: each orientation key is "
        "the same key, discharged the same way (0 <= pi/2 linear, "
        "0 <= pi^2/4 sign, 1 <= e_const linear); no N moves",
        "int_subst's flipped outputs (decreasing_symbolic_ends_flipped, "
        "cos_theta_*, QC1): E46's flip is kept",
        "INT_SUBST_PLANTED_BUGS int_subst_no_orientation: still caught at "
        "its three cases (cos_theta_full's ftc now succeeds on the "
        "unflipped goal under the bug, but its goal_after and lists "
        "differ)",
        "farkas_swaps_interval_ends and every other checker bug: the "
        "search proposes no certificate for a false order, so a widened "
        "checker never selects the wrong interval, and a narrowed one "
        "(the swap) leaves 0 <= pi/2, a fact-only certificate, alone",
        "tracker_drops_reemitted: its key 0 <= pi/2 is still emitted at "
        "P1.1's installation and dropped once",
        "F3_ROOTS_CASES, the E27 cases, the stage-0 seams: no symbolic "
        "reversed range",
    ),
    "prose superseded": (
        "DOMAIN_RULES E4 ('a non-literal reversed range ... gets the false "
        "obligation pi/2 <= 0 ... refused once discharge exists'; 'An "
        "orient argument is future work')",
        "DISCHARGE_RULE's vacuity paragraph ('What keeps a vacuous "
        "discharge from mattering is E4 ...'): E56's intervals are never "
        "empty, which is stronger",
        "E33's and DISCHARGE_RULE's F2 example pi/2 <= 0 (now "
        "decided_false_closed_negation's -(pi/2) >= 0)",
        "E51's limitation and DESIGN_DEFECTS' E4-installation entry",
    ),
}


# ---------------------------------------------------------------------------
# 15. The consolidation review (consolidation review 2026-09-24)
#
# The skeptic of the consolidation build (834b8a2) found a false plain
# 'Proved.' (E57) and two E56 defects: an enclosing range used undecided by
# int_subst, and eager orientation decisions costing 30 s on a range no key
# uses. Specified before any code; staged (REVIEW2_SWITCH).

E57_RULE = (
    "Amends REWRITE_RULE at the build, as a new step 2a between steps 2 "
    "and 3: if any inst value, or the target `at`, holds an Integral or "
    "Deriv node (terms.trees), the rewrite is refused "
    "'Int-or-D-not-normalisable', whichever branch step 3 would take. "
    "Step 3's App branch already refused such an argument through ring_nf "
    "(E26 (b)); its tree branch, for a left side that is not an App "
    "(pyth's sum, pyth_cos's power), compared trees and never "
    "normalised, so a schema variable bound to an Int or D node passed, "
    "and an entry whose right side drops that variable erased the node. "
    "The test is a seam for the architecture to name, because BACKSTOPS "
    "rewrite_closing_check_goal (an Int carried in through an inst value, "
    "reaching the closing check_goal when step 3 is lax) must now patch it "
    "too to reach the check.",
)

# The principle, checked against every move.
E57_PRINCIPLE = {
    "rewrite": "refuses by E57_RULE; R and H are instances of the entry's "
               "sides under inst, so an Int or D node reaches them only "
               "through inst, which the rule stops",
    "close": "complies: the whitelist (E23) refuses a value holding Int or "
             "D, and the check's ring or field refuses any side holding "
             "one (E26 (b)), so close cannot cancel one away",
    "ftc": "complies: ftc replaces the top-level Int by F(b) - F(a), which "
           "is its conclusion, and the Int's definedness is owed by its "
           "premises (f in C^0, admitted until regularity); an Int or D "
           "inside F is refused by deriv (E12), one inside the integrand "
           "by the check's ring or field, and (second review) one in a "
           "limit by an explicit check before the orientation is decided, "
           "since F(b) - F(a) would carry it into the goal with nothing "
           "owed for it (SECOND_REVIEW_RULE)",
    "int_subst": "complies: it replaces one Int by another under its "
                 "premises; a nested Int or D in the body is carried into "
                 "the new body by substitution, never dropped; one in sub "
                 "is refused by deriv, one in a limit or in f by the "
                 "endpoint or integrand check's ring (E26 (b))",
    "int_flip": "complies: it reorders the limits and negates the body, "
                "dropping nothing; by decision (second review) it refuses an "
                "Int whose limit holds an Int or D node, as ftc and int_subst "
                "do, so that no move acts on an integral whose range cannot "
                "be stated",
    "fact": "complies: a handle whose inst holds an Int or D node keeps it "
            "in its conclusion, and every use refuses it (field's "
            "normaliser for facts, norm_num for the inst formers it "
            "charges, E26 (b)); fact itself need not refuse",
    "field facts": "comply: field normalises each fact's sides, and its "
                   "normaliser refuses an Int or D node",
    "exact values (E31) and every checker": "comply: they match or "
                                            "normalise through ring_nf, "
                                            "which refuses the node, and a "
                                            "refusal inside discharge is no "
                                            "rewrite and no acceptance "
                                            "(E30)",
}

E57_BAD_MOVES = [
    {"id": "pyth_erases_D",
     "goal": "(sin(D[x](abs x)))^2 + (cos(D[x](abs x)))^2 == ?A", "setup": [],
     "move": ("rewrite", {"entry": "pyth", "inst": {"u": "D[x](abs x)"},
                          "at": "(sin(D[x](abs x)))^2 + (cos(D[x](abs x)))^2"}),
     "refusal": "Int-or-D-not-normalisable",
     "was": "accepted; close 1 by ring then reported 'Proved.' with no "
            "admission, though D[x](abs x) does not exist at x = 0",
     "why": "E57: the inst value holds a D node, which pyth's right side 1 "
            "would erase. The goal installs: sin, cos and abs are total and "
            "a D node owes no former"},
    {"id": "pyth_erases_divergent_Int",
     "goal": "(sin(Int[x = 1 .. oo] 1))^2 + (cos(Int[x = 1 .. oo] 1))^2 == ?A",
     "setup": [],
     "move": ("rewrite", {"entry": "pyth",
                          "inst": {"u": "Int[x = 1 .. oo] 1"},
                          "at": "(sin(Int[x = 1 .. oo] 1))^2"
                                " + (cos(Int[x = 1 .. oo] 1))^2"}),
     "refusal": "Int-or-D-not-normalisable",
     "was": "accepted, then 'Proved.' for a goal about a divergent integral",
     "why": "E57, with an Int node: Int[x = 1 .. oo] 1 diverges"},
]
E57_ACCEPTS = [
    {"id": "pyth_on_a_variable",
     "goal": "(sin z)^2 + (cos z)^2 == ?A",
     "goal_emits": [],   # sin and cos are total
     "move": ("rewrite", {"entry": "pyth", "inst": {"u": "z"},
                          "at": "(sin z)^2 + (cos z)^2"}),
     "occurrences": 1,
     "goal_after": "1 == ?A",
     "emits": [],        # no hypothesis; R = 1 has no former
     "then": [{"move": ("close", {"value": "1", "check": "ring",
                                  "facts": []}),
               "goal_after": None, "emits": []}],
     "report": PROVED,
     "theorem": "(sin z)^2 + (cos z)^2 == 1",
     "why": "the tree branch at a tree-equal target, sound for every real "
            "z; a plain 'Proved.' with nothing owed is right here"},
]

E56_AMENDMENTS = (
    "Enclosing ranges. Every interval item in the domain of every key any "
    "step emits was built by E56: the step's own ranges, and each "
    "enclosing Int's range in a position domain P. So a step emitting any "
    "key at P, or at a domain extending P (int_subst's D = P+I or P+I', "
    "rewrite's P, int_flip's and a new goal's position domains), first "
    "decides the order of each enclosing range that domain holds, "
    "outermost first, and refuses 'orientation-undecided' with that "
    "range's {lo} and {hi} when neither order is discharged. A decided "
    "enclosing order is emitted as its key (source orient), as the step's "
    "own is. The skeptic's reproducer, Int[y = a .. b] (Int[x = a .. y] "
    "1) with int_subst on the inner Int, emitted its premises on an "
    "undecided [a, b]: refused now (E56_REVIEW_CASES).",

    "Laziness. The order of a range is decided when, and only when, a key "
    "whose domain holds that range's interval is emitted; a range no "
    "emitted key uses is never decided, and costs nothing. That was E4's "
    "reading and E56's text ('wherever a range is used'), so no expected "
    "value changes. Each decision (steps (3)-(5) on lo <= hi, then on "
    "hi <= lo) is memoised per key: discharge is a function of the key "
    "and ENTRIES alone (E32), so a repeated question has the same answer. "
    "Int[x = (a-1)^40 .. 0] sin 0 == ?A emits nothing at installation "
    "(sin 0 is total, the limits owe no former), so it decides nothing; "
    "the build asserts it installs within E56_TIMING_BOUND seconds (it "
    "took 30.5 s at 834b8a2).",
)
E56_TIMING_BOUND = 2.0   # seconds, on the suite's machine
E56_REVIEW_CASES = {
    "bad_moves": [
        {"id": "int_subst_enclosing_range_undecided",
         "goal": "Int[y = a .. b] (Int[x = a .. y] 1) == ?A", "setup": [],
         "move": ("int_subst", {"var": "x", "sub": "t", "new_var": "t",
                                "lo": "a", "hi": "y", "check": "ring",
                                "facts": []}),
         "refusal": "orientation-undecided",
         "message": ("orientation-undecided", {"lo": "a", "hi": "b"}),
         "was": "accepted, its premises on y in [a, b] with a <= b never "
                "decided",
         "why": "the inner Int's position domain holds the outer range, "
                "whose order a <= b is not discharged (a and b are free and "
                "unconstrained); the goal installs, since 1 owes nothing"},
    ],
    "accepts": [
        # the decided twin; hand-derived, then matched against the
        # committed kernel, which emits every key below but a <= b
        {"id": "int_subst_enclosing_range_decided",
         "goal": "Int[y = a .. b] (Int[x = a .. y] 1) == ?A @ a <= b",
         "goal_emits": [],
         "move": ("int_subst", {"var": "x", "sub": "t", "new_var": "t",
                                "lo": "a", "hi": "y", "check": "ring",
                                "facts": []}),
         "goal_after": "Int[y = a .. b] (Int[t = a .. y] 1*1) == ?A @ a <= b",
         "deriv": {"var": "t", "F": "t",
                   "trace": [("d_var", "t", ())], "output": "1",
                   "emits": ()},
         "emits": [
             ("a <= b", "a <= b", (S_ORIENT,), DISCHARGED, T_HYP, True),
             ("a <= y", "a <= b, y in [a, b]", (S_ORIENT,), DISCHARGED,
              T_RANGE, True),
             ("a == a", "a <= b, y in [a, b]", (S_SUBST_LO,), DISCHARGED,
              T_RING, True),
             ("y == y", "a <= b, y in [a, b]", (S_SUBST_HI,), DISCHARGED,
              T_RING, True),
             ("t in C^1(a <= b, y in [a, b], t in [a, y])",
              "a <= b, y in [a, b], t in [a, y]", (S_SUBST_C1,), ADMITTED,
              T_REG, True),
             ("1 in C^0(a <= b, y in [a, b], t in [a, y])",
              "a <= b, y in [a, b], t in [a, y]", (S_SUBST_C0,), ADMITTED,
              T_REG, True)],
         "certificates": {("a <= b", "a <= b"): _member(0),
                          ("a <= y", "a <= b, y in [a, b]"):
                              _farkas({GOAL: "1", LO(1): "1"})},
         "why": "the outer order a <= b is the goal's hypothesis; the new "
                "range's a <= y follows from y's lower end"},
        {"id": "lazy_unused_range_installs",
         "goal": "Int[x = (a-1)^40 .. 0] sin 0 == ?A",
         "goal_emits": [],
         "timing_bound": E56_TIMING_BOUND,
         "why": "no key uses the range, so its order is never decided "
                "(E56_AMENDMENTS, laziness)"},
    ],
}

REVIEW2_PLANTED_BUGS = {
    "rewrite_tree_branch_skips_E57": {
        "mutation": "E57's test runs only on the App branch",
        "caught_by": [("E57_BAD_MOVES", "pyth_erases_D"),
                      ("E57_BAD_MOVES", "pyth_erases_divergent_Int")]},
    "enclosing_range_undecided": {
        "mutation": "a position domain's enclosing ranges are used without "
                    "deciding their order",
        "caught_by": [("E56_REVIEW_CASES",
                       "int_subst_enclosing_range_undecided"),
                      ("E56_REVIEW_CASES",
                       "int_subst_enclosing_range_decided")]},
}

# What changes in existing expectations: nothing. E57 refuses only moves
# whose inst values or target hold an Int or D node, and every such case in
# the data (match_refuses_Int, match_refuses_D, rewrite_inst_shadows) was
# already refused 'Int-or-D-not-normalisable' by step 3; no accepted rewrite
# carries one. The enclosing-range rule changes no accepted case, since none
# acts inside an Int with an undecided range. Laziness changes no value. The
# suite-level BACKSTOPS rewrite_closing_check_goal needs E57's seam patched
# as well (E57_RULE).
REVIEW2_CHANGES = {
    "BACKSTOPS rewrite_closing_check_goal (suite)": "patch E57's seam too",
    "CONSOLIDATION_ENTRIES pyth 'use'": "corrected (rewrite can use pyth)",
    "entries.py's docstring for pyth": "the build corrects it the same way",
    "DESIGN_DEFECTS §6.2 pyth entry": "corrected in place",
    "expected values": "none change",
}
REVIEW2_SWITCH = (
    "One commit: E57's step 2a in kernel.py's rewrite (a seam), the "
    "enclosing-range decision and the lazy, memoised orientation "
    "decision; the suite asserts E57_BAD_MOVES, E57_ACCEPTS, "
    "E56_REVIEW_CASES (the timing case by its bound), REVIEW2_PLANTED_BUGS "
    "in child processes, and patches E57's seam in the backstop.",
)



# ---------------------------------------------------------------------------
# 16. The second review (second review 2026-09-24)
#
# An independent second review of 45132e5 found no false 'Proved.' and four
# minors; these two need spec. Staged (SECOND_REVIEW_SWITCH).

SECOND_REVIEW_RULE = (
    "ftc (after E9's infinite-endpoint check), int_subst (after "
    "INT_SUBST_RULE step 3) and int_flip (after its selection) test the "
    "limits of the Int they act on, and int_subst also its new limits lo "
    "and hi, for an Integral or Deriv node (terms.trees); one found "
    "refuses 'Int-or-D-not-normalisable' before anything is emitted and "
    "before any order is decided. Reason (E57's principle): such a limit "
    "has no definedness condition the kernel can state, and ftc's F(b) - "
    "F(a), int_subst's endpoint images and int_flip's new integral would "
    "carry it into the goal; the refusal was reached before only by "
    "accident (norm_num refusing the orientation key inside E56's "
    "decision, or the endpoint check's ring). int_flip is included by "
    "decision, for one rule across the three moves; it erased nothing. "
    "Installation is unchanged: a goal may hold such an Int, and every key "
    "holding the tree is refused by E7 as before.",
)
SECOND_REVIEW_BAD_MOVES = [
    {"id": "ftc_limit_holds_Int",
     "goal": "Int[x = 0 .. (Int[y = 1 .. oo] 1)] 0 == ?A", "setup": [],
     "move": ("ftc", {"F": "0", "check": "ring", "facts": []}),
     "refusal": "Int-or-D-not-normalisable",
     "was": "orientation-undecided, 'the order of 0 and Int[y = 1 .. oo] 1 "
            "is not decided', by accident",
     "why": "the upper limit is a divergent integral; the goal installs "
            "(0 owes nothing, so no key uses the range)"},
    {"id": "int_subst_reverse_limit_holds_Int",
     "goal": "Int[x = 0 .. (Int[y = 1 .. oo] 1)] 0 == ?A", "setup": [],
     "move": ("int_subst", {"mode": "reverse", "var": "x", "sub": "x",
                            "new_var": "u", "lo": "0",
                            "hi": "1", "f": "0",
                            "check": "ring", "facts": [], "occurrence": 0}),
     "refusal": "Int-or-D-not-normalisable",
     # hi was the Int itself, but it holds oo, which INT_SUBST_RULE step 1
     # refuses 'bad-args' before step 3 (DATA_CHANGES, adjudicated)
     "was": "bad-args with the old hi (it held oo); with hi := 1, "
            "orientation-undecided: reverse mode decides the old range's "
            "order first (step 8)",
     "why": "the selected Int's upper limit holds an Int"},
    {"id": "int_flip_limit_holds_Int",
     "goal": "Int[x = 0 .. (Int[y = 1 .. oo] 1)] 0 == ?A", "setup": [],
     "move": ("int_flip", {"occurrence": 0}),
     "refusal": "Int-or-D-not-normalisable",
     "was": "accepted (no key uses the new range, so nothing decided it)",
     "why": "int_flip's part of SECOND_REVIEW_RULE, by decision"},
]
# Forward int_subst on the same goal was refused Int-or-D-not-normalisable
# already, by its endpoint check's ring; now by the explicit test, the same
# code. No existing case in either data file acts on an Int with a tree in a
# limit, so no existing refusal code changes.

# E58: 0^0 = 1. Each installs owing nothing (a Pow with a literal exponent
# owes no former) and closes by ring with 1; E27 accepts the value 1 (a
# rational literal in lowest terms); the report is 'Proved.'. Checked on
# the committed kernel (45132e5), which already behaves this way.
E58_ACCEPTS = [
    {"id": "zero_to_the_zero",
     "goal": "0^0 == ?A", "goal_emits": [],
     "move": ("close", {"value": "1", "check": "ring", "facts": []}),
     "goal_after": None, "emits": [],
     "report": PROVED, "theorem": "0^0 == 1"},
    {"id": "difference_to_the_zero",
     "goal": "(x - x)^0 == ?A", "goal_emits": [],
     "move": ("close", {"value": "1", "check": "ring", "facts": []}),
     "goal_after": None, "emits": [],
     "report": PROVED, "theorem": "(x - x)^0 == 1",
     "why": "the base normalises to 0 for every x, and the power is still 1: "
            "the convention is about the integer exponent, not the base"},
]
SECOND_REVIEW_SWITCH = (
    "One commit: the three moves' limit test; the suite asserts "
    "SECOND_REVIEW_BAD_MOVES and E58_ACCEPTS (these already pass on "
    "45132e5). GRAMMAR.md and DESIGN.md §5.1 are the main session's to "
    "edit for E58.",
)


# ---------------------------------------------------------------------------
# 17. Regularity, specified before any code (regularity spec 2026-09-24)
#
# WHAT.md "Start here: regularity, the last piece of stage 1". DECISIONS
# E59-E70 give the design in brief with § references; the tables below
# state it in full, one paragraph per point, as DISCHARGE_RULE and
# INT_SUBST_RULE do. Written from DESIGN.md revision 10 (§5.1, §5.2, §5.3,
# §5.4, §6.1, §6.4, §6.9, §14, §15.2, §18 Q22-Q23), ARCHITECTURE.md,
# GRAMMAR.md and the data files, without reading kernel.py, discharge.py,
# search.py or refute.py. Every string was parsed with terms.py's parser,
# every certificate's side conditions re-checked against the committed
# checker, and every regularity claim, certified or rejected, checked with
# SymPy in a scratch directory (VERIFIED, last entry). Staged: nothing here
# is asserted until the build (REG_SWITCH, E70).

# Reasons after the switch: REASON_REG is retired (E60). An admitted Reg
# carries REASON_NONE (no derivation, tag ('none', ())) or REASON_REJECTED
# (the search proposed a certificate the checker refused, tag ('reg', ())),
# which no unmutated run produces.
REG_REASONS_AFTER = (REASON_NONE, REASON_REJECTED)
# A discharged Reg's tag is ('reg', cites): the cites of its side
# certificates in pre-order first use (REG_CHECK_RULE, Tag).
T_REG_OK = ("reg", ())
T_REG_SQRT_POS = ("reg", ("sqrt_pos",))
T_REG_SQRT_NONNEG = ("reg", ("sqrt_nonneg",))
T_REG_COS = ("reg", ("cos_le_one", "cos_ge_neg_one"))
DISCHARGE_METHODS_REG = {
    "reg": "§6.9's closure rules as a checked derivation by term structure, "
           "each side condition a §5.3 certificate (E60, REG_CHECK_RULE)",
}

# E61. The rule table, as data: rule name -> (the term node it applies to,
# the children it consumes in GRAMMAR.md §7's field order, its C^0 sides,
# its C^1 sides). 'NATURAL_DOMAINS' means the builtin's row of E26's table,
# read at check time from the one table the formers also read; 'interior'
# means that row with >= made > and <= made < (REG_C1_EXTRA added).
REG_RULES = {
    "const":   ("Num, or Const pi or e_const", (), (), ()),
    "var":     ("Var, any variable", (), (), ()),
    "neg":     ("Neg(a)", ("a",), (), ()),
    "add":     ("Add(a, b)", ("a", "b"), (), ()),
    "mul":     ("Mul(a, b)", ("a", "b"), (), ()),
    "div":     ("Div(a, b)", ("a", "b"), ("b # 0",), ("b # 0",)),
    "pow":     ("Pow(a, n), n >= 0 (n = 0 included: E58's u^0 is 1, but "
                "the base is still owed, conservatively)", ("a",), (), ()),
    "pow_neg": ("Pow(a, n), n < 0", ("a",), ("a # 0",), ("a # 0",)),
    "rpow":    ("RPow(a, w)", ("a", "w"), ("a > 0",), ("a > 0",)),
    # one rule per builtin, named by the builtin; its child is the argument u
    "app":     ("App(f, u), f one of the sixteen builtins; the rule's name "
                "is f", ("u",), "NATURAL_DOMAINS[f](u), nothing for a total "
                "builtin", "interior(NATURAL_DOMAINS[f](u)) + "
                "REG_C1_EXTRA[f](u)"),
}
REG_BUILTINS_TOTAL = ("sin", "cos", "atan", "exp", "abs", "sinh", "cosh",
                      "tanh", "asinh")
REG_C1_EXTRA = {"abs": "u # 0"}   # the one datum regularity adds to E26's
# The resulting sides, spelled out once for review (not a second table the
# kernel reads: the checker derives them from NATURAL_DOMAINS and
# REG_C1_EXTRA, and the suite compares this listing against that derivation).
REG_SIDES_LISTED = {
    "ln":    (("u > 0",), ("u > 0",)),
    "sqrt":  (("u >= 0",), ("u > 0",)),
    "tan":   (("cos u # 0",), ("cos u # 0",)),
    "asin":  (("u >= -1", "u <= 1"), ("u > -1", "u < 1")),
    "acos":  (("u >= -1", "u <= 1"), ("u > -1", "u < 1")),
    "acosh": (("u >= 1",), ("u > 1",)),
    "atanh": (("u > -1", "u < 1"), ("u > -1", "u < 1")),
    "abs":   ((), ("u # 0",)),
    **{f: ((), ()) for f in ("sin", "cos", "atan", "exp", "sinh", "cosh",
                             "tanh", "asinh")},
}

# The certificate the untrusted search proposes and the checker checks.
REG_CERTIFICATE = (
    "{'method': 'reg', 'tree': NODE}, where NODE is {'rule': name, "
    "'args': (NODE, ...), 'side': ((prop, cert), ...)}: plain data, like "
    "every certificate (DISCHARGE_RULE, the trust split). 'rule' is a "
    "REG_RULES name or a builtin's name; 'args' has one node per child the "
    "rule consumes, in order; 'side' has one pair per side condition the "
    "rule gives at the key's class, in the table's order, prop being the "
    "side's proposition (a GRAMMAR.md string in this file, a Judgement "
    "with empty domain for the checker) and cert its §5.3 certificate "
    "(hyp, farkas, sign, sign product, cite, or the norm_num leaf). The "
    "tree mirrors the term: the checker walks the key's term and the "
    "certificate together, so the certificate never names a subterm.",
)

# E60. What the trusted checker checks, in order; the first rule broken
# names the rejection (REG_REASONS).
REG_CHECK_RULE = (
    "Key. The key is Reg(e, k, D). k must be 0 or 1, else 'class-not-built' "
    "(C^2 and up and C^omega are §6.9's, not this step's). The certificate "
    "must be a dict with exactly the keys method ('reg') and tree, and "
    "every node a dict with exactly rule, args and side, args a tuple of "
    "nodes and side a tuple of pairs, else 'malformed' (a field the "
    "checker does not know rejects, as in DISCHARGE_RULE).",

    "Rule. At each node, with t the term at that position (e at the root): "
    "the rule the term's head determines is const for Num and Const, var "
    "for Var, neg, add, mul, div for their nodes, pow for Pow with n >= 0, "
    "pow_neg for Pow with n < 0, rpow for RPow, and the builtin's name for "
    "App; there is none for Integral, Deriv, Call and MVar, which rejects "
    "'no-rule'. The node's 'rule' must be that name, else 'wrong-rule'. "
    "The checker dispatches on the TERM, never on the certificate's name: "
    "the name is checked so that a certificate is a readable derivation "
    "and §14's provenance count ('n rule applications over m rules') can "
    "be read off it.",

    "Children. 'args' must have exactly the rule's number of children, "
    "else 'arity', and each is checked, recursively, against the "
    "corresponding child of t (Neg: a; Add, Mul, Div: a then b; Pow: the "
    "base; RPow: the base then the exponent; App: the argument).",

    "Sides. The checker REBUILDS the node's side propositions from t and k "
    "(REG_RULES; a builtin's from the natural-domain table and "
    "REG_C1_EXTRA, never from the certificate). 'side' must have exactly "
    "that many pairs, else 'side-count', and each pair's prop must equal "
    "the rebuilt one as a tree, else 'wrong-side'. Each side is then keyed "
    "terms.with_domain(prop, D), so E5 applies (a closed side such as "
    "sqrt 3 # 0 has domain true), and decided by discharge's own "
    "dispatcher on its cert, exact values first, exactly as DISCHARGE_RULE "
    "decides a child: accepted, or 'child-rejected/<that checker's "
    "reason>'. Sides are never refuted, never tracker entries, and a side "
    "is always keyed at the Reg's whole domain D, so a certificate can "
    "never supply a domain.",

    "Tag. ('reg', cites): the union of the side certificates' cites (their "
    "tags' second components), in the order a pre-order walk first meets "
    "them, a node's own sides before its children's. The exact-value "
    "entries a side used are among its cites, as for any child.",

    "Refusals and depth. A terms.Refused met inside the check (a side's "
    "ring meeting an unstatable Int, say) is a rejection, and a "
    "RecursionError is 'too-deep', as for the other checkers (E30); the "
    "walk is structural recursion on a finite certificate, so it "
    "terminates.",

    "What it does not check, deliberately. It does not check that the "
    "derivation is the only one (there is one per term), that a side is "
    "necessary (sufficient is sound), or anything about the variables: "
    "every rule is side-free at a variable, so no rule depends on which "
    "variable is being integrated (E59).",
)
REG_REASONS = ("class-not-built", "malformed", "no-rule", "wrong-rule",
               "arity", "side-count", "wrong-side", "child-rejected",
               "too-deep")

# E62. Why each rule is sound, in E59's reading, with the standard theorem
# §14 (A) would cite. Every rule has the same shape: if the children are
# C^k on D and the sides hold on D, then the node is C^k on D.
REG_SOUNDNESS = {
    "const": "a constant is C^infinity everywhere",
    "var": "a coordinate function is C^infinity everywhere",
    "neg": "C^0: -1 times a continuous function; C^1: (-u)' = -u'",
    "add": "sums of continuous (C^1) functions are continuous (C^1), on "
           "the common set (neighbourhoods intersected)",
    "mul": "products likewise; C^1 by the product rule, (uv)' = u'v + uv' "
           "continuous",
    "div": "C^0: u/v is continuous wherever v # 0 and u, v are; C^1: v # 0 "
           "at p and v continuous give v # 0 on a neighbourhood, and "
           "(u/v)' = (u'v - uv')/v^2 is continuous there",
    "pow": "u^n = u*...*u (n factors, u^0 = 1), mul's argument n times",
    "pow_neg": "u^n = 1/u^|n| with u # 0, div's argument",
    "rpow": "u^w = exp(w*ln u) with u > 0 (§5.1's reading of e ^ e): exp, "
            "mul and ln's theorems, u > 0 being ln's side",
    "app": "composition f(u): C^0, f is continuous on its natural domain A "
           "(relative topology) and the sides put u(S) inside A, so f o u "
           "is continuous on S; C^1, f is C^1 (analytic) on the open "
           "interior O of A, except abs, which is C^1 on u # 0, and the "
           "strict sides put u(p) in O, hence u(N) in O for a neighbourhood "
           "N of p, so f o u is C^1 on N by the chain rule. The natural "
           "domains are E26's: ln (0, oo), sqrt [0, oo), tan cos u # 0, "
           "asin and acos [-1, 1], acosh [1, oo), atanh (-1, 1), the rest R",
}

# E60. At emission, a Reg key (never ftc's derivative premise, which stays
# DISCHARGE_RULE step (1)) goes through these steps in place of step (2).
REG_DISCHARGE_ORDER = (
    "(2r-a) A Reg skips DISCHARGE_RULE's steps (3) and (4): E7 never sees "
    "a Reg, as now (so its term may hold an Int or D node, which "
    "REG_CHECK_RULE then rejects 'no-rule'), and the exact values apply "
    "inside its sides, not to the Reg itself.",
    "(2r-b) Certify: the untrusted search proposes one reg certificate "
    "(REG_SEARCH_RULE) and the trusted checker decides it: accepted gives "
    "DISCHARGED with ('reg', cites) and the certificate.",
    "(2r-c) Refute (E63): otherwise, the untrusted refuter walks the C^0 "
    "sides of the term's derivation (REG_RULES at every node that has a "
    "rule, pre-order, not descending into a node without one), each keyed "
    "at the Reg's domain, and the first that F1, F2 or F3 decides false "
    "refuses the step 'obligation-decided-false' with "
    "DECIDED_FALSE_MESSAGES_REG['reg_undefined'].",
    "(2r-d) Otherwise ADMITTED, with REG_TAG_RULE's tag and REASON_NONE "
    "when that tag is ('none', ()), else REASON_REJECTED.",
)

# E24's reg row, replaced at the switch (TAG_RULES' second paragraph).
REG_TAG_RULE = (
    "reg. A regularity judgement e in C^k(D) is tagged ('reg', cites) when "
    "its derivation exists (every node of e has a rule, REG_CHECK_RULE) "
    "and every side condition of it, keyed at D, is not tagged none by "
    "this same list (the side's tag, recursively, as sub-obligations are); "
    "cites are the sides' cites in pre-order first use. Otherwise "
    "('none', ()). No other method sees a regularity judgement, and reg "
    "sees nothing else.",
)

# The untrusted search's rule. It is untrusted: whatever it builds, only
# the checker's acceptance discharges (E28).
REG_SEARCH_RULE = (
    "The search walks e as the checker will, builds each node's rule name "
    "from the term's head and each node's side propositions from the same "
    "tables the checker reads (untrusted code reading trusted data, as the "
    "tagger reads ENTRIES), and asks search.propose for each side's "
    "certificate at D. If some node has no rule, or some side has no "
    "certificate, it proposes nothing. It never proposes a certificate for "
    "a key with no derivation, and it does not try alternatives: there is "
    "one derivation per term.",
)

# E64-E66, the formers of §18 Q23 and what changes in E26 (b) and E57.
FORMER_RULE = (
    "Statable. An Integral node is statable when neither limit is PosInf or "
    "NegInf and neither limit holds an Integral or Deriv node "
    "(terms.trees). A Deriv node is always statable.",

    "The Int former. A statable Int[x = a .. b] f at position domain P owes "
    "Reg(f, 0, P + I), I its range as E56 builds it (two rational literals "
    "ordered by norm_num; otherwise the order discharge proves, emitted as "
    "the orientation key, source orient; neither refuses "
    "'orientation-undecided'). Source 'former'. For a top-level integral "
    "with no goal domain this is the key ftc later emits as ftc_f_C0 on "
    "the same range, so the two merge (E8).",

    "The D former. D[x] e at position domain P owes Reg(e, 1, P). Source "
    "'former'. P constrains x where the goal or an enclosing range does, "
    "and is 'true' when nothing does: D[x] x^2 == ?A owes x^2 in "
    "C^1(true).",

    "When. Wherever a term enters the proof and its E6 and E26 formers are "
    "charged (installation's two sides; ftc's new goal; a rewrite's R at "
    "each occurrence; close's value; int_subst's step 14 on the new "
    "integral, its limits and its body; int_flip's new integral; a used "
    "fact's inst values), its Int and D formers are charged too: after "
    "every E6 and E26 former of that term, at the same position domains, "
    "in pre-order among themselves (an outer node before the nodes in its "
    "body). The order is what keeps every existing refusal: a false "
    "E6/E26 former refuses first, as before. An unstatable Int owes "
    "nothing, as E26 (b) had it.",

    "Not recharged. A step that changes an Int's or a D's body without "
    "creating the node (a rewrite at an occurrence inside it, int_subst "
    "replacing an Int nested in a D's body) does not charge the enclosing "
    "node again: the step proves the old body equal to the new one where "
    "the old one's formers were owed, so the new node denotes where the "
    "old one was owed to (§6.1's congruence).",

    "ring and field (E66 (1)). A statable Int and every Deriv node are "
    "opaque atoms, keyed by the node's tree exactly. An unstatable Int is "
    "refused 'Int-or-D-not-normalisable', everywhere ring_nf runs, as "
    "now. The residual renderer prints such an atom as the node itself.",

    "Unchanged (E66 (2)). E7 refuses an obligation holding any Integral or "
    "Deriv node in its proposition or its domain; install's hypothesis "
    "gate refuses a goal hypothesis holding one; deriv's d_const guard "
    "refuses an x-free subterm holding one; SECOND_REVIEW_RULE refuses a "
    "limit holding one. So discharge's checkers, search and refuter never "
    "meet a tree atom through a key, and a Reg's side holding one belongs "
    "to a term with no derivation.",

    "E57 (E66 (3)). REWRITE_RULE step 2a refuses 'Int-or-D-not-normalisable' "
    "when an inst value or the target holds an UNSTATABLE Int; a statable "
    "Int or a D node passes, and its former is charged with R's at step 10 "
    "when R carries it. Step 9 (a): a Reg that step 10 charges from R and "
    "whose proposition or domain mentions x is not open in x.",
)

# E63's message. {key} is terms.show of the Reg, {cond} of the side's key
# (proposition @ domain, or the bare proposition when closed), and {inner}
# the side's own decided-false message, DECIDED_FALSE_MESSAGES' template
# filled as for any key.
DECIDED_FALSE_MESSAGES_REG = {
    "reg_undefined": "{key} is false: its term owes {cond}. {inner}",
}

# _reg_undefined(key, cond, inner) is defined beside _point (section 11b).


# What this step does not cover, each with where it goes.
REG_NOT_COVERED = (
    "Improper integrals: convergence and `diverges` (E65), with "
    "int_improper and readiness P5.",
    "int_parts (E67).",
    "Regularity through an Int node (FTC-1: Int[t = a .. x] g is C^1 in x "
    "where g is C^0; Leibniz for a parameter), a D node (needs C^2) or a "
    "declared symbol (§6.9's hypothesis form, §12.1): no rule, so any Reg "
    "whose term holds one is admitted none. D[y](y*(Int[x = 0 .. 1] 2*x)) "
    "shows it (REG_CASE_CHANGES under_D_constant_integral).",
    "C^1 read one-sided at a closed end: x := t*sqrt t over [0, 1] is "
    "C^1([0, 1]) in §6.4's one-sided sense, and E59's neighbourhood "
    "reading does not certify it (sqrt's C^1 side t > 0 fails at 0). "
    "DESIGN.md §6.4 says such a case 'goes away only with §6.9's "
    "regularity rules, which can state C^1 without differentiating "
    "through the root'; these rules do not, and int_subst's deriv refuses "
    "it first anyway (d_sqrt's t > 0 on the closed range, E38). A "
    "DESIGN.md note, not a soundness matter.",
    "C^2 and up, C^omega: 'class-not-built'.",
)


# --- Certificate helpers ------------------------------------------------------
def _N(rule, *args, side=()):
    """A regularity certificate node (REG_CERTIFICATE)."""
    return {"rule": rule, "args": tuple(args), "side": tuple(side)}


def _REG(tree):
    return {"method": "reg", "tree": tree}


_K = _N("const")
_X = _N("var")
_T2_SQ = _sos("0", [("1", "t", 2)])     # t^2 >= 0 by E20, as P1.1's goal key


def _sqrt_t2(side_cert=_T2_SQ):
    """sqrt(t^2) at C^0: its side t^2 >= 0."""
    return _N("sqrt", _N("pow", _X), side=[("t^2 >= 0", side_cert)])


def _two_t1_1():
    """2*t^1*1, deriv's output for t^2 (E41): no side."""
    return _N("mul", _N("mul", _K, _N("pow", _X)), _K)


# P1.1's F, 2*sin t - 2*t*cos t: (add (mul 2 (sin t)) (neg (mul (mul 2 t)
# (cos t)))). No side at either class.
_F_P11 = _N("add", _N("mul", _K, _N("sin", _X)),
            _N("neg", _N("mul", _N("mul", _K, _X), _N("cos", _X))))


def _F_fallback(k):
    """The fallback's F, 2*sin(sqrt x) - 2*sqrt x * cos(sqrt x): three sqrt
    nodes, each with sqrt's side at class k on the key's own range: x >= 0
    on [0, pi^2/4] (k = 0) or x > 0 on (0, pi^2/4) (k = 1), both by the
    range's lower end."""
    side = [("x >= 0", _RANGE_LO)] if k == 0 else [("x > 0", _RANGE_LO)]

    def sq():
        return _N("sqrt", _X, side=side)
    return _N("add", _N("mul", _K, _N("sin", sq())),
              _N("neg", _N("mul", _N("mul", _K, sq()), _N("cos", sq()))))


def _F_p12(k):
    """P1.2's F, (1/3)*ln(1 + x) - (1/6)*ln(x^2 - x + 1) + (1/sqrt 3)*
    atan((2*x - 1)/sqrt 3), on [0, 1] (k = 0) or (0, 1) (k = 1). Sides in
    pre-order: 3 # 0; 1 + x > 0 (range, lower end); 6 # 0;
    x^2 - x + 1 > 0 (sign, its completed square); sqrt 3 # 0 (cite
    sqrt_pos, E5: domain true); sqrt 3's own 3 >= 0 (k = 0) or 3 > 0
    (k = 1, the interior), literal; the atan argument's divisor sqrt 3 # 0
    and its sqrt again."""
    three = [("3 >= 0", NORM_NUM_LEAF)] if k == 0 else \
        [("3 > 0", NORM_NUM_LEAF)]

    def sq3():
        return _N("sqrt", _K, side=three)
    return _N(
        "add",
        _N("add",
           _N("mul", _N("div", _K, _K, side=[("3 # 0", NORM_NUM_LEAF)]),
              _N("ln", _N("add", _K, _X), side=[("1 + x > 0", _RANGE_LO)])),
           _N("neg", _N("mul",
                        _N("div", _K, _K, side=[("6 # 0", NORM_NUM_LEAF)]),
                        _N("ln", _N("add", _N("add", _N("pow", _X),
                                              _N("neg", _X)), _K),
                           side=[("x^2 - x + 1 > 0", _QUAD)])))),
        _N("mul", _N("div", _K, sq3(), side=[("sqrt 3 # 0", _SQRT3)]),
           _N("atan", _N("div", _N("add", _N("mul", _K, _X), _N("neg", _K)),
                         sq3(), side=[("sqrt 3 # 0", _SQRT3)]))))


# REG_EXPECTED[proof][(prop, dom)] = (tag, certificate): every Reg key of
# every PROOFS proof, each DISCHARGED at the switch. The dom column is the
# judgement's own domain, as FINAL_TRACKER writes it.
_REG_P11_GOAL = ("sin(sqrt(t^2))*(2*t) in C^0([0, pi/2])", "[0, pi/2]")
_REG_SHEET_GOAL = ("sin(sqrt x) in C^0([0, pi^2/4])", "[0, pi^2/4]")
_REG_SHEET_S1 = ("sin(sqrt(t^2))*(2*t^1*1) in C^0([0, pi/2])", "[0, pi/2]")
_REG_P12_GOAL = ("1/(1 + x^3) in C^0([0, 1])", "[0, 1]")
REG_EXPECTED = {
    "P1.1": {
        # new: the goal's integral's former (E64)
        _REG_P11_GOAL: (T_REG_OK, _REG(_N("mul", _N("sin", _sqrt_t2()),
                                          _N("mul", _K, _X)))),
        ("2*sin t - 2*t*cos t in C^0([0, pi/2])", "[0, pi/2]"):
            (T_REG_OK, _REG(_F_P11)),
        ("2*sin t - 2*t*cos t in C^1((0, pi/2))", "(0, pi/2)"):
            (T_REG_OK, _REG(_F_P11)),
        ("sin t * (2*t) in C^0([0, pi/2])", "[0, pi/2]"):
            (T_REG_OK, _REG(_N("mul", _N("sin", _X), _N("mul", _K, _X)))),
    },
    "P1.1-sheet": {
        # new: the sheet's integral's former, the fallback's f premise key
        _REG_SHEET_GOAL: (T_REG_OK, _REG(_N("sin", _N(
            "sqrt", _X, side=[("x >= 0", _RANGE_LO)])))),
        ("t^2 in C^1([0, pi/2])", "[0, pi/2]"):
            (T_REG_OK, _REG(_N("pow", _X))),
        ("sin(sqrt(t^2)) in C^0([0, pi/2])", "[0, pi/2]"):
            (T_REG_OK, _REG(_N("sin", _sqrt_t2()))),
        # new: int_subst's new integral's former (step 14)
        _REG_SHEET_S1: (T_REG_OK, _REG(_N("mul", _N("sin", _sqrt_t2()),
                                          _two_t1_1()))),
        ("2*sin t - 2*t*cos t in C^0([0, pi/2])", "[0, pi/2]"):
            (T_REG_OK, _REG(_F_P11)),
        ("2*sin t - 2*t*cos t in C^1((0, pi/2))", "(0, pi/2)"):
            (T_REG_OK, _REG(_F_P11)),
        ("sin t * (2*t^1*1) in C^0([0, pi/2])", "[0, pi/2]"):
            (T_REG_OK, _REG(_N("mul", _N("sin", _X), _two_t1_1()))),
    },
    "P1.1-fallback": {
        ("2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^0([0, pi^2/4])",
         "[0, pi^2/4]"): (T_REG_OK, _REG(_F_fallback(0))),
        ("2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^1((0, pi^2/4))",
         "(0, pi^2/4)"): (T_REG_OK, _REG(_F_fallback(1))),
        # now emitted first at installation (E64), then by ftc
        _REG_SHEET_GOAL: (T_REG_OK, _REG(_N("sin", _N(
            "sqrt", _X, side=[("x >= 0", _RANGE_LO)])))),
    },
    "P1.2": {
        (P1_2_F + " in C^0([0, 1])", "[0, 1]"):
            (T_REG_SQRT_POS, _REG(_F_p12(0))),
        (P1_2_F + " in C^1((0, 1))", "(0, 1)"):
            (T_REG_SQRT_POS, _REG(_F_p12(1))),
        # now emitted first at installation (E64), then by ftc
        _REG_P12_GOAL: (T_REG_OK, _REG(_N(
            "div", _K, _N("add", _K, _N("pow", _X)),
            side=[("1 + x^3 # 0", _ONE_PLUS_X3)]))),
    },
}
REG_EXPECTED["P1.2-alt"] = dict(REG_EXPECTED["P1.2"])

# What each proof's per-step lists gain (E64): the Int formers, at the step
# where the integral enters, and the `new` flags they flip later.
REG_STEP_ADDS = {
    "P1.1": {"goal": [_REG_P11_GOAL + ((S_FORMER,), DISCHARGED, T_REG_OK,
                                       True)]},
    "P1.1-sheet": {"goal": [_REG_SHEET_GOAL + ((S_FORMER,), DISCHARGED,
                                               T_REG_OK, True)],
                   "s1": [_REG_SHEET_S1 + ((S_FORMER,), DISCHARGED, T_REG_OK,
                                           True)]},
    "P1.1-fallback": {"goal": [_REG_SHEET_GOAL + ((S_FORMER,), DISCHARGED,
                                                  T_REG_OK, True)]},
    "P1.2": {"goal": [_REG_P12_GOAL + ((S_FORMER,), DISCHARGED, T_REG_OK,
                                       True)]},
}
REG_STEP_ADDS["P1.2-alt"] = REG_STEP_ADDS["P1.2"]
# (proof, step) -> keys whose emission there is no longer new: ftc's f
# premise, first emitted at installation now (P1.1's and the sheet's ftc
# see the rewritten integrand, a different key, so nothing flips there).
REG_NOT_NEW = {
    ("P1.1-fallback", "s1"): (_REG_SHEET_GOAL,),
    ("P1.2", "s2"): (_REG_P12_GOAL,),
    ("P1.2-alt", "s2"): (_REG_P12_GOAL,),
}


def _after_regularity(proof, sid, obs, table, adds, not_new):
    """The per-step list under the regularity switch, derived by one rule
    from the post-discharge list: every Reg row DISCHARGED with its tag in
    `table` (asserted admitted and tagged reg before), `new` cleared for
    the keys `not_new` names, then the rows `adds` gives."""
    out = []
    for prop, dom, sources, status, tag, new in obs:
        k = (prop, dom)
        if " in C^" in prop:
            assert status == ADMITTED and tag == T_REG, (proof, sid, k)
            status, tag = DISCHARGED, table[k][0]
        if k in not_new.get((proof, sid), ()):
            assert new, (proof, sid, k)
            new = False
        out.append((prop, dom, sources, status, tag, new))
    return out + list(adds.get(proof, {}).get(sid, ()))


_REG_BASE_OBLIGATIONS = {p: DISCHARGE_OBLIGATIONS[p]
                         for p in ("P1.1", "P1.1-fallback", "P1.2",
                                   "P1.2-alt")}
_REG_BASE_OBLIGATIONS["P1.1-sheet"] = INT_SUBST_OBLIGATIONS["P1.1-sheet"]
REG_OBLIGATIONS = {
    p: {sid: _after_regularity(p, sid, obs, REG_EXPECTED[p], REG_STEP_ADDS,
                               REG_NOT_NEW)
        for sid, obs in steps.items()}
    for p, steps in _REG_BASE_OBLIGATIONS.items()}

# Written out by hand: every key once, final status and tag.
REG_FINAL_TRACKER = {
    "P1.1": [
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("t^2 >= 0", "[0, pi/2]", DISCHARGED, T_SIGN),
        ("0 <= pi/2", "true", DISCHARGED, T_LINEAR_PI),
        ("sin(sqrt(t^2))*(2*t) in C^0([0, pi/2])", "[0, pi/2]", DISCHARGED,
         T_REG_OK),
        ("t >= 0", "[0, pi/2]", DISCHARGED, T_RANGE),
        ("2*sin t - 2*t*cos t in C^0([0, pi/2])", "[0, pi/2]", DISCHARGED,
         T_REG_OK),
        ("2*sin t - 2*t*cos t in C^1((0, pi/2))", "(0, pi/2)", DISCHARGED,
         T_REG_OK),
        ("D[t](2*sin t - 2*t*cos t) == sin t * (2*t)", "(0, pi/2)",
         DISCHARGED, T_DERIV_RING),
        ("sin t * (2*t) in C^0([0, pi/2])", "[0, pi/2]", DISCHARGED,
         T_REG_OK),
    ],
    "P1.1-sheet": [
        ("4 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("x >= 0", "[0, pi^2/4]", DISCHARGED, T_RANGE),
        ("0 <= pi^2/4", "true", DISCHARGED, T_SIGN),
        ("sin(sqrt x) in C^0([0, pi^2/4])", "[0, pi^2/4]", DISCHARGED,
         T_REG_OK),
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("0 <= pi/2", "true", DISCHARGED, T_LINEAR_PI),
        ("0^2 == 0", "true", DISCHARGED, T_RING),
        ("(pi/2)^2 == pi^2/4", "true", DISCHARGED, T_RING),
        ("t^2 in C^1([0, pi/2])", "[0, pi/2]", DISCHARGED, T_REG_OK),
        ("sin(sqrt(t^2)) in C^0([0, pi/2])", "[0, pi/2]", DISCHARGED,
         T_REG_OK),
        ("t^2 >= 0", "[0, pi/2]", DISCHARGED, T_SIGN),
        ("sin(sqrt(t^2))*(2*t^1*1) in C^0([0, pi/2])", "[0, pi/2]",
         DISCHARGED, T_REG_OK),
        ("t >= 0", "[0, pi/2]", DISCHARGED, T_RANGE),
        ("2*sin t - 2*t*cos t in C^0([0, pi/2])", "[0, pi/2]", DISCHARGED,
         T_REG_OK),
        ("2*sin t - 2*t*cos t in C^1((0, pi/2))", "(0, pi/2)", DISCHARGED,
         T_REG_OK),
        ("D[t](2*sin t - 2*t*cos t) == sin t * (2*t^1*1)", "(0, pi/2)",
         DISCHARGED, T_DERIV_RING),
        ("sin t * (2*t^1*1) in C^0([0, pi/2])", "[0, pi/2]", DISCHARGED,
         T_REG_OK),
    ],
    "P1.1-fallback": [
        ("4 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("x >= 0", "[0, pi^2/4]", DISCHARGED, T_RANGE),
        ("0 <= pi^2/4", "true", DISCHARGED, T_SIGN),
        ("sin(sqrt x) in C^0([0, pi^2/4])", "[0, pi^2/4]", DISCHARGED,
         T_REG_OK),
        ("2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^0([0, pi^2/4])",
         "[0, pi^2/4]", DISCHARGED, T_REG_OK),
        ("2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^1((0, pi^2/4))",
         "(0, pi^2/4)", DISCHARGED, T_REG_OK),
        ("D[x](2*sin(sqrt x) - 2*sqrt x * cos(sqrt x)) == sin(sqrt x)",
         "(0, pi^2/4)", DISCHARGED, T_DERIV_FIELD),
        ("x > 0", "(0, pi^2/4)", DISCHARGED, T_RANGE),
        ("2*sqrt x # 0", "(0, pi^2/4)", DISCHARGED, T_PRODUCT_SQRT),
        ("pi^2/4 >= 0", "true", DISCHARGED, T_SIGN),
        ("0 >= 0", "true", DISCHARGED, T_NORM_NUM),
        ("pi/2 >= 0", "true", DISCHARGED, T_LINEAR_PI),
        ("2 # 0", "true", DISCHARGED, T_NORM_NUM),
    ],
    "P1.2": [
        ("1 + x^3 # 0", "[0, 1]", DISCHARGED, T_PRODUCT),
        ("1/(1 + x^3) in C^0([0, 1])", "[0, 1]", DISCHARGED, T_REG_OK),
        ("3 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("6 # 0", "true", DISCHARGED, T_NORM_NUM),
        ("sqrt 3 # 0", "true", DISCHARGED, T_SQRT_POS),
        ("3 >= 0", "true", DISCHARGED, T_NORM_NUM),
        ("1 + x > 0", "[0, 1]", DISCHARGED, T_RANGE),
        ("x^2 - x + 1 > 0", "[0, 1]", DISCHARGED, T_SIGN),
        (P1_2_F + " in C^0([0, 1])", "[0, 1]", DISCHARGED, T_REG_SQRT_POS),
        (P1_2_F + " in C^1((0, 1))", "(0, 1)", DISCHARGED, T_REG_SQRT_POS),
        ("D[x](" + P1_2_F + ") == 1/(1 + x^3)", "(0, 1)", DISCHARGED,
         T_DERIV_FIELD_FACT),
        ("1 + x > 0", "(0, 1)", DISCHARGED, T_RANGE),
        ("x^2 - x + 1 > 0", "(0, 1)", DISCHARGED, T_SIGN),
        ("1 + x # 0", "(0, 1)", DISCHARGED, T_RANGE),
        ("x^2 - x + 1 # 0", "(0, 1)", DISCHARGED, T_SIGN),
        ("1 + ((2*x - 1)/sqrt 3)^2 # 0", "(0, 1)", DISCHARGED, T_SIGN),
        ("1 + x^3 # 0", "(0, 1)", DISCHARGED, T_PRODUCT),
        ("1 + 1 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("1^2 - 1 + 1 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("1 + 0 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("0^2 - 0 + 1 > 0", "true", DISCHARGED, T_NORM_NUM),
        ("3*sqrt 3 # 0", "true", DISCHARGED, T_PRODUCT_SQRT),
        ("2 > 0", "true", DISCHARGED, T_NORM_NUM),
    ],
}
REG_FINAL_TRACKER["P1.2-alt"] = (
    [ob for ob in REG_FINAL_TRACKER["P1.2"] if ob[0] != "3*sqrt 3 # 0"]
    + [("9 # 0", "true", DISCHARGED, T_NORM_NUM)])

# N: zero everywhere. Every proof reads 'Proved.' (E69), which §11.1 and
# §11.2 promised and no build reached until now.
REG_ADMISSIONS = {p: 0 for p in REG_FINAL_TRACKER}
REG_VERDICTS = {p: PROVED for p in REG_FINAL_TRACKER}
# The keys each proof gains, and the Reg count, for the report
REG_NEW_KEYS = {p: [k for k in REG_EXPECTED[p]
                    if any(r[:2] == k for rows in REG_STEP_ADDS.get(p, {})
                           .values() for r in rows)]
                for p in REG_EXPECTED}

# Cross-check on import, as section 11's.
for _p, _rows in REG_FINAL_TRACKER.items():
    _keys = [(r[0], r[1]) for r in _rows]
    assert len(set(_keys)) == len(_keys), _p
    _seen = set()
    for _sid, _obs in REG_OBLIGATIONS[_p].items():
        for _ob in _obs:
            _k = (_ob[0], _ob[1])
            _fin = [r for r in _rows if (r[0], r[1]) == _k]
            assert _fin and _fin[0][2:] == (_ob[3], _ob[4]), (_p, _sid, _ob)
            assert _ob[5] == (_k not in _seen), (_p, _sid, _ob)
        _seen |= {(o[0], o[1]) for o in _obs}
    assert _seen == set(_keys), (_p, set(_keys) ^ _seen)
    assert all(r[2] == DISCHARGED for r in _rows), _p
    assert {k for k in _keys if " in C^" in k[0]} == set(REG_EXPECTED[_p]), _p
    for _k, (_tag, _c) in REG_EXPECTED[_p].items():
        assert [r for r in _rows if (r[0], r[1]) == _k][0][3] == _tag, _k
del _p, _rows, _keys, _seen, _sid, _obs, _ob, _k, _fin, _tag, _c


# --- §18 Q23: the atom algebra and the formers' cases (E64-E67) ---------------
#
# In INT_SUBST_ACCEPTS' shape: goal_emits is installation's list, then each
# move with its own list, to a report. 'certificates' gives every key a
# §5.3 method or regularity discharges, 'reasons' every admission's.
_I_EXP_SIN = "(Int[x = 0 .. pi] exp x * sin x)"
_REG_EXP_SIN = ("exp x * sin x in C^0([0, pi])", "[0, pi]")
_PI_ORDER = _farkas({GOAL: "1", FACT("pi_pos"): "1"})   # 0 <= pi
REG_Q23_CASES = [
    {"id": "solve_for_I_cancels",
     "goal": "2*" + _I_EXP_SIN + " - " + _I_EXP_SIN + " - " + _I_EXP_SIN
             + " == ?A",
     # the three Ints are one key (E8); the range [0, pi] is symbolic, so
     # its order 0 <= pi is decided and emitted first (E56, E68)
     "goal_emits": [
         ("0 <= pi", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI, True),
         _REG_EXP_SIN + ((S_FORMER,), DISCHARGED, T_REG_OK, True)],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "goal_after": None, "emits": [],
     "report": PROVED,
     "theorem": "2*" + _I_EXP_SIN + " - " + _I_EXP_SIN + " - " + _I_EXP_SIN
                + " == 0",
     "certificates": {("0 <= pi", "true"): _PI_ORDER,
                      _REG_EXP_SIN: _REG(_N("mul", _N("exp", _X),
                                            _N("sin", _X)))},
     "was": "refused Int-or-D-not-normalisable by ring (E26 (b))",
     "why": "Q23's first case: 2I - I - I is 0 in Q[I], the atom I's "
            "integrability owed at installation and discharged (exp and sin "
            "are total, so no side)"},
    {"id": "solve_for_I_after_parts",
     # the goal an int_parts step would leave (E67): I rewritten at one of
     # two occurrences of (I + I)/2 into (e^pi + 1) - I, by parts twice
     "goal": "(exp pi + 1 - " + _I_EXP_SIN + " + " + _I_EXP_SIN
             + ")/2 == ?A",
     "goal_emits": [
         ("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM, True),
         ("0 <= pi", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI, True),
         _REG_EXP_SIN + ((S_FORMER,), DISCHARGED, T_REG_OK, True)],
     "move": ("close", {"value": "(exp pi + 1)/2", "check": "ring",
                        "facts": []}),
     "goal_after": None,
     "emits": [("2 # 0", "true", (S_FORMER,), DISCHARGED, T_NORM_NUM,
                False)],
     "report": PROVED,
     "theorem": "(exp pi + 1 - " + _I_EXP_SIN + " + " + _I_EXP_SIN
                + ")/2 == (exp pi + 1)/2",
     "certificates": {("0 <= pi", "true"): _PI_ORDER,
                      _REG_EXP_SIN: _REG(_N("mul", _N("exp", _X),
                                            _N("sin", _X)))},
     "why": "solving for I is ring algebra on the atom once I denotes: "
            "(e^pi + 1 - I + I)/2 = (e^pi + 1)/2, and Int_0^pi e^x sin x "
            "is (e^pi + 1)/2 (SymPy), so the theorem an int_parts proof "
            "would reach is true. E27 accepts the value (exp pi has no "
            "exact value)"},
    {"id": "d_atoms_defined",
     "goal": "D[x] x^2 - D[x] x^2 == ?A",
     "goal_emits": [("x^2 in C^1(true)", "true", (S_FORMER,), DISCHARGED,
                     T_REG_OK, True)],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "goal_after": None, "emits": [],
     "report": PROVED,
     "theorem": "D[x] x^2 - D[x] x^2 == 0",
     "certificates": {("x^2 in C^1(true)", "true"): _REG(_N("pow", _X))},
     "why": "the D former (E64): D[x] x^2 owes x^2 differentiable at every "
            "x, which regularity discharges, and the two atoms cancel"},
    # The two BAD_MOVES cases ring_refuses_D and field_refuses_D, which
    # E66 turns into acceptances owing the false condition (REG_CHANGES).
    {"id": "d_atoms_cancel_undefined",
     "goal": "D[x](abs x) - D[x](abs x) == ?A",
     "goal_emits": [("abs x in C^1(true)", "true", (S_FORMER,), ADMITTED,
                     T_NONE, True)],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "goal_after": None, "emits": [],
     "report": VERDICT.format(n=1),
     "theorem": "D[x](abs x) - D[x](abs x) == 0",
     "reasons": {("abs x in C^1(true)", "true"): REASON_NONE},
     "why": "abs's C^1 side x # 0 @ true has no certificate (tagged none), "
            "and E63 does not refute it: abs has no C^0 side. The theorem "
            "is false at 0, where the left side does not exist, and the "
            "proof says so: 'Proved modulo 1 admissions', the admission "
            "tagged none (§5.4: an admission tagged none may be false)"},
    {"id": "d_atoms_cancel_undefined_field",
     "goal": "D[x](abs x) - D[x](abs x) == ?A",
     "goal_emits": [("abs x in C^1(true)", "true", (S_FORMER,), ADMITTED,
                     T_NONE, True)],
     "move": ("close", {"value": "0", "check": "field", "facts": []}),
     "goal_after": None, "emits": [],
     "report": VERDICT.format(n=1),
     "theorem": "D[x](abs x) - D[x](abs x) == 0",
     "reasons": {("abs x in C^1(true)", "true"): REASON_NONE},
     "why": "the same by field: no divisor in its input"},
]
# Refused, in BAD_MOVES' shape.
REG_Q23_REFUSALS = [
    {"id": "divergent_I_minus_I",
     "goal": "(Int[x = 1 .. oo] 1/x) - (Int[x = 1 .. oo] 1/x) == ?A",
     "setup": [],
     "move": ("close", {"value": "0", "check": "ring", "facts": []}),
     "refusal": "Int-or-D-not-normalisable",
     "goal_emits": [("x # 0", "[1, oo)", (S_FORMER,), DISCHARGED, T_RANGE,
                     True)],
     "certificates": {("x # 0", "[1, oo)"): _RANGE_LO_NZ},
     "why": "Q23's second case, with conv deferred (E65): an improper Int "
            "is unstatable, owes nothing and is not an atom, so ring still "
            "refuses it. Int_1^oo 1/x diverges (SymPy)"},
    {"id": "hypothesis_gate_kept",
     "goal": "1 == ?A @ (Int[t = 0 .. 1] t) > 0", "setup": [],
     "move": ("install", {}),
     "refusal": "Int-or-D-not-normalisable",
     "why": "E66 (2): install's hypothesis gate is unchanged, for a "
            "statable Int too"},
]

# --- E57 after the formers (E66 (3)) -----------------------------------------
REG_E57_CHANGES = {
    # moves from E57_BAD_MOVES to REG_E57_ACCEPTS below
    "E57_BAD_MOVES pyth_erases_D": {
        "old": ("refused", "Int-or-D-not-normalisable"),
        "new": "accepted, and after close 1 'Proved modulo 1 admissions', "
               "owing abs x in C^1(true) tagged none (REG_E57_ACCEPTS)"},
    "E57_BAD_MOVES pyth_erases_divergent_Int": {
        "old": ("refused", "Int-or-D-not-normalisable"),
        "new": ("refused", "Int-or-D-not-normalisable"),
        "why": "unchanged: Int[x = 1 .. oo] 1 is unstatable (E65)"},
    "E57_PRINCIPLE rewrite": "refuses an unstatable Int in an inst value "
                             "or the target (E66 (3)); a statable Int or D "
                             "is owed where it entered and R's at step 10",
    "E57_PRINCIPLE ftc": "its f premise is the Int's former, the same key "
                         "(E64), no longer admitted",
}
REG_E57_ACCEPTS = [
    {"id": "pyth_erases_D",
     "goal": "(sin(D[x](abs x)))^2 + (cos(D[x](abs x)))^2 == ?A",
     "goal_emits": [("abs x in C^1(true)", "true", (S_FORMER,), ADMITTED,
                     T_NONE, True)],
     "move": ("rewrite", {"entry": "pyth", "inst": {"u": "D[x](abs x)"},
                          "at": "(sin(D[x](abs x)))^2"
                                " + (cos(D[x](abs x)))^2"}),
     "occurrences": 1, "goal_after": "1 == ?A", "emits": [],
     "then": [{"move": ("close", {"value": "1", "check": "ring",
                                  "facts": []}),
               "goal_after": None, "emits": []}],
     "report": VERDICT.format(n=1),
     "theorem": "(sin(D[x](abs x)))^2 + (cos(D[x](abs x)))^2 == 1",
     "reasons": {("abs x in C^1(true)", "true"): REASON_NONE},
     "why": "the last review's reproducer: it no longer yields a plain "
            "'Proved.'. The erased D node's definedness was owed at "
            "installation, admitted none because it is false at 0, and it "
            "stays in the verdict"},
    {"id": "pyth_erases_proper_Int",
     "goal": "(sin(Int[x = 0 .. 1] x))^2 + (cos(Int[x = 0 .. 1] x))^2 == ?A",
     "goal_emits": [("x in C^0([0, 1])", "[0, 1]", (S_FORMER,), DISCHARGED,
                     T_REG_OK, True)],
     "move": ("rewrite", {"entry": "pyth",
                          "inst": {"u": "Int[x = 0 .. 1] x"},
                          "at": "(sin(Int[x = 0 .. 1] x))^2"
                                " + (cos(Int[x = 0 .. 1] x))^2"}),
     "occurrences": 1, "goal_after": "1 == ?A", "emits": [],
     "then": [{"move": ("close", {"value": "1", "check": "ring",
                                  "facts": []}),
               "goal_after": None, "emits": []}],
     "report": PROVED,
     "theorem": "(sin(Int[x = 0 .. 1] x))^2 + (cos(Int[x = 0 .. 1] x))^2"
                " == 1",
     "certificates": {("x in C^0([0, 1])", "[0, 1]"): _REG(_X)},
     "why": "a statable Int whose integrability is owed and discharged may "
            "be erased: the identity holds for its value, 1/2"},
    {"id": "pyth_erases_defined_D",
     "goal": "(sin(D[x] x^2))^2 + (cos(D[x] x^2))^2 == ?A",
     "goal_emits": [("x^2 in C^1(true)", "true", (S_FORMER,), DISCHARGED,
                     T_REG_OK, True)],
     "move": ("rewrite", {"entry": "pyth", "inst": {"u": "D[x] x^2"},
                          "at": "(sin(D[x] x^2))^2 + (cos(D[x] x^2))^2"}),
     "occurrences": 1, "goal_after": "1 == ?A", "emits": [],
     "then": [{"move": ("close", {"value": "1", "check": "ring",
                                  "facts": []}),
               "goal_after": None, "emits": []}],
     "report": PROVED,
     "theorem": "(sin(D[x] x^2))^2 + (cos(D[x] x^2))^2 == 1",
     "certificates": {("x^2 in C^1(true)", "true"): _REG(_N("pow", _X))},
     "why": "the D twin: x^2 is C^1 everywhere, so D[x] x^2 denotes at every "
            "x and the rewrite owes nothing more"},
]

# --- Must-reject: the regularity checker called directly ---------------------
#
# DISCHARGE_MUST_REJECT's shape: 'rejects_because' is REG_REASONS' name,
# 'truth' whether the claim holds in E59's reading, 'if_emitted' the
# kernel's outcome when the key is emitted and the search offers its own
# certificate (REG_DISCHARGE_ORDER): ('discharged', tag), ('admitted', tag,
# reason) or ('refused', message).
_SQRTX_C1_CLOSED = ("sqrt x in C^1([0, 1])", "[0, 1]")
REG_MUST_REJECT = [
    {"id": "sqrt_C1_closed_at_zero", "key": _SQRTX_C1_CLOSED,
     "cert": _REG(_N("sqrt", _X, side=[("x > 0", _RANGE_LO)])),
     "rejects_because": "child-rejected",
     "note": "sqrt's C^1 side x > 0 on [0, 1]: (0 - x) + (x - 0) = 0, no "
             "strict constraint (DISCHARGE_MUST_REJECT farkas_nonstrict_"
             "pair's combination)",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("admitted", T_NONE, REASON_NONE)},
    {"id": "sqrt_C1_side_weakened", "key": _SQRTX_C1_CLOSED,
     "cert": _REG(_N("sqrt", _X, side=[("x >= 0", _RANGE_LO)])),
     "rejects_because": "wrong-side",
     "note": "the C^0 side offered for the C^1 claim, with a valid "
             "certificate: only a checker that rebuilds the side from k "
             "refuses it",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("admitted", T_NONE, REASON_NONE)},
    {"id": "sqrt_C0_side_omitted", "key": ("sqrt x in C^0([-1, 1])",
                                           "[-1, 1]"),
     "cert": _REG(_N("sqrt", _X)),
     "rejects_because": "side-count",
     "truth": ("false", {"x": "-1"}),
     "if_emitted": ("refused", _reg_undefined(
         "sqrt x in C^0([-1, 1])", "x >= 0 @ [-1, 1]",
         _point("x >= 0 @ [-1, 1]", "-1 >= 0", x="-1")))},
    {"id": "inv_C0_across_pole", "key": ("1/x in C^0([-1, 1])", "[-1, 1]"),
     "cert": _REG(_N("div", _K, _X, side=[("x # 0", _RANGE_LO_NZ)])),
     "rejects_because": "child-rejected",
     "note": "(0 - x) + (x + 1) = 1, no contradiction",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _reg_undefined(
         "1/x in C^0([-1, 1])", "x # 0 @ [-1, 1]",
         _point("x # 0 @ [-1, 1]", "0 # 0", x="0")))},
    {"id": "div_side_omitted", "key": ("1/x in C^0([-1, 1])", "[-1, 1]"),
     "cert": _REG(_N("div", _K, _X)),
     "rejects_because": "side-count",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _reg_undefined(
         "1/x in C^0([-1, 1])", "x # 0 @ [-1, 1]",
         _point("x # 0 @ [-1, 1]", "0 # 0", x="0")))},
    {"id": "ln_C0_at_zero", "key": ("ln x in C^0([0, 1])", "[0, 1]"),
     "cert": _REG(_N("ln", _X, side=[("x > 0", _RANGE_LO)])),
     "rejects_because": "child-rejected",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _reg_undefined(
         "ln x in C^0([0, 1])", "x > 0 @ [0, 1]",
         _point("x > 0 @ [0, 1]", "0 > 0", x="0")))},
    {"id": "ln_side_omitted", "key": ("ln x in C^0([0, 1])", "[0, 1]"),
     "cert": _REG(_N("ln", _X)),
     "rejects_because": "side-count",
     "note": "accepted by a checker that reads a mutated natural-domain "
             "table (DEFINEDNESS_MUTATIONS no_ln_former): the one-datum "
             "coupling of E61, caught here",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _reg_undefined(
         "ln x in C^0([0, 1])", "x > 0 @ [0, 1]",
         _point("x > 0 @ [0, 1]", "0 > 0", x="0")))},
    {"id": "ln_as_const", "key": ("ln x in C^0([0, 1])", "[0, 1]"),
     "cert": _REG(_K),
     "rejects_because": "wrong-rule",
     "note": "accepted by a checker that dispatches on the certificate's "
             "rule name instead of the term",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _reg_undefined(
         "ln x in C^0([0, 1])", "x > 0 @ [0, 1]",
         _point("x > 0 @ [0, 1]", "0 > 0", x="0")))},
    {"id": "abs_C1_at_zero", "key": ("abs x in C^1([-1, 1])", "[-1, 1]"),
     "cert": _REG(_N("abs", _X, side=[("x # 0", _RANGE_LO_NZ)])),
     "rejects_because": "child-rejected",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("admitted", T_NONE, REASON_NONE)},
    {"id": "abs_C1_side_omitted", "key": ("abs x in C^1([-1, 1])",
                                          "[-1, 1]"),
     "cert": _REG(_N("abs", _X)),
     "rejects_because": "side-count",
     "note": "accepted by a checker without REG_C1_EXTRA, or one that "
             "demands the C^0 sides at k = 1",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("admitted", T_NONE, REASON_NONE)},
    {"id": "composition_leaves_domain",
     "key": ("sqrt(x - 2) in C^0([0, 1])", "[0, 1]"),
     "cert": _REG(_N("sqrt", _N("add", _X, _N("neg", _K)),
                     side=[("x - 2 >= 0", _RANGE_LO)])),
     "rejects_because": "child-rejected",
     "note": "(2 - x, strict) + (x - 0) = 2: the inner x - 2 never enters "
             "sqrt's domain on [0, 1]",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _reg_undefined(
         "sqrt(x - 2) in C^0([0, 1])", "x - 2 >= 0 @ [0, 1]",
         _point("x - 2 >= 0 @ [0, 1]", "0 - 2 >= 0", x="0")))},
    {"id": "asin_inner_leaves_domain",
     "key": ("asin(2*x) in C^0([0, 1])", "[0, 1]"),
     "cert": _REG(_N("asin", _N("mul", _K, _X),
                     side=[("2*x >= -1", _farkas({GOAL: "1", LO(0): "2"})),
                           ("2*x <= 1", _farkas({GOAL: "1", HI(0): "2"}))])),
     "rejects_because": "child-rejected",
     "note": "the first side holds ((-(2x + 1), strict) + 2x = -1); the "
             "second is 2*(1 - x) + (2x - 1) = 1, no contradiction, since "
             "2x leaves [-1, 1] above x = 1/2",
     "truth": ("false", {"x": "1"}),
     "if_emitted": ("refused", _reg_undefined(
         "asin(2*x) in C^0([0, 1])", "2*x <= 1 @ [0, 1]",
         _point("2*x <= 1 @ [0, 1]", "2*1 <= 1", x="1")))},
    {"id": "nested_arg_unchecked",
     "key": ("sin(ln x) in C^0([0, 1])", "[0, 1]"),
     "cert": _REG(_N("sin")),
     "rejects_because": "arity",
     "note": "sin's child omitted, so ln's side is never asked",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _reg_undefined(
         "sin(ln x) in C^0([0, 1])", "x > 0 @ [0, 1]",
         _point("x > 0 @ [0, 1]", "0 > 0", x="0")))},
    {"id": "wrong_rule_name", "key": ("sin x in C^0([0, 1])", "[0, 1]"),
     "cert": _REG(_N("cos", _X)),
     "rejects_because": "wrong-rule",
     "truth": ("true",),
     "if_emitted": ("discharged", T_REG_OK)},
    {"id": "negative_power_as_power",
     "key": ("x^(-1) in C^0([-1, 1])", "[-1, 1]"),
     "cert": _REG(_N("pow", _X)),
     "rejects_because": "wrong-rule",
     "note": "Pow with n < 0 is pow_neg, whose side is x # 0 (§5.1's "
             "spelling symmetry: x^(-1) owes what 1/x owes)",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _reg_undefined(
         "x^(-1) in C^0([-1, 1])", "x # 0 @ [-1, 1]",
         _point("x # 0 @ [-1, 1]", "0 # 0", x="0")))},
    {"id": "rpow_side_omitted",
     "key": ("x^y in C^0(x in [0, 1], y in [1, 2])",
             "x in [0, 1], y in [1, 2]"),
     "cert": _REG(_N("rpow", _X, _X)),
     "rejects_because": "side-count",
     "truth": ("false", {"x": "0", "y": "1"}),
     "if_emitted": ("refused", _reg_undefined(
         "x^y in C^0(x in [0, 1], y in [1, 2])",
         "x > 0 @ x in [0, 1], y in [1, 2]",
         _point("x > 0 @ x in [0, 1], y in [1, 2]", "0 > 0", x="0",
                y="1")))},
    {"id": "int_node_no_rule",
     "key": ("(Int[t = 0 .. 1] t)*x in C^0([0, 1])", "[0, 1]"),
     "cert": _REG(_N("mul", _K, _X)),
     "rejects_because": "no-rule",
     "note": "true (the Int is 1/2), and out of this step: no rule reads "
             "an Int node (REG_NOT_COVERED)",
     "truth": ("true",),
     "if_emitted": ("admitted", T_NONE, REASON_NONE)},
    {"id": "d_node_no_rule",
     "key": ("D[x](abs x) in C^0([-1, 1])", "[-1, 1]"),
     "cert": _REG(_K),
     "rejects_because": "no-rule",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("admitted", T_NONE, REASON_NONE)},
    {"id": "class_omega", "key": ("x in C^omega([0, 1])", "[0, 1]"),
     "cert": _REG(_X),
     "rejects_because": "class-not-built",
     "truth": ("true",),
     "if_emitted": ("admitted", T_NONE, REASON_NONE)},
    {"id": "class_two", "key": ("x in C^2([0, 1])", "[0, 1]"),
     "cert": _REG(_X),
     "rejects_because": "class-not-built",
     "truth": ("true",),
     "if_emitted": ("admitted", T_NONE, REASON_NONE)},
    {"id": "malformed_extra_field", "key": ("x in C^0([0, 1])", "[0, 1]"),
     "cert": {"method": "reg", "tree": _X, "note": "trust me"},
     "rejects_because": "malformed",
     "truth": ("true",),
     "if_emitted": ("discharged", T_REG_OK)},
    {"id": "ftc_F_C1_on_the_closed_range",
     "key": ("2*sin(sqrt x) - 2*sqrt x * cos(sqrt x) in C^1([0, pi^2/4])",
             "[0, pi^2/4]"),
     "cert": _REG(_F_fallback(1)),
     "rejects_because": "child-rejected",
     "note": "the fallback's F claimed C^1 on the CLOSED range: sqrt's "
             "x > 0 fails at 0. ftc never asks this (its C^1 premise is on "
             "(0, pi^2/4), REG_EXPECTED), which is §6.4's split: F may "
             "misbehave at an endpoint, f may not",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("admitted", T_NONE, REASON_NONE)},
]

# The nearest valid neighbours, and the forms no proof exercises.
REG_CHECKER_ACCEPTS = [
    {"id": "sqrt_C0_closed_end", "key": ("sqrt x in C^0([0, 1])", "[0, 1]"),
     "cert": _REG(_N("sqrt", _X, side=[("x >= 0", _RANGE_LO)])),
     "tag": T_REG_OK},
    {"id": "sqrt_C1_open", "key": ("sqrt x in C^1((0, 1))", "(0, 1)"),
     "cert": _REG(_N("sqrt", _X, side=[("x > 0", _RANGE_LO)])),
     "tag": T_REG_OK},
    {"id": "abs_C0_everywhere", "key": ("abs x in C^0([-1, 1])", "[-1, 1]"),
     "cert": _REG(_N("abs", _X)), "tag": T_REG_OK},
    {"id": "abs_C1_off_zero", "key": ("abs x in C^1((0, 1))", "(0, 1)"),
     "cert": _REG(_N("abs", _X, side=[("x # 0", _RANGE_LO_NZ)])),
     "tag": T_REG_OK},
    {"id": "inv_C0_off_pole", "key": ("1/x in C^0([1, 2])", "[1, 2]"),
     "cert": _REG(_N("div", _K, _X, side=[("x # 0", _RANGE_LO_NZ)])),
     "tag": T_REG_OK},
    {"id": "ln_C1_on_a_closed_range", "key": ("ln x in C^1([1, 2])",
                                              "[1, 2]"),
     "cert": _REG(_N("ln", _X, side=[("x > 0", _RANGE_LO)])),
     "tag": T_REG_OK},
    {"id": "asin_C0_closed", "key": ("asin x in C^0([-1, 1])", "[-1, 1]"),
     "cert": _REG(_N("asin", _X, side=[
         ("x >= -1", _RANGE_LO), ("x <= 1", _farkas({GOAL: "1",
                                                      HI(0): "1"}))])),
     "tag": T_REG_OK},
    {"id": "asin_C1_open", "key": ("asin x in C^1((-1, 1))", "(-1, 1)"),
     "cert": _REG(_N("asin", _X, side=[
         ("x > -1", _RANGE_LO), ("x < 1", _farkas({GOAL: "1",
                                                    HI(0): "1"}))])),
     "tag": T_REG_OK},
    {"id": "acosh_C0_closed_end", "key": ("acosh x in C^0([1, 2])",
                                          "[1, 2]"),
     "cert": _REG(_N("acosh", _X, side=[("x >= 1", _RANGE_LO)])),
     "tag": T_REG_OK},
    {"id": "acosh_C1_open", "key": ("acosh x in C^1((1, 2))", "(1, 2)"),
     "cert": _REG(_N("acosh", _X, side=[("x > 1", _RANGE_LO)])),
     "tag": T_REG_OK},
    {"id": "atanh_C1_inside", "key": ("atanh x in C^1([-1/2, 1/2])",
                                      "[-1/2, 1/2]"),
     "cert": _REG(_N("atanh", _X, side=[
         ("x > -1", _RANGE_LO), ("x < 1", _farkas({GOAL: "1",
                                                    HI(0): "1"}))])),
     "tag": T_REG_OK},
    {"id": "tan_by_hypothesis",
     "key": ("tan x in C^0(cos x > 0, x in [0, 1])",
             "cos x > 0, x in [0, 1]"),
     "cert": _REG(_N("tan", _X, side=[("cos x # 0", _member(0))])),
     "tag": ("reg", ())},
    {"id": "rpow_C1", "key": ("x^y in C^1(x in [1, 2], y in [0, 1])",
                              "x in [1, 2], y in [0, 1]"),
     "cert": _REG(_N("rpow", _X, _X, side=[("x > 0", _RANGE_LO)])),
     "tag": T_REG_OK},
    {"id": "negative_power", "key": ("x^(-2) in C^0([1, 2])", "[1, 2]"),
     "cert": _REG(_N("pow_neg", _X, side=[("x # 0", _RANGE_LO_NZ)])),
     "tag": T_REG_OK},
    {"id": "joint_in_parameters",
     "key": ("x*y in C^1(x in [0, 1], y in [0, 1])",
             "x in [0, 1], y in [0, 1]"),
     "cert": _REG(_N("mul", _X, _X)), "tag": T_REG_OK},
    {"id": "d_former_by_hypothesis", "key": ("abs x in C^1(x > 0)", "x > 0"),
     "cert": _REG(_N("abs", _X, side=[("x # 0", _member(0))])),
     "tag": T_REG_OK},
    {"id": "closed_term_constant", "key": ("sqrt 3 in C^1(true)", "true"),
     "cert": _REG(_N("sqrt", _K, side=[("3 > 0", NORM_NUM_LEAF)])),
     "tag": T_REG_OK},
]

# E63 through a move: the FTC-across-a-pole trap, refused by its former
# first and, when the former is lost, by regularity (REG_PLANTED_BUGS
# former_div_dropped and ftc_no_F_formers, where 'as_well' is asserted).
REG_BAD_MOVES = [
    {"id": "ftc_across_pole",
     "goal": "Int[x = -1 .. 1] 1/x^2 == ?A", "setup": [],
     "move": ("install", {}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("x^2 # 0 @ [-1, 1]", "0^2 # 0", x="0"),
     "as_well": _reg_undefined("1/x^2 in C^0([-1, 1])", "x^2 # 0 @ [-1, 1]",
                               _point("x^2 # 0 @ [-1, 1]", "0^2 # 0",
                                      x="0")),
     "why": "the '/' former is charged before the Int's own (E64's order), "
            "so the message is DISCHARGE_BAD_MOVES_ADDED decided_false_"
            "pole's; without that former the Int's former 1/x^2 in "
            "C^0([-1, 1]) is decided false by E63 at the same point "
            "(as_well). Int_-1^1 1/x^2 diverges (SymPy); HolPy's kernel "
            "returned -2 (§4.2)"},
    {"id": "ftc_F_across_pole",
     "goal": "Int[x = -1 .. 1] 1 == ?A", "setup": [],
     "move": ("ftc", {"F": "x + 0*(1/x)", "check": "ring", "facts": []}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("x # 0 @ [-1, 1]", "0 # 0", x="0"),
     "as_well": _reg_undefined("x + 0*(1/x) in C^0([-1, 1])",
                               "x # 0 @ [-1, 1]",
                               _point("x # 0 @ [-1, 1]", "0 # 0", x="0")),
     "why": "an antiderivative undefined at an interior point: F's former "
            "refuses first (E9 (ii)); without it, ftc's F in C^0([-1, 1]) "
            "premise is decided false by E63 (as_well), before deriv"},
    {"id": "ftc_f_not_C0_at_an_end",
     "goal": "Int[x = 0 .. 1] 1/(2*sqrt x) == ?A", "setup": [],
     "move": ("install", {}),
     "refusal": OBLIGATION_DECIDED_FALSE,
     "message": _point("2*sqrt x # 0 @ [0, 1]", "2*0 # 0",
                       entries=("sqrt_zero",), x="0"),
     "as_well": _reg_undefined("1/(2*sqrt x) in C^0([0, 1])",
                               "2*sqrt x # 0 @ [0, 1]",
                               _point("2*sqrt x # 0 @ [0, 1]", "2*0 # 0",
                                      entries=("sqrt_zero",), x="0")),
     "why": "§6.4's other half of the split: f may not misbehave at an "
            "endpoint. The integral is 1, but improper (STAGE0.md S30): F "
            "= sqrt x is C^0 on [0, 1] and C^1 on (0, 1), and f is not C^0 "
            "on [0, 1]. int_improper is its route (E65)"},
]
# The accepted twin of the split: F only C^0 at an end is fine, and that is
# PROOFS' P1.1-fallback (F = 2 sin sqrt x - 2 sqrt x cos sqrt x, C^1 only on
# (0, pi^2/4)), 'Proved.' under REG_EXPECTED; REG_MUST_REJECT
# ftc_F_C1_on_the_closed_range shows the closed claim is not certifiable.

# E63 called on keys directly (item D), each emitted alone at a fresh
# goal's domain: the kernel's outcome for the key.
REG_DECIDED_FALSE = [c for c in REG_MUST_REJECT
                     if c["if_emitted"][0] == "refused"] + [
    {"id": "ln_C1_refuted_by_its_C0_side",
     "key": ("ln x in C^1([0, 1])", "[0, 1]"),
     "if_emitted": ("refused", _reg_undefined(
         "ln x in C^1([0, 1])", "x > 0 @ [0, 1]",
         _point("x > 0 @ [0, 1]", "0 > 0", x="0"))),
     "why": "k = 1 is refuted through the C^0 side, which here is also "
            "the C^1 side"},
    {"id": "pole_integrand", "key": ("1/x^2 in C^0([-1, 1])", "[-1, 1]"),
     "if_emitted": ("refused", _reg_undefined(
         "1/x^2 in C^0([-1, 1])", "x^2 # 0 @ [-1, 1]",
         _point("x^2 # 0 @ [-1, 1]", "0^2 # 0", x="0")))},
    {"id": "f_at_an_end", "key": ("1/(2*sqrt x) in C^0([0, 1])", "[0, 1]"),
     "if_emitted": ("refused", _reg_undefined(
         "1/(2*sqrt x) in C^0([0, 1])", "2*sqrt x # 0 @ [0, 1]",
         _point("2*sqrt x # 0 @ [0, 1]", "2*0 # 0", entries=("sqrt_zero",),
                x="0")))},
]
# Not decided false (E63's C^1-only sides never refute): admitted none.
REG_UNDECIDED = [c["id"] for c in REG_MUST_REJECT
                 if c["if_emitted"][0] == "admitted"] + [
    "f3_irrational_pole_undecided's Int former (REG_CASE_CHANGES)"]


# Install-only cases for the formers' domains (DISCHARGE_UNDECIDED's shape).
REG_INSTALL_CASES = [
    {"id": "d_under_its_own_Int",
     "goal": "Int[x = 0 .. 1] D[x](x^2) == ?A",
     "goal_emits": [
         ("D[x](x^2) in C^0([0, 1])", "[0, 1]", (S_FORMER,), ADMITTED,
          T_NONE, True),
         ("x^2 in C^1([0, 1])", "[0, 1]", (S_FORMER,), DISCHARGED, T_REG_OK,
          True)],
     "certificates": {("x^2 in C^1([0, 1])", "[0, 1]"): _REG(_N("pow", _X))},
     "reasons": {("D[x](x^2) in C^0([0, 1])", "[0, 1]"): REASON_NONE},
     "why": "pre-order: the Int's former first, whose term holds a D node "
            "(no rule, REG_NOT_COVERED: admitted none), then the D's former "
            "at ITS position domain, the Int's range [0, 1] (not true)"},
    {"id": "d_former_with_goal_domain",
     "goal": "D[x](ln x) == ?A @ x > 0",
     "goal_emits": [
         ("x > 0", "x > 0", (S_FORMER,), DISCHARGED, T_HYP, True),
         ("ln x in C^1(x > 0)", "x > 0", (S_FORMER,), DISCHARGED, T_REG_OK,
          True)],
     "certificates": {("x > 0", "x > 0"): _member(0),
                      ("ln x in C^1(x > 0)", "x > 0"):
                          _REG(_N("ln", _X, side=[("x > 0", _member(0))]))},
     "why": "ln's E26 former first, then the D former at the goal's "
            "domain; both by hypothesis"},
]

# --- What changes in the existing cases (E64-E68) ----------------------------
#
# Every table the suite asserts, re-traced by hand. A case not named keeps
# every expected value except that each Reg row it lists becomes DISCHARGED
# with REG_CASE_CERTS' tag (or ADMITTED as REG_CASE_ADMITTED says), and its
# report loses those admissions (a 'Proved modulo 3' that owed only Regs
# reads 'Proved.'). For a named case: 'goal_emits_add' and 'emits_add' are
# rows appended to installation's and the move's lists, 'then_add' to the
# continuation's i-th step; 'not_new' names the keys whose row in that list
# (by 'goal', 'emits' or the step index) is no longer new; 'report' the new
# report. Every added row's key is in REG_CASE_CERTS or REG_CASE_ADMITTED
# (Reg) or has its certificate in 'certificates'.
def _rrow(prop, dom, sources=(S_FORMER,), tag=T_REG_OK, new=True,
          status=DISCHARGED):
    return (prop, dom, sources, status, tag, new)


_ORIENT_PI_HALF = ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI,
                   True)
_KEY_PI_HALF = ("0 <= pi/2", "true")
_RANGE_LO1 = _farkas({GOAL: "1", LO(1): "1"})
# 1 - (cos theta)^2 >= 0 on [0, pi/2], as CONSOLIDATION_CHANGES pins it
_COS_SQ_PRODUCT = _product(
    "-1", [("cos theta - 1", "<=",
            _farkas({GOAL: "1", ATOM("cos_le_one", "theta"): "1"})),
           ("cos theta + 1", ">=",
            _farkas({GOAL: "1", ATOM("cos_ge_neg_one", "theta"): "1"}))])
REG_CASE_CERTS = {
    # MATCH_ACCEPTS
    ("ln(1/x - 1/x + 1) in C^0([1, 2])", "[1, 2]"): (T_REG_OK, _REG(_N(
        "ln", _N("add", _N("add", _N("div", _K, _X,
                                     side=[("x # 0", _RANGE_LO_NZ)]),
                            _N("neg", _N("div", _K, _X,
                                         side=[("x # 0", _RANGE_LO_NZ)]))),
                 _K),
        side=[("1/x - 1/x + 1 > 0", _farkas({GOAL: "1"}))]))),
    ("atan(-ln x) in C^0([1, 2])", "[1, 2]"): (T_REG_OK, _REG(_N(
        "atan", _N("neg", _N("ln", _X, side=[("x > 0", _RANGE_LO)]))))),
    ("atan(-ln(x + y)) in C^0(y > 0, x in [1, 2])", "y > 0, x in [1, 2]"):
        (T_REG_OK, _REG(_N("atan", _N("neg", _N(
            "ln", _N("add", _X, _X),
            side=[("x + y > 0", _farkas({GOAL: "1", REL(0): "1",
                                         LO(1): "1"}))]))))),
    ("t in C^0(y >= 0, t in [0, sqrt y])", "y >= 0, t in [0, sqrt y]"):
        (T_REG_OK, _REG(_X)),
    # OCCURRENCE_CASE
    ("sqrt(t^2) in C^0([0, 1])", "[0, 1]"): (T_REG_OK, _REG(_sqrt_t2())),
    ("sqrt(t^2) in C^0([-1, 0])", "[-1, 0]"): (T_REG_OK, _REG(_sqrt_t2())),
    # INT_SUBST_ACCEPTS (and the case E56_CHANGES moved there)
    ("2*x in C^0([0, 1])", "[0, 1]"): (T_REG_OK, _REG(_N("mul", _K, _X))),
    ("1 - t in C^1([0, 1])", "[0, 1]"): (T_REG_OK, _REG(_N(
        "add", _K, _N("neg", _X)))),
    ("2*(1 - t) in C^0([0, 1])", "[0, 1]"): (T_REG_OK, _REG(_N(
        "mul", _K, _N("add", _K, _N("neg", _X))))),
    ("2*(1 - t)*(0 + (0*t + (-1)*1)) in C^0([0, 1])", "[0, 1]"):
        (T_REG_OK, _REG(_N("mul", _N("mul", _K, _N("add", _K, _N("neg", _X))),
                           _N("add", _K, _N("add", _N("mul", _K, _X),
                                                  _N("mul", _N("neg", _K),
                                                     _K)))))),
    ("t^2 - 2*t in C^0([0, 1])", "[0, 1]"): (T_REG_OK, _REG(_N(
        "add", _N("pow", _X), _N("neg", _N("mul", _K, _X))))),
    ("t^2 - 2*t in C^1((0, 1))", "(0, 1)"): (T_REG_OK, _REG(_N(
        "add", _N("pow", _X), _N("neg", _N("mul", _K, _X))))),
    ("x in C^0([1, 1])", "[1, 1]"): (T_REG_OK, _REG(_X)),
    ("t^2 in C^1([-1, 1])", "[-1, 1]"): (T_REG_OK, _REG(_N("pow", _X))),
    ("t^2 in C^0([-1, 1])", "[-1, 1]"): (T_REG_OK, _REG(_N("pow", _X))),
    ("t^2*(2*t^1*1) in C^0([-1, 1])", "[-1, 1]"): (T_REG_OK, _REG(_N(
        "mul", _N("pow", _X), _two_t1_1()))),
    ("exp x in C^0([0, 1])", "[0, 1]"): (T_REG_OK, _REG(_N("exp", _X))),
    ("ln t in C^1([1, e_const])", "[1, e_const]"): (T_REG_OK, _REG(_N(
        "ln", _X, side=[("t > 0", _RANGE_LO)]))),
    ("exp(ln t) in C^0([1, e_const])", "[1, e_const]"): (T_REG_OK, _REG(_N(
        "exp", _N("ln", _X, side=[("t > 0", _RANGE_LO)])))),
    ("exp(ln t)*(1/t) in C^0([1, e_const])", "[1, e_const]"):
        (T_REG_OK, _REG(_N("mul", _N("exp", _N("ln", _X, side=[
            ("t > 0", _RANGE_LO)])), _N("div", _K, _X, side=[
                ("t # 0", _RANGE_LO_NZ)])))),
    ("cos x in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N("cos",
                                                                  _X))),
    ("pi/2 - t in C^1([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N(
        "add", _N("div", _K, _K, side=[("2 # 0", NORM_NUM_LEAF)]),
        _N("neg", _X)))),
    ("cos(pi/2 - t) in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N(
        "cos", _N("add", _N("div", _K, _K, side=[("2 # 0", NORM_NUM_LEAF)]),
                  _N("neg", _X))))),
    ("-(cos(pi/2 - t)*(0 + (0*t + (-1)*1))) in C^0([0, pi/2])", "[0, pi/2]"):
        (T_REG_OK, _REG(_N("neg", _N(
            "mul", _N("cos", _N("add", _N("div", _K, _K, side=[
                ("2 # 0", NORM_NUM_LEAF)]), _N("neg", _X))),
            _N("add", _K, _N("add", _N("mul", _K, _X),
                             _N("mul", _N("neg", _K), _K))))))),
    ("x in C^0([0, 1])", "[0, 1]"): (T_REG_OK, _REG(_X)),
    ("cos theta in C^1([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N("cos",
                                                                      _X))),
    ("cos theta in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N("cos",
                                                                      _X))),
    ("-(cos theta * (-sin theta * 1)) in C^0([0, pi/2])", "[0, pi/2]"):
        (T_REG_OK, _REG(_N("neg", _N("mul", _N("cos", _X), _N(
            "mul", _N("neg", _N("sin", _X)), _K))))),
    ("(sin theta)^2/2 in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N(
        "div", _N("pow", _N("sin", _X)), _K,
        side=[("2 # 0", NORM_NUM_LEAF)]))),
    ("(sin theta)^2/2 in C^1((0, pi/2))", "(0, pi/2)"): (T_REG_OK, _REG(_N(
        "div", _N("pow", _N("sin", _X)), _K,
        side=[("2 # 0", NORM_NUM_LEAF)]))),
    ("sqrt(1 - x^2) in C^0([0, 1])", "[0, 1]"): (T_REG_OK, _REG(_N(
        "sqrt", _N("add", _K, _N("neg", _N("pow", _X))),
        side=[("1 - x^2 >= 0", _ONE_MINUS_X2)]))),
    ("sqrt(1 - (cos theta)^2) in C^0([0, pi/2])", "[0, pi/2]"):
        (T_REG_COS, _REG(_N("sqrt", _N("add", _K, _N("neg", _N(
            "pow", _N("cos", _X)))), side=[("1 - (cos theta)^2 >= 0",
                                            _COS_SQ_PRODUCT)]))),
    ("-(sqrt(1 - (cos theta)^2)*(-sin theta * 1)) in C^0([0, pi/2])",
     "[0, pi/2]"):
        (T_REG_COS, _REG(_N("neg", _N("mul", _N("sqrt", _N(
            "add", _K, _N("neg", _N("pow", _N("cos", _X)))),
            side=[("1 - (cos theta)^2 >= 0", _COS_SQ_PRODUCT)]),
            _N("mul", _N("neg", _N("sin", _X)), _K))))),
    ("t^2 in C^1([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N("pow", _X))),
    ("sin(sqrt(t^2)) in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N(
        "sin", _sqrt_t2()))),
    _REG_SHEET_GOAL: (T_REG_OK, _REG(_N("sin", _N(
        "sqrt", _X, side=[("x >= 0", _RANGE_LO)])))),
    _REG_SHEET_S1: (T_REG_OK, _REG(_N("mul", _N("sin", _sqrt_t2()),
                                      _two_t1_1()))),
    ("2*x^3 in C^0([-1, 1])", "[-1, 1]"): (T_REG_OK, _REG(_N(
        "mul", _K, _N("pow", _X)))),
    ("x^2 in C^1([-1, 1])", "[-1, 1]"): (T_REG_OK, _REG(_N("pow", _X))),
    ("x^2 in C^0([-1, 1])", "[-1, 1]"): (T_REG_OK, _REG(_N("pow", _X))),
    ("u in C^0([1, 1])", "[1, 1]"): (T_REG_OK, _REG(_X)),
    ("2*x in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N("mul", _K,
                                                                _X))),
    ("-1 in C^0(u in [0, pi^2/4])", "u in [0, pi^2/4]"): (T_REG_OK, _REG(
        _N("neg", _K))),
    ("x^2 in C^1([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N("pow", _X))),
    ("1 in C^0(x in [0, pi/2])", "x in [0, pi/2]"): (T_REG_OK, _REG(_K)),
    # INT_FLIP_ACCEPTS
    ("-(2*x) in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N(
        "neg", _N("mul", _K, _X)))),
    ("-x^2 in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N(
        "neg", _N("pow", _X)))),
    ("-x^2 in C^1((0, pi/2))", "(0, pi/2)"): (T_REG_OK, _REG(_N(
        "neg", _N("pow", _X)))),
    ("sqrt x in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N(
        "sqrt", _X, side=[("x >= 0", _RANGE_LO)]))),
    ("-(sqrt x) in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N(
        "neg", _N("sqrt", _X, side=[("x >= 0", _RANGE_LO)])))),
    # E56_ACCEPTS
    ("sqrt(t^2) in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(
        _sqrt_t2())),
    ("t^2/2 in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N(
        "div", _N("pow", _X), _K, side=[("2 # 0", NORM_NUM_LEAF)]))),
    ("t^2/2 in C^1((0, pi/2))", "(0, pi/2)"): (T_REG_OK, _REG(_N(
        "div", _N("pow", _X), _K, side=[("2 # 0", NORM_NUM_LEAF)]))),
    ("t in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_X)),
    ("x^2 in C^0([0, pi/2])", "[0, pi/2]"): (T_REG_OK, _REG(_N("pow", _X))),
    ("x^2 in C^1((0, pi/2))", "(0, pi/2)"): (T_REG_OK, _REG(_N("pow", _X))),
    # REVIEW_ACCEPTS
    ("1 in C^0(x in [0, 1])", "x in [0, 1]"): (T_REG_OK, _REG(_K)),
    ("1 in C^0(t in [1, e_const])", "t in [1, e_const]"): (T_REG_OK,
                                                           _REG(_K)),
    ("1*(1/t) in C^0([1, e_const])", "[1, e_const]"): (T_REG_OK, _REG(_N(
        "mul", _K, _N("div", _K, _X, side=[("t # 0", _RANGE_LO_NZ)])))),
    ("1 in C^0(u in [0, pi^2/4])", "u in [0, pi^2/4]"): (T_REG_OK, _REG(_K)),
    # E56_REVIEW_CASES
    ("t in C^1(a <= b, y in [a, b], t in [a, y])",
     "a <= b, y in [a, b], t in [a, y]"): (T_REG_OK, _REG(_X)),
    ("1 in C^0(a <= b, y in [a, b], t in [a, y])",
     "a <= b, y in [a, b], t in [a, y]"): (T_REG_OK, _REG(_K)),
    ("1 in C^0(a <= b, y in [a, b], x in [a, y])",
     "a <= b, y in [a, b], x in [a, y]"): (T_REG_OK, _REG(_K)),
    ("1*1 in C^0(a <= b, y in [a, b], t in [a, y])",
     "a <= b, y in [a, b], t in [a, y]"): (T_REG_OK, _REG(_N("mul", _K,
                                                              _K))),
    ("sin 0 in C^0(x in [0, (a - 1)^40])", "x in [0, (a - 1)^40]"):
        (T_REG_OK, _REG(_N("sin", _K))),
    # DISCHARGE_BAD_MOVES_ADDED rewrite_under_D_through_Int_stated
    ("sqrt(t^2) in C^0(0 <= x, t in [0, x])", "0 <= x, t in [0, x]"):
        (T_REG_OK, _REG(_sqrt_t2())),
    # the BAD_MOVES case ftc_check_refuses_D, now accepted
    ("x in C^0([-1, 1])", "[-1, 1]"): (T_REG_OK, _REG(_X)),
    ("x in C^1((-1, 1))", "(-1, 1)"): (T_REG_OK, _REG(_X)),
    # the BAD_MOVES case close_D_goal_scope_passes
    ("x^2 in C^1(true)", "true"): (T_REG_OK, _REG(_N("pow", _X))),
}
# Reg keys in the cases that stay admitted (no derivation), each tagged none.
REG_CASE_ADMITTED = {
    ("y*(Int[x = 0 .. 1] 2*x) in C^1(true)", "true"): (T_NONE, REASON_NONE),
    ("Int[x = a .. y] 1 in C^0(a <= b, y in [a, b])", "a <= b, y in [a, b]"):
        (T_NONE, REASON_NONE),
    ("Int[t = 0 .. x] sqrt(t^2) in C^1(0 <= x)", "0 <= x"):
        (T_NONE, REASON_NONE),
    ("1/((x + pi)/(x + pi) - 1) in C^0([1, 2])", "[1, 2]"):
        (T_NONE, REASON_NONE),
    ("1/(t^2 - 2) in C^0([0, 2])", "[0, 2]"): (T_NONE, REASON_NONE),
    ("abs x in C^1(true)", "true"): (T_NONE, REASON_NONE),
    ("abs x in C^1([-1, 1])", "[-1, 1]"): (T_NONE, REASON_NONE),
    ("1 + (D[x](abs x) - D[x](abs x)) in C^0([-1, 1])", "[-1, 1]"):
        (T_NONE, REASON_NONE),
}

REG_CASE_CHANGES = {
    "MATCH_ACCEPTS": {
        "ring_cancels_inv_atom": {"goal_emits_add": [_rrow(
            "ln(1/x - 1/x + 1) in C^0([1, 2])", "[1, 2]")]},
        "rewrite_R_former_at_position": {"goal_emits_add": [_rrow(
            "atan(-ln x) in C^0([1, 2])", "[1, 2]")]},
        "rewrite_R_former_at_goal_and_range": {"goal_emits_add": [_rrow(
            "atan(-ln(x + y)) in C^0(y > 0, x in [1, 2])",
            "y > 0, x in [1, 2]")]},
        # the Int's range 0 .. sqrt y is used by its former now (E68)
        "limit_former_at_outer_domain": {
            "goal_emits_add": [
                ("0 <= sqrt y", "y >= 0", (S_ORIENT,), DISCHARGED,
                 T_LINEAR_SQRT, True),
                _rrow("t in C^0(y >= 0, t in [0, sqrt y])",
                      "y >= 0, t in [0, sqrt y]")],
            "certificates": {("0 <= sqrt y", "y >= 0"):
                             _farkas({GOAL: "1", SQRT("y"): "1"})}},
        "rewrite_under_infinite_range": {"note": "unchanged: its Int is "
                                                 "improper (E65)"},
    },
    "OCCURRENCE_CASE": {"goal_emits_add": [
        _rrow("sqrt(t^2) in C^0([0, 1])", "[0, 1]"),
        _rrow("sqrt(t^2) in C^0([-1, 0])", "[-1, 0]")]},
    "INT_SUBST_ACCEPTS": {
        "decreasing_literal_ends": {
            "goal_emits_add": [_rrow("2*x in C^0([0, 1])", "[0, 1]")],
            "emits_add": [_rrow("2*(1 - t)*(0 + (0*t + (-1)*1)) in "
                                "C^0([0, 1])", "[0, 1]")],
            "not_new": {0: [("2*(1 - t)*(0 + (0*t + (-1)*1)) in C^0([0, 1])",
                             "[0, 1]")]},
            "report": PROVED},
        "non_monotone_accepted": {
            "goal_emits_add": [_rrow("x in C^0([1, 1])", "[1, 1]")],
            "emits_add": [_rrow("t^2*(2*t^1*1) in C^0([-1, 1])",
                                "[-1, 1]")]},
        "ln_endpoints_by_exact_values": {
            "goal_emits_add": [_rrow("exp x in C^0([0, 1])", "[0, 1]")],
            "emits_add": [_rrow("exp(ln t)*(1/t) in C^0([1, e_const])",
                                "[1, e_const]")]},
        "decreasing_symbolic_ends_flipped": {
            "goal_emits_add": [_ORIENT_PI_HALF,
                               _rrow("cos x in C^0([0, pi/2])",
                                     "[0, pi/2]")],
            "not_new": {"emits": [_KEY_PI_HALF]},
            "emits_add": [_rrow("-(cos(pi/2 - t)*(0 + (0*t + (-1)*1))) in "
                                "C^0([0, pi/2])", "[0, pi/2]")]},
        "cos_theta_canonical": {
            "goal_emits_add": [_rrow("sqrt(1 - x^2) in C^0([0, 1])",
                                     "[0, 1]")],
            "emits_add": [_rrow("-(sqrt(1 - (cos theta)^2)*(-sin theta * 1))"
                                " in C^0([0, pi/2])", "[0, pi/2]",
                                tag=T_REG_COS)]},
        "cos_theta_full": {
            "goal_emits_add": [_rrow("x in C^0([0, 1])", "[0, 1]")],
            "emits_add": [_rrow("-(cos theta * (-sin theta * 1)) in "
                                "C^0([0, pi/2])", "[0, pi/2]")],
            "not_new": {0: [("-(cos theta * (-sin theta * 1)) in "
                             "C^0([0, pi/2])", "[0, pi/2]")]},
            "report": PROVED},
        "sum_second_occurrence": {
            "goal_emits_add": [_rrow("2*x in C^0([0, 1])", "[0, 1]"),
                               _rrow(*_REG_SHEET_GOAL)],
            "emits_add": [_rrow(*_REG_SHEET_S1)]},
        # E61's limit, visible: the D former's term holds an Int
        "under_D_constant_integral": {
            "goal_emits_add": [
                _rrow("y*(Int[x = 0 .. 1] 2*x) in C^1(true)", "true",
                      status=ADMITTED, tag=T_NONE),
                _rrow("2*x in C^0([0, 1])", "[0, 1]")],
            "emits_add": [_rrow("2*(1 - t)*(0 + (0*t + (-1)*1)) in "
                                "C^0([0, 1])", "[0, 1]")]},
        "reverse_non_monotone": {
            "goal_emits_add": [_rrow("2*x^3 in C^0([-1, 1])", "[-1, 1]")],
            "emits_add": [_rrow("u in C^0([1, 1])", "[1, 1]")]},
        # moved here by E56_CHANGES
        "reverse_symbolic_old_range_reversed": {
            "goal_emits_add": [_ORIENT_PI_HALF,
                               _rrow("2*x in C^0([0, pi/2])", "[0, pi/2]")],
            "not_new": {"emits": [_KEY_PI_HALF]},
            "emits_add": [_rrow("-1 in C^0(u in [0, pi^2/4])",
                                "u in [0, pi^2/4]")]},
    },
    "INT_FLIP_ACCEPTS": {
        "flip_reversed_symbolic_to_value": {
            "goal_emits_add": [_ORIENT_PI_HALF,
                               _rrow("2*x in C^0([0, pi/2])", "[0, pi/2]")],
            "emits_add": [
                ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI,
                 False),
                _rrow("-(2*x) in C^0([0, pi/2])", "[0, pi/2]")],
            "not_new": {0: [_KEY_PI_HALF,
                            ("-(2*x) in C^0([0, pi/2])", "[0, pi/2]")]},
            "report": PROVED},
        "flip_sum_second_occurrence": {
            "goal_emits_add": [_rrow("2*x in C^0([0, 1])", "[0, 1]"),
                               _ORIENT_PI_HALF,
                               _rrow("2*x in C^0([0, pi/2])", "[0, pi/2]")],
            "emits_add": [
                ("0 <= pi/2", "true", (S_ORIENT,), DISCHARGED, T_LINEAR_PI,
                 False),
                _rrow("-(2*x) in C^0([0, pi/2])", "[0, pi/2]")],
            # regularity build 2026-09-25, adjudicated: the added row's
            # certificate, which the case's rule requires
            "certificates": {_KEY_PI_HALF: _PI_HALF}},
        "flip_oriented_symbolic_with_former": {
            "goal_emits_add": [_rrow("sqrt x in C^0([0, pi/2])",
                                     "[0, pi/2]")],
            "emits_add": [_rrow("-(sqrt x) in C^0([0, pi/2])",
                                "[0, pi/2]")]},
    },
    "E56_ACCEPTS": {
        "reversed_symbolic_with_former_by_ftc": {
            "goal_emits_add": [_rrow("sqrt(t^2) in C^0([0, pi/2])",
                                     "[0, pi/2]")],
            "report": PROVED},
        "reversed_symbolic_by_ftc_linear": {
            "goal_emits_add": [_ORIENT_PI_HALF,
                               _rrow("2*x in C^0([0, pi/2])", "[0, pi/2]")],
            "not_new": {"emits": [_KEY_PI_HALF,
                                  ("2*x in C^0([0, pi/2])", "[0, pi/2]")]},
            "report": PROVED},
    },
    "REVIEW_ACCEPTS": {
        "forward_constant_body_partial_phi": {
            "goal_emits_add": [_rrow("1 in C^0(x in [0, 1])", "x in [0, 1]")],
            "emits_add": [_rrow("1*(1/t) in C^0([1, e_const])",
                                "[1, e_const]")]},
        "reverse_symbolic_old_range_oriented": {
            "goal_emits_add": [_ORIENT_PI_HALF,
                               _rrow("2*x in C^0([0, pi/2])", "[0, pi/2]")],
            "not_new": {"emits": [_KEY_PI_HALF]},
            "emits_add": [_rrow("1 in C^0(u in [0, pi^2/4])",
                                "u in [0, pi^2/4]")]},
    },
    "E56_REVIEW_CASES": {
        # the outer Int's own former now needs a <= b at installation
        "int_subst_enclosing_range_undecided": {
            "old": ("refused at the int_subst move", "orientation-undecided",
                    {"lo": "a", "hi": "b"}),
            "new": ("refused at installation", "orientation-undecided",
                    {"lo": "a", "hi": "b"})},
        "int_subst_enclosing_range_decided": {
            "goal_emits_add": [
                ("a <= b", "a <= b", (S_ORIENT,), DISCHARGED, T_HYP, True),
                _rrow("Int[x = a .. y] 1 in C^0(a <= b, y in [a, b])",
                      "a <= b, y in [a, b]", status=ADMITTED, tag=T_NONE),
                ("a <= y", "a <= b, y in [a, b]", (S_ORIENT,), DISCHARGED,
                 T_RANGE, True),
                _rrow("1 in C^0(a <= b, y in [a, b], x in [a, y])",
                      "a <= b, y in [a, b], x in [a, y]")],
            "not_new": {"emits": [("a <= b", "a <= b"),
                                  ("a <= y", "a <= b, y in [a, b]")]},
            "emits_add": [_rrow("1*1 in C^0(a <= b, y in [a, b], "
                                "t in [a, y])",
                                "a <= b, y in [a, b], t in [a, y]")],
            "certificates": {("a <= y", "a <= b, y in [a, b]"): _RANGE_LO1}},
        "lazy_unused_range_installs": {
            "goal_emits_add": [
                ("0 <= (a - 1)^40", "true", (S_ORIENT,), DISCHARGED, T_SIGN,
                 True),
                _rrow("sin 0 in C^0(x in [0, (a - 1)^40])",
                      "x in [0, (a - 1)^40]")],
            "certificates": {("0 <= (a - 1)^40", "true"):
                             _sos("0", [("1", "a - 1", 40)])},
            "timing_bound": E56_TIMING_BOUND,
            "note": "E68: the range is used by the Int's own former, so its "
                    "order is decided; the bound stays, a requirement on the "
                    "untrusted search"},
    },
    "E57_BAD_MOVES": {"pyth_erases_D": "moves to REG_E57_ACCEPTS"},
    "DISCHARGE_BAD_MOVES_ADDED": {
        "rewrite_under_D_through_Int_stated": {"goal_emits_add": [
            _rrow("Int[t = 0 .. x] sqrt(t^2) in C^1(0 <= x)", "0 <= x",
                  status=ADMITTED, tag=T_NONE),
            _rrow("sqrt(t^2) in C^0(0 <= x, t in [0, x])",
                  "0 <= x, t in [0, x]")]},
        "field_zero_divisor_opaque": {"goal_emits_add": [
            _rrow("1/((x + pi)/(x + pi) - 1) in C^0([1, 2])", "[1, 2]",
                  status=ADMITTED, tag=T_NONE)]},
    },
    "F3_ROOTS_UNDECIDED": {
        "f3_irrational_pole_undecided": {"goal_emits_add": [
            _rrow("1/(t^2 - 2) in C^0([0, 2])", "[0, 2]", status=ADMITTED,
                  tag=T_NONE)],
            "note": "its div side t^2 - 2 # 0 @ [0, 2] is the former that "
                    "stays admitted none; E63's F3 misses the irrational "
                    "pole as F3 does"},
    },
}

# BAD_MOVES whose outcome changes, old -> new, each traced (E66).
REG_BAD_MOVES_CHANGED = {
    "close_D_goal_scope_passes": {
        "old": ("refused", "Int-or-D-not-normalisable"),
        "new": ("refused", "close-check-failed"),
        "residual": ("D[x] x^2 - 2*x", "ring"),
        "goal_emits": [_rrow("x^2 in C^1(true)", "true")],
        "why": "ring reads D[x] x^2 as an atom (E66 (1)), unrelated to 2*x "
               "(no rule reads a D atom's value), so the check fails, as it "
               "did before E26; the scope check and the whitelist still "
               "pass first, which is what the case is for"},
    "ring_refuses_D": {
        "old": ("refused", "Int-or-D-not-normalisable"),
        "new": "accepted: REG_Q23_CASES d_atoms_cancel_undefined, 'Proved "
               "modulo 1 admissions'"},
    "field_refuses_D": {
        "old": ("refused", "Int-or-D-not-normalisable"),
        "new": "accepted: REG_Q23_CASES d_atoms_cancel_undefined_field"},
    "divisor_test_refuses_D": {
        "old": ("refused", "Int-or-D-not-normalisable"),
        "new": ("refused", "divisor-normalises-to-zero"),
        "why": "E25's ring_nf reads the two D atoms and cancels them: the "
               "divisor is 0 wherever it is defined, and it is refused before "
               "any D former is charged (E64's order)"},
    "match_refuses_D": {
        "old": ("refused", "Int-or-D-not-normalisable"),
        "new": {"goal_emits": [_rrow("abs x in C^1(true)", "true",
                                     status=ADMITTED, tag=T_NONE)],
                "goal_after": "-atan 0 == ?A", "emits": [],
                "reasons": {("abs x in C^1(true)", "true"): REASON_NONE}},
        "why": "step 2a passes a D node (E66 (3)), and step 3's ring_nf "
               "matches -0 against D - D. The D's definedness was owed at "
               "installation, admitted none"},
    "ftc_check_refuses_D": {
        "old": ("refused", "Int-or-D-not-normalisable"),
        "new": {
            "goal_emits": [
                _rrow("1 + (D[x](abs x) - D[x](abs x)) in C^0([-1, 1])",
                      "[-1, 1]", status=ADMITTED, tag=T_NONE),
                _rrow("abs x in C^1([-1, 1])", "[-1, 1]", status=ADMITTED,
                      tag=T_NONE)],
            "goal_after": "1 - -1 == ?A",
            "emits": [
                _rrow("x in C^0([-1, 1])", "[-1, 1]", (S_FTC_C0F,)),
                _rrow("x in C^1((-1, 1))", "(-1, 1)", (S_FTC_C1F,)),
                ("D[x] x == 1 + (D[x](abs x) - D[x](abs x))", "(-1, 1)",
                 (S_FTC_D,), DISCHARGED, T_DERIV_RING, True),
                _rrow("1 + (D[x](abs x) - D[x](abs x)) in C^0([-1, 1])",
                      "[-1, 1]", (S_FTC_C0f,), status=ADMITTED, tag=T_NONE,
                      new=False)],
            "then": [{"move": ("close", {"value": "2", "check": "ring",
                                         "facts": []}),
                      "goal_after": None, "emits": []}],
            "report": VERDICT.format(n=2),
            "theorem": "Int[x = -1 .. 1] (1 + (D[x](abs x) - D[x](abs x)))"
                       " == 2"},
        "why": "the check's ring cancels the D atoms; the integrand's "
               "definedness is owed twice and both are false at 0: its "
               "Int former (a term holding D nodes has no derivation) and "
               "the D former abs x in C^1([-1, 1]), each admitted none. "
               "'Proved modulo 2 admissions', where before E26 it was "
               "'Proved modulo 3' with nothing false visible"},
    "unchanged, re-traced": (
        "every BAD_MOVES case on an improper Int (ring_refuses_Int, "
        "field_refuses_Int, norm_num_refuses_Int, divisor_test_refuses_Int, "
        "match_refuses_Int, ftc_check_refuses_Int, ftc_F_holds_x_free_Int, "
        "ftc_infinite_endpoint): E65",
        "norm_num_refuses_D, norm_num_refuses_open_Int, "
        "norm_num_refuses_Int_in_domain, norm_num_refuses_D_in_domain: E7 "
        "and the hypothesis gate are unchanged, and each refuses before any "
        "Int or D former is charged (E64's order)",
        "ftc_F_contains_D (deriv-no-rule) and ftc_F_holds_x_free_D (E12's "
        "guard): F's formers, now including a D former, are charged first "
        "and discarded with the refused step (E13)",
        "rewrite_under_D, rewrite_under_D_stated, rewrite_under_D_R_closed_"
        "former, rewrite_under_D_R_divisor: they install, owing sqrt(x^2) "
        "in C^1 (admitted none: x^2 > 0 fails at 0) or atan(-x) in C^1 "
        "(discharged), and step 9 refuses as before",
        "rewrite_in_own_endpoint: 0 <= sqrt 1 is decided at installation "
        "now (linear, sqrt_nonneg), and step 6 refuses as before",
        "INT_SUBST_BAD_MOVES and INT_FLIP_BAD_MOVES: every goal installs as "
        "before (each symbolic range's order is decidable, the stated ones "
        "by hypothesis), and each refusal comes before step 14's formers, "
        "except INT_SUBST_BAD_MOVES non_monotone_divergent, whose step-13 "
        "premise 1/t^2 in C^0([-1, 1]) is now refuted by E63 before step 14 "
        "(same code, E63's message; amended in place, regularity build "
        "2026-09-25, adjudicated)",
        "SECOND_REVIEW_BAD_MOVES: an Int with a tree in a limit is "
        "unstatable, owes nothing, and every move still refuses it",
        "F3_ROOTS_CASES, DISCHARGE_BAD_MOVES_ADDED's decided_false_*, "
        "WRONG_ANSWERS, and stage 0's refusals: each refusal is an E6/E26 "
        "former's, a check's or a step's, all before any new emission",
    ),
}

# The suite's own cases in proof_of_life.py (read, not edited): what the
# build must change there, with the reason, as DISCHARGE's 11b did.
REG_SUITE_CHANGES = {
    "SUITE_BAD_MOVES rewrite_inst_shadows": {
        "old": "Int-or-D-not-normalisable (E57's step 2a)",
        "new": "shadowing (rewrite's closing check_goal)",
        "why": "the inst value's Ints are statable, so step 2a passes them "
               "(E66 (3)) and step 3 matches; R carries Int[t = ..] into "
               "Int[t = ..]'s body, which check_goal refuses. BACKSTOPS "
               "rewrite_closing_check_goal still passes, and is now also "
               "reached without its seam"},
    "SUITE_BAD_MOVES rewrite_under_D_through_Int_R_former and _ln": {
        "old": "rewrite-under-D-needs-open-domain",
        "new": "orientation-undecided at installation, {'lo': '1', "
               "'hi': 'x'}",
        "why": "the Int's own former now uses its range [1, x] (E68); the "
               "stated twins REG_BAD_MOVES_ADDED keep step 9 (b) reachable"},
    "BAD_MOVES rewrite_under_D_through_Int_R_former and _ln (data)": {
        "old": "rewrite-under-D-needs-open-domain",
        "new": "orientation-undecided at installation, {'lo': '1', "
               "'hi': 'x'}"},
    "SUITE_BAD_MOVES goal_hyp_holds_Int, goal_hyp_holds_D, "
    "goal_hyp_holds_Int_before_ftc, norm_num_refuses_Int_in_range_domain "
    "and _div, ftc_F_holds_Int_binder, ftc_F_binder_free_in_rhs, "
    "close_value_is_goal_lhs": "unchanged (E66 (2); the last installs "
                               "owing x^2 in C^1(true), discharged, and "
                               "E23 still refuses the value)",
    "ISOLATED_SEAMS, BACKSTOPS": "unchanged",
}
REG_BAD_MOVES_ADDED = [
    {"id": "rewrite_under_D_through_Int_R_former_stated",
     "twin_of": "rewrite_under_D_through_Int_R_former",
     "goal": "D[x](Int[t = 1 .. x] atan(-t)) == ?A @ 1 <= x", "setup": [],
     "move": ("rewrite", {"entry": "atan_odd",
                          "inst": {"u": "t + (sqrt t - sqrt t)"},
                          "at": "atan(-t)"}),
     "refusal": "rewrite-under-D-needs-open-domain",
     "goal_emits": [
         _rrow("Int[t = 1 .. x] atan(-t) in C^1(1 <= x)", "1 <= x",
               status=ADMITTED, tag=T_NONE),
         ("1 <= x", "1 <= x", (S_ORIENT,), DISCHARGED, T_HYP, True),
         _rrow("atan(-t) in C^0(1 <= x, t in [1, x])",
               "1 <= x, t in [1, x]")],
     "certificates": {("1 <= x", "1 <= x"): _member(0),
                      ("atan(-t) in C^0(1 <= x, t in [1, x])",
                       "1 <= x, t in [1, x]"):
                          _REG(_N("atan", _N("neg", _X)))},
     "why": "the hypothesis orders the range, so installation succeeds, "
            "and step 9 (b) refuses R's t >= 0 on the x-dependent [1, x]"},
    {"id": "rewrite_under_D_through_Int_R_former_ln_stated",
     "twin_of": "rewrite_under_D_through_Int_R_former_ln",
     "goal": "D[x](Int[t = 1 .. x] atan(-t)) == ?A @ 1 <= x", "setup": [],
     "move": ("rewrite", {"entry": "atan_odd",
                          "inst": {"u": "t + (ln t - ln t)"},
                          "at": "atan(-t)"}),
     "refusal": "rewrite-under-D-needs-open-domain",
     "why": "the ln twin: R's t > 0 on the closed, x-dependent [1, x]"},
]
REG_CASE_ADMITTED[("Int[t = 1 .. x] atan(-t) in C^1(1 <= x)", "1 <= x")] = \
    (T_NONE, REASON_NONE)

# --- FORGERIES (E69) -----------------------------------------------------------
# print_proved_with_admissions and direct_tracker_write need a finished state
# that still has an admission; P1.1 at s6 now reads 'Proved.'. They move to
# REG_Q23_CASES d_atoms_cancel_undefined after its close (N = 1, the
# admission abs x in C^1(true) tagged none). The suite replays that case's
# goal and move to reach it.
REG_FORGERY_STATE = ("REG_Q23_CASES", "d_atoms_cancel_undefined", "closed")
REG_FORGERY_CHANGES = {
    "direct_tracker_write": {
        "state": REG_FORGERY_STATE,
        "does": "public API only: take the object returned by the state's "
                "public obligations or tracker accessor, and delete the "
                "admission abs x in C^1(true) from it",
        "post": "the accessor again returns that case's final tracker, "
                "[abs x in C^1(true), admitted, ('none', ())], and the "
                "report is 'Proved modulo 1 admissions'"},
    "print_proved_with_admissions": {
        "state": REG_FORGERY_STATE,
        "post": "every report string the kernel produces for the state "
                "equals 'Proved modulo 1 admissions', and 'Proved.' is not "
                "a substring of any captured stdout or report output"},
    "json_roundtrip_state, the handle forgeries": "unchanged; FORGERY_STATE "
        "stays (P1.2, s8), and TRACKER_AT_FORGERY_STATE is derived from "
        "REG_FINAL_TRACKER['P1.2'] as it was from FINAL_TRACKER",
}


# --- Planted bugs: one per checker rule, and for the formers -----------------
#
# DISCHARGE_NEW_PLANTED_BUGS' shape: the mutation, and what must catch it.
# Seams are the architecture's to name (ARCHITECTURE.md §7): each rule a
# small function looked up by name at call time. Locations: (table, id) for
# a case whose expected outcome the bug changes, ('PROPERTY', 'reg') for
# REG_PROPERTY_TEST, ('N', proof) and (proof, step, prop, dom) as
# PLANTED_BUGS read them; 'admissions' where N moves.
REG_PLANTED_BUGS = {
    # the checker, rule by rule
    "reg_side_not_decided": {
        "mutation": "a side condition's certificate is not decided (every "
                    "side accepted)",
        "caught_by": [("REG_MUST_REJECT", "sqrt_C1_closed_at_zero"),
                      ("REG_MUST_REJECT", "inv_C0_across_pole"),
                      ("REG_MUST_REJECT", "ln_C0_at_zero"),
                      ("REG_MUST_REJECT", "abs_C1_at_zero"),
                      ("REG_MUST_REJECT", "composition_leaves_domain"),
                      ("REG_MUST_REJECT", "asin_inner_leaves_domain"),
                      ("REG_MUST_REJECT", "ftc_F_C1_on_the_closed_range"),
                      ("PROPERTY", "reg")]},
    "reg_side_count_unchecked": {
        "mutation": "sides are paired with the rebuilt list without "
                    "checking the count, so a missing side is never asked",
        "caught_by": [("REG_MUST_REJECT", "sqrt_C0_side_omitted"),
                      ("REG_MUST_REJECT", "div_side_omitted"),
                      ("REG_MUST_REJECT", "ln_side_omitted"),
                      ("REG_MUST_REJECT", "abs_C1_side_omitted"),
                      ("REG_MUST_REJECT", "rpow_side_omitted")]},
    "reg_side_from_certificate": {
        "mutation": "a side's proposition is taken from the certificate, "
                    "not rebuilt from the term and k",
        "caught_by": [("REG_MUST_REJECT", "sqrt_C1_side_weakened"),
                      ("PROPERTY", "reg")]},
    "reg_rule_from_certificate": {
        "mutation": "the checker dispatches on the certificate's rule name, "
                    "not on the term's head",
        "caught_by": [("REG_MUST_REJECT", "ln_as_const"),
                      ("REG_MUST_REJECT", "negative_power_as_power"),
                      ("REG_MUST_REJECT", "d_node_no_rule"),
                      ("REG_MUST_REJECT", "wrong_rule_name")]},
    "reg_children_not_walked": {
        "mutation": "only the root node is checked; args is not compared "
                    "with the term's children",
        "caught_by": [("REG_MUST_REJECT", "nested_arg_unchecked"),
                      ("PROPERTY", "reg")]},
    "reg_c1_uses_c0_sides": {
        "mutation": "at k = 1 the builtin's C^0 sides are demanded (no "
                    "interior, no REG_C1_EXTRA)",
        "caught_by": [("REG_MUST_REJECT", "sqrt_C1_side_weakened"),
                      ("REG_MUST_REJECT", "abs_C1_side_omitted")]},
    "reg_no_c1_extra": {
        "mutation": "REG_C1_EXTRA is not read: abs is C^1 everywhere",
        "caught_by": [("REG_MUST_REJECT", "abs_C1_side_omitted")]},
    "reg_div_no_side": {
        "mutation": "div owes no side",
        "caught_by": [("REG_MUST_REJECT", "div_side_omitted")]},
    "reg_negative_power_as_power": {
        "mutation": "Pow with n < 0 is given the pow rule (no side)",
        "caught_by": [("REG_MUST_REJECT", "negative_power_as_power")]},
    "reg_rpow_no_side": {
        "mutation": "rpow owes no side",
        "caught_by": [("REG_MUST_REJECT", "rpow_side_omitted")]},
    "reg_any_class": {
        "mutation": "k is not checked (C^2 and C^omega read as C^1)",
        "caught_by": [("REG_MUST_REJECT", "class_omega"),
                      ("REG_MUST_REJECT", "class_two")]},
    "reg_tree_as_const": {
        "mutation": "an Integral or Deriv node is given the const rule",
        "caught_by": [("REG_MUST_REJECT", "int_node_no_rule"),
                      ("REG_MUST_REJECT", "d_node_no_rule")]},
    "reg_extra_fields_ignored": {
        "mutation": "a certificate field the checker does not know is "
                    "ignored",
        "caught_by": [("REG_MUST_REJECT", "malformed_extra_field")]},
    # untrusted, can only cost admissions or a refusal
    "reg_search_drops_side": {
        "mutation": "the untrusted search omits the last side of every node "
                    "that has one",
        "admissions": {"P1.1": 1, "P1.1-sheet": 3, "P1.1-fallback": 3,
                       "P1.2": 3, "P1.2-alt": 3},
        "caught_by": [("N", "P1.1"), ("N", "P1.1-sheet"),
                      ("N", "P1.1-fallback"), ("N", "P1.2"),
                      ("N", "P1.2-alt")],
        "note": "each rejected Reg is admitted REASON_REJECTED, tagged "
                "('reg', cites) by REG_TAG_RULE (P1.2's F keeps its "
                "sqrt_pos), which the search's bug does not reach: a search "
                "bug costs admissions, never a discharge"},
    "reg_refute_off": {
        "mutation": "E63 never refutes a Reg",
        "caught_by": [("REG_DECIDED_FALSE", c["id"])
                      for c in REG_DECIDED_FALSE]},
    # the formers
    "int_former_not_charged": {
        "mutation": "a statable Int owes no former where it enters",
        "caught_by": [("P1.1", "goal", "sin(sqrt(t^2))*(2*t) in "
                       "C^0([0, pi/2])", "[0, pi/2]"),
                      ("P1.1-sheet", "s1", "sin(sqrt(t^2))*(2*t^1*1) in "
                       "C^0([0, pi/2])", "[0, pi/2]"),
                      ("P1.2", "s2", "1/(1 + x^3) in C^0([0, 1])", "new"),
                      ("REG_Q23_CASES", "solve_for_I_cancels"),
                      ("REG_E57_ACCEPTS", "pyth_erases_proper_Int"),
                      ("E56_REVIEW_CASES", "int_subst_enclosing_range_"
                                           "undecided")],
        "note": "no false 'Proved.' follows in the data: every erased or "
                "atom-read statable Int there is integrable. The worst case "
                "is an atom whose integrand has an irrational pole, which "
                "E6's own former already owes (admitted none)"},
    "d_former_not_charged": {
        "mutation": "a D node owes no former where it enters",
        "caught_by": [("REG_E57_ACCEPTS", "pyth_erases_D"),
                      ("REG_Q23_CASES", "d_atoms_cancel_undefined"),
                      ("REG_Q23_CASES", "d_atoms_defined"),
                      ("REG_INSTALL_CASES", "d_under_its_own_Int")],
        "note": "the case that matters: pyth_erases_D reports a plain "
                "'Proved.' again, the false Proved the consolidation review "
                "found. Its report is what catches it"},
    "d_former_at_goal_domain": {
        "mutation": "a D node's former is charged at the goal's domain, not "
                    "at its position domain",
        "caught_by": [("REG_INSTALL_CASES", "d_under_its_own_Int")]},
    "int_former_charged_first": {
        "mutation": "the Int and D formers are charged before the term's E6 "
                    "and E26 formers",
        "caught_by": [("REG_BAD_MOVES", "ftc_across_pole"),
                      ("REG_BAD_MOVES", "ftc_f_not_C0_at_an_end")],
        "note": "each is refused by E63 with its 'as_well' message instead "
                "of its former's"},
    "former_div_dropped": {
        "mutation": "installation does not charge a '/' former (the seam "
                    "that charges formers, not kernel._owed, so E63's walk "
                    "of the derivation still sees the divisor)",
        "caught_by": [("REG_BAD_MOVES", "ftc_across_pole"),
                      ("REG_BAD_MOVES", "ftc_f_not_C0_at_an_end"),
                      ("P1.2", "goal", "1 + x^3 # 0", "[0, 1]")],
        "expect": "ftc_across_pole and ftc_f_not_C0_at_an_end are still "
                  "refused 'obligation-decided-false', with their 'as_well' "
                  "messages: the FTC-across-a-pole trap refused by "
                  "regularity alone"},
    "ftc_no_F_formers": {
        "mutation": "ftc does not charge F's formers",
        "caught_by": [("REG_BAD_MOVES", "ftc_F_across_pole"),
                      ("P1.2", "s2", "1 + x > 0", "[0, 1]")],
        "expect": "ftc_F_across_pole is still refused, with its 'as_well' "
                  "message (F in C^0([-1, 1]) decided false by E63)"},
    "e57_refuses_nothing": {
        "mutation": "REWRITE_RULE step 2a is dropped",
        "caught_by": [("E57_BAD_MOVES", "pyth_erases_divergent_Int")]},
    "e57_refuses_statable": {
        "mutation": "step 2a still refuses every Int and D node (E57 as it "
                    "stood)",
        "caught_by": [("REG_E57_ACCEPTS", "pyth_erases_D"),
                      ("REG_E57_ACCEPTS", "pyth_erases_proper_Int"),
                      ("REG_E57_ACCEPTS", "pyth_erases_defined_D"),
                      ("REG_BAD_MOVES_CHANGED", "match_refuses_D")]},
    "improper_Int_as_atom": {
        "mutation": "ring and field read an unstatable Int as an atom",
        "caught_by": [("REG_Q23_REFUSALS", "divergent_I_minus_I"),
                      ("BAD_MOVES", "ring_refuses_Int"),
                      ("BAD_MOVES", "field_refuses_Int")],
        "note": "the same patch as DEFINEDNESS_MUTATIONS "
                "ring_reads_Int_as_atom and field_reads_Int_as_atom, which "
                "keep their meaning (REG_BUG_RETRACE)"},
}

# --- The existing planted bugs, mutations and seams under the switch ---------
#
# The rule, applied to every entry of PLANTED_BUGS (with DISCHARGE_PLANTED_
# BUGS), DISCHARGE_NEW_PLANTED_BUGS, DEFINEDNESS_MUTATIONS (with DISCHARGE_
# MUTATION_CHANGES), INT_SUBST_PLANTED_BUGS, INT_SUBST_SEAMS, REVIEW_PLANTED_
# BUGS, CONSOLIDATION_PLANTED_BUGS, E56_PLANTED_BUGS, REVIEW2_PLANTED_BUGS,
# P1_1_SHEET_TRACES and problems/stage0's DISCHARGE_S0_SEAMS: a proof's
# expected N under a bug is its post-discharge N minus the Reg keys that
# proof had (3 for P1.1, P1.1-fallback, P1.2, P1.2-alt and the stage-0
# proofs; 5 for the sheet; 5 for SUB1, SUB2 and QC1, 4 for S2R), because
# every Reg key, old and new, is discharged under the bug exactly as without
# it, EXCEPT where listed below. A bug reaches a Reg's certificate only by
# weakening a side's certificate (a checker bug that rejects, a search bug)
# or the natural-domain table the checker shares with the formers
# (DEFINEDNESS_MUTATIONS' table rows): every one was traced. caught_by is
# unchanged except where listed. Refusals are unchanged: no bug's refused
# step reaches a new emission first.
REG_BUG_RETRACE = {
    # N given, re-traced
    "PLANTED_BUGS / DISCHARGE_PLANTED_BUGS: every 'admissions' of 3": 0,
    "PLANTED_BUGS tracker_drops_one": {
        "admissions": {"P1.1": 0, "P1.1-fallback": 0, "P1.2": 0,
                       "P1.2-alt": 0},
        "drop": [("N", "P1.1"), ("N", "P1.2"), ("N", "P1.2-alt")],
        # regularity build 2026-09-25, adjudicated
        "add": [("P1.2", "s2", "1/(1 + x^3) in C^0([0, 1])", "new"),
                ("P1.2-alt", "s2", "1/(1 + x^3) in C^0([0, 1])", "new")],
        "step_lists_changed": True,
        "why": "its drop keys sin t * (2*t) in C^0 and 1/(1 + x^3) in C^0 "
               "are discharged now, so dropping them no longer moves N; "
               "the FINAL_TRACKER locations still catch it (E69). "
               "1/(1 + x^3) in C^0([0, 1]) is now first emitted at "
               "installation, and the wrapper drops every emission of it, "
               "so at s2 the key is absent from the tracker before the "
               "step and ftc's row reads new, where REG_NOT_NEW makes it "
               "not new (KEYING: new is read from the tracker): the step "
               "lists now catch it at P1.2's and P1.2-alt's s2, and "
               "PLANTED_BUGS' 'step_lists_changed': False no longer holds. "
               "Its other drop keys are emitted once each (t >= 0 at P1.1's "
               "s1, sin t * (2*t) in C^0 at P1.1's s2, 1 + x^3 # 0 at P1.2's "
               "installation), so no other list changes"},
    # regularity build 2026-09-25, adjudicated
    "INT_SUBST_PLANTED_BUGS int_subst_no_orientation": {
        "drop": [("INT_SUBST_BAD_MOVES", "orientation_undecided")],
        "why": "with step 8's orientation skipped and the limits kept, step "
               "14's new integral Int[t = 0 .. 1/y] still owes its own "
               "former (E64), which uses its range, so E68 decides the order "
               "there and refuses 'orientation-undecided' naming 0 and 1/y: "
               "the case's own code and message, so the case no longer sees "
               "the mutation. It stays caught at decreasing_symbolic_ends_"
               "flipped and cos_theta_full (the unflipped new integral). "
               "int_subst_flips_without_decision keeps that location: its "
               "flipped Int[t = 1/y .. 0] refuses naming 1/y and 0, a "
               "different message"},
    "REVIEW2_PLANTED_BUGS rewrite_tree_branch_skips_E57": {
        "drop": [("E57_BAD_MOVES", "pyth_erases_D")],
        "why": "REG_E57_CHANGES moves pyth_erases_D to REG_E57_ACCEPTS, "
               "where a D node passes step 2a on every branch (E66 (3)), so "
               "the mutation changes nothing there; it stays caught at "
               "pyth_erases_divergent_Int, whose Int is unstatable"},
    "DISCHARGE_NEW_PLANTED_BUGS search_scales_wrongly": {
        "admissions": {"P1.1-fallback": 1, "P1.2": 0, "P1.2-alt": 0},
        "why": "P1.1 and the sheet are still refused (orientation-"
               "undecided); the fallback keeps pi/2 >= 0 REASON_REJECTED; no "
               "P1 Reg side uses a fact label (they are range, sign, cite "
               "and literal certificates), so every Reg is discharged"},
    "DISCHARGE_NEW_PLANTED_BUGS farkas_swaps_interval_ends": {
        "admissions": {"P1.1": 1, "P1.1-sheet": 3, "P1.1-fallback": 6,
                       "P1.2": 0, "P1.2-alt": 0},
        "why": "a range certificate using a lower end is rejected where the "
               "upper end is not rational (its note): P1.1's t >= 0; the "
               "sheet's x >= 0 and t >= 0, and its Int former sin(sqrt x) "
               "in C^0([0, pi^2/4]), whose side x >= 0 is range; the "
               "fallback's x >= 0, x > 0 and 2*sqrt x # 0, and its three "
               "Regs, all with range sides on pi^2/4. P1.2's [0, 1] is "
               "not caught, as before. caught_by keeps ('N', 'P1.1') and "
               "('N', 'P1.1-fallback'); P1_1_SHEET_TRACES' N 7 -> 3"},
    "DISCHARGE_MUTATION_CHANGES sqrt_open_at_0": {
        "admissions": {"P1.2": 0, "P1.2-alt": 0},
        "why": "the shared table makes sqrt's C^0 side u > 0 too, and P1.2's "
               "sqrt 3 owes 3 > 0 in both its former and its Reg sides: "
               "literal, true. P1.1, the fallback and the sheet are refused "
               "at installation, as before"},
    "E56_CHANGES pi_pos_not_in_constraint_set": {
        "admissions": {"P1.1": 0, "P1.1-fallback": 0, "P1.2": 0,
                       "P1.2-alt": 0, "P1.1-sheet": 0}},
    "INT_SUBST_SEAMS no_sqrt_former, d_ln_emits_nothing": {
        "admissions": {"P1.1-sheet": 0}},
    "P1_1_SHEET_TRACES": "every N 5 -> 0; farkas_swaps_interval_ends 7 -> 3",
    "problems/stage0 DISCHARGE_S0_SEAMS": "every N 3 -> 0",
    # the table mutations, now read by the checker too (E61)
    "DEFINEDNESS_MUTATIONS, the 19 table rows": {
        "rule": "N 0 for every proof the mutation does not refuse: the "
                "search builds its sides from the mutated table and the "
                "checker demands exactly those, so each Reg is discharged "
                "with the mutated sides. Each keeps its caught_by, and the "
                "row removals gain REG_MUST_REJECT's side-omitted cases",
        "add": {"no_ln_former": [("REG_MUST_REJECT", "ln_side_omitted")],
                "no_sqrt_former": [("REG_MUST_REJECT",
                                    "sqrt_C0_side_omitted")]},
        "drop": {"no_sqrt_former": [
            ("P1.1", "goal", "0 <= pi/2", "true"),
            ("P1.1", "s1", "0 <= pi/2", "new"),
            ("P1.1-fallback", "goal", "0 <= pi^2/4", "true"),
            ("P1.1-fallback", "s1", "0 <= pi^2/4", "new")]},
        "why": "no_sqrt_former's orientation catches relied on sqrt's "
               "former being the only key that used the range at "
               "installation; the Int's own former uses it now (E64), so "
               "the orientation is emitted at installation under the "
               "mutation too. Its other locations still catch it"},
    "INT_SUBST_SEAMS no_sqrt_former": {
        "drop": [("P1.1-sheet", "goal", "0 <= pi^2/4", "true")]},
    "P1_1_SHEET_TRACES no_sqrt_former": {
        "drop": [("P1.1-sheet", "goal", "0 <= pi^2/4", "true")]},
    "DEFINEDNESS_MUTATIONS ring_reads_D_as_atom, field_reads_D_as_atom": {
        "retire": True,
        "why": "vacuous after the switch: the kernel itself reads every D "
               "node as an atom (E66 (1)), so the patched normaliser is the "
               "unpatched one and nothing can catch it. Retired with a "
               "DATA_CHANGES entry, not deleted silently. E57's and the "
               "formers' own bugs (REG_PLANTED_BUGS d_former_not_charged, "
               "e57_refuses_statable) are what now guard D nodes"},
    "DEFINEDNESS_MUTATIONS ring_reads_Int_as_atom, field_reads_Int_as_atom": {
        "why": "kept: after the switch they differ from the kernel only on "
               "an unstatable Int, and every caught_by case uses one "
               "(Int[x = 0 .. oo] 1); REG_PLANTED_BUGS improper_Int_as_atom "
               "is the same patch named for this step"},
    "DEFINEDNESS_MUTATIONS norm_num_admits_Int": {
        "note": "caught_by unchanged. Under it norm_num_refuses_open_Int "
                "installs past E7 and is then refused 'orientation-"
                "undecided' by its Int's own former (0 .. x undecided): "
                "still a changed outcome"},
    "DEFINEDNESS_MUTATIONS deriv_d_const_on_Int_or_D": {
        "note": "caught_by unchanged: with the guard off both ftc steps are "
                "accepted, their Reg premises admitted none (a term holding "
                "an Int or D has no derivation)"},
    "INT_SUBST_PLANTED_BUGS int_subst_C0_on_original_integrand": {
        "note": "under it the forward C^0 premise is the old integrand on "
                "the old range, which is now the Int's own former from "
                "installation (sheet: sin(sqrt x) in C^0([0, pi^2/4])), so "
                "at s1 it is emitted not new; its catches (the s1 lists) "
                "still differ"},
    "every other entry": "N as the rule gives; caught_by, refusals and "
                         "retags unchanged (each traced: checker bugs that "
                         "only accept more discharge no Reg less, and "
                         "CONSOLIDATION_PLANTED_BUGS' atom-fact bugs "
                         "strengthen QC1's cos sides, never reject them)",
}

# --- The property test (E34's, extended) --------------------------------------
REG_PROPERTY_TEST = (
    "Family 'reg', for kernel/test_discharge.py, on its own seeded stream: "
    "random terms over one variable x built from the rules (literals, x, "
    "neg, add, mul, div, pow with n in -2..3, and the sixteen builtins), "
    "depth up to 4, on a random interval with rational ends, open or "
    "closed, and k in {0, 1}. For each key the search's certificate, if "
    "the checker accepts it, is tested at the interval's rational points "
    "(its ends where closed, its midpoint, and 16 more): every side "
    "condition of the derivation must hold there, evaluated exactly where "
    "the term is a rational function and with math-module floats and a "
    "1e-9 margin otherwise, and for k = 1 at points a margin inside the "
    "open ends as well. An accepted key whose sides fail anywhere is a "
    "soundness failure. The same keys with each certificate mutated (a side "
    "dropped, a side's proposition weakened >= for >, a child's rule "
    "renamed) must be rejected. Counts: 2,000 keys, as the other families.",
)

# --- The switch (E70) ------------------------------------------------------------
REG_SWITCH = (
    "Commit 1: the checker in discharge.py, one function per REG_CHECK_RULE "
    "paragraph (the seams REG_PLANTED_BUGS names), reading the "
    "natural-domain table the formers read, from wherever the build puts it "
    "so that both see one object (DEFINEDNESS_MUTATIONS' patch must reach "
    "both); the search's REG_SEARCH_RULE; E63 in refute.py; REG_TAG_RULE in "
    "the tagger. test_discharge.py gains REG_MUST_REJECT, "
    "REG_CHECKER_ACCEPTS, REG_DECIDED_FALSE and every certificate in "
    "REG_EXPECTED, REG_CASE_CERTS and problems/stage0's REG_EXPECTED, each "
    "handed to the checker directly, the search's own certificate for each "
    "compared node by node, and REG_PROPERTY_TEST. Nothing is wired into "
    "kernel._emit, so items 1-7 still assert the current tables; the suite "
    "stays green.",

    "Commit 2: the wiring (REG_DISCHARGE_ORDER in _emit), the Int and D "
    "formers (FORMER_RULE), ring and field's atoms, E57's relaxation, and in "
    "the same commit the suite asserts, for both data files: REG_OBLIGATIONS "
    "for the per-step lists, REG_FINAL_TRACKER, REG_ADMISSIONS and "
    "REG_VERDICTS; each Reg's certificate (REG_EXPECTED) and every "
    "admission's reason; REG_CASE_CHANGES, REG_BAD_MOVES_CHANGED, "
    "REG_E57_CHANGES and REG_SUITE_CHANGES applied to the tables they name; "
    "REG_Q23_CASES, REG_Q23_REFUSALS, REG_E57_ACCEPTS, REG_INSTALL_CASES, "
    "REG_BAD_MOVES (with 'as_well' asserted under former_div_dropped and "
    "ftc_no_F_formers) and REG_BAD_MOVES_ADDED; REG_FORGERY_CHANGES; "
    "REG_PLANTED_BUGS and REG_BUG_RETRACE in child processes; "
    "DECIDED_FALSE_MESSAGES_REG among the messages; SOURCES['former'], "
    "DISCHARGE_METHODS and TAG_RULES' reg row as REG_TEXT_CHANGES gives "
    "them. The no-none assertion over PROOFS runs and every E24 tag "
    "assertion stay. One constant in proof_of_life.py switches it, never a "
    "kernel file, and no kernel file imports either data file.",

    "The pre-regularity tables stay in both files as the record and are no "
    "longer asserted; retiring them later is a DATA_CHANGES entry. "
    "REASON_REG is then no longer produced by the kernel.",
)

# Text that changes at the switch (the build edits the data's prose it
# asserts nothing of; listed so the change is reviewed, not incidental).
# The first four were applied in place by the regularity build adjudication
# (2026-09-25); the rest are read with FORMER_RULE and REG_DISCHARGE_ORDER.
REG_TEXT_CHANGES = {
    "SOURCES['former']": "adds: a statable Int owes its integrand in C^0 on "
                         "its range, and a D[x] e owes e in C^1 at its "
                         "position domain (E64)",
    "DISCHARGE_METHODS": "gains DISCHARGE_METHODS_REG['reg']",
    "ADMISSION_METHODS['reg']": "'§6.9 closure rules, checked (E60); an "
                                "admitted Reg is tagged none or reg by "
                                "REG_TAG_RULE'",
    "TAG_RULES, the reg paragraph": "replaced by REG_TAG_RULE",
    "DISCHARGE_RULE, scope and step (2)": "a Reg is decided by "
                                          "REG_DISCHARGE_ORDER",
    "E26 (b) comment, E7, REWRITE_RULE steps 5 and 9, E57_RULE": "read with "
        "FORMER_RULE's E66 paragraphs",
}


# ---------------------------------------------------------------------------
# 18. The regularity review (regularity review 2026-09-25)
#
# A skeptic of the regularity build (eeb1a8b) found no false 'Proved.', one
# suite gap, one intended-but-unstated behaviour and one crash. Specified
# before any code; staged (REG_REVIEW_SWITCH).

# The suite gap: no REG_MUST_REJECT side certificate referenced a domain
# item, so a checker that decided each side on D + (the side itself) passed
# every case (the skeptic's M3). The rule, stated so the build can assert
# it, and two cases that fail under M3.
REG_SIDE_KEY_RULE = (
    "Every side condition a regularity certificate carries is decided on "
    "exactly the key terms.with_domain(prop, key.dom): the Reg's own domain "
    "tuple, unchanged, with nothing appended (never the side itself, an "
    "earlier side, or the parent's children's sides), and E5 alone may "
    "shorten it (to true, for a closed side). So an item index in a side's "
    "hyp or farkas certificate ranges over key.dom only, and one past its "
    "end is 'unknown-item'. The build asserts it directly: for every side "
    "of every certificate in REG_EXPECTED (both files), REG_CASE_CERTS and "
    "REG_CHECKER_ACCEPTS, the key the checker decides equals "
    "with_domain(prop, key.dom) as a tree (REG_CHECK_RULE, Sides, which "
    "already says 'a side is always keyed at the Reg's whole domain D').",
)
REG_REVIEW_MUST_REJECT = [
    {"id": "side_assumes_itself_pole",
     "key": ("1/x in C^0([-1, 1])", "[-1, 1]"),
     "cert": _REG(_N("div", _K, _X, side=[("x # 0", _member(1))])),
     "rejects_because": "child-rejected/unknown-item",
     "note": "the domain has one item, [-1, 1], at index 0; member 1 names "
             "the side x # 0 itself only if the checker appended it (M3)",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("refused", _reg_undefined(
         "1/x in C^0([-1, 1])", "x # 0 @ [-1, 1]",
         _point("x # 0 @ [-1, 1]", "0 # 0", x="0")))},
    {"id": "side_assumes_itself_sqrt_C1",
     "key": _SQRTX_C1_CLOSED,
     "cert": _REG(_N("sqrt", _X, side=[("x > 0", _member(1))])),
     "rejects_because": "child-rejected/unknown-item",
     "note": "the C^1 twin: x > 0 assumed from itself would certify sqrt x "
             "C^1 at 0",
     "truth": ("false", {"x": "0"}),
     "if_emitted": ("admitted", T_NONE, REASON_NONE)},
]
# The contrast, already pinned: REG_CHECKER_ACCEPTS tan_by_hypothesis and
# d_former_by_hypothesis certify a side by hyp member 0, a real item of D.

# The minor, pinned as intended (E63's amendment).
REG_REVIEW_DECIDED_FALSE = [
    {"id": "vacuous_domain_closed_side",
     "key": ("sqrt(-1) + x in C^0(x > 1, x < 0)", "x > 1, x < 0"),
     "if_emitted": ("refused", _reg_undefined(
         "sqrt(-1) + x in C^0(x > 1, x < 0)", "-1 >= 0",
         _negation("-1 >= 0", "-1 < 0", T_NORM_NUM))),
     "why": "the domain is empty, so the claim is vacuously true, but the "
            "side -1 >= 0 is closed and E5 keys it at true; it is literal "
            "as emitted, so F1 (which needs the exact values to change it) "
            "does not apply, and F2 decides it: its negation -1 < 0 is "
            "discharged by norm_num. Consistent with E7, which refuses the "
            "same former wherever sqrt(-1) enters"},
]

# The crash: kernel._discharge_reg's _frozen(cert) is recursive and raised
# RecursionError out of install at term depth ~330-600. The build makes it
# iterative and maps a RecursionError anywhere in a Reg's search, check or
# refutation to 'no certificate' (ARCHITECTURE.md §5's rule for a key
# deeper than the stack). Each goal installs, with no exception and no
# refusal; it owes exactly one obligation, its Int's former (the integrand
# owes no E6/E26 former, and the range is literal, so no orientation).
_DEEP_SUM = " + ".join("x^%d" % i for i in range(400))
_DEEP_SIN = "sin " * 350 + "x"      # juxtaposed: sin(sin(...)) is D6's
_DEEP_SIN_300 = "sin " * 300 + "x"  # form, but see REG_REVIEW_NOTES
REG_DEEP_ADMIT_REASONS = (REASON_NONE, REASON_REJECTED)
REG_REVIEW_DEEP_CASES = [
    {"id": "deep_sum_400",
     "goal": "Int[x = 0 .. 1] " + _DEEP_SUM + " == ?A",
     "outcome": "installs",
     "emits_one": (_DEEP_SUM + " in C^0([0, 1])", "[0, 1]", (S_FORMER,)),
     "status": ("discharged", T_REG_OK, "or admitted, reason in "
                "REG_DEEP_ADMIT_REASONS, when the derivation is deeper than "
                "the stack"),
     "report": "Open: the goal as installed",
     "was": "RecursionError out of install (the skeptic; committed "
            "eeb1a8b, reproduced 2026-09-25)",
     "why": "the certificate's depth follows the left-nested sum, 400 add "
            "nodes; every rule is side-free here (pow with n >= 0, E58's "
            "x^0 included), so a derivation that fits the stack is "
            "accepted ('reg', ()). Whether it fits is the stack's business "
            "(ARCHITECTURE.md §5), so the case asserts no exception, the one "
            "key, and one of the two statuses; the build records which on "
            "its machine"},
    {"id": "deep_sin_350",
     "goal": "Int[x = 0 .. 1] " + _DEEP_SIN + " == ?A",
     "outcome": "installs",
     "emits_one": (_DEEP_SIN + " in C^0([0, 1])", "[0, 1]", (S_FORMER,)),
     "status": ("discharged", T_REG_OK, "or admitted, reason in "
                "REG_DEEP_ADMIT_REASONS"),
     "report": "Open: the goal as installed",
     "was": "RecursionError out of install (reproduced 2026-09-25)",
     "why": "350 nested sin nodes, total, side-free"},
    {"id": "deep_sin_300_control",
     "goal": "Int[x = 0 .. 1] " + _DEEP_SIN_300 + " == ?A",
     "outcome": "installs",
     "emits_one": (_DEEP_SIN_300 + " in C^0([0, 1])", "[0, 1]",
                   (S_FORMER,)),
     "status": ("discharged", T_REG_OK),
     "report": "Open: the goal as installed",
     "why": "the control: at depth 300 the committed kernel installs and "
            "discharges the former (checked 2026-09-25), so the fix must "
            "keep that"},
]

REG_REVIEW_PLANTED_BUGS = {
    "reg_side_assumes_itself": {
        "mutation": "each side is decided on D + (prop,) instead of D (the "
                    "skeptic's M3, in the checker's side function)",
        "caught_by": [("REG_REVIEW_MUST_REJECT", "side_assumes_itself_pole"),
                      ("REG_REVIEW_MUST_REJECT",
                       "side_assumes_itself_sqrt_C1")]},
}

REG_REVIEW_NOTES = (
    "Not a regularity matter, for the main session: the parser raises "
    "RecursionError on sin(...) nested with parentheses 200 deep "
    "(Int[x = 0 .. 1] sin(sin(...(x))) == ?A, reproduced 2026-09-25), where "
    "the juxtaposed sin sin ... x parses at 350. The parser is trusted "
    "(§15.2 item 8) and E21 reads an exception out of it as a crash, not a "
    "refusal. That is why the deep cases above are written juxtaposed.",
)

REG_REVIEW_CHANGES = {
    "expected values": "none change: the two must-reject cases and the "
                       "vacuous case already behave as stated on eeb1a8b; "
                       "the deep cases change a crash into an install",
    "DECISIONS E63": "amended (the vacuous closed-side refusal, intended)",
    "test_discharge.py's count of REG_MUST_REJECT (22)": "unchanged: the "
        "new cases are their own table, asserted the same way",
}
REG_REVIEW_SWITCH = (
    "One commit: kernel._discharge_reg's freeze made iterative, and a "
    "RecursionError in a Reg's search, check or refutation read as no "
    "certificate. The suite asserts REG_REVIEW_MUST_REJECT as "
    "REG_MUST_REJECT is asserted (rejected for exactly its reason, its "
    "point, its outcome if emitted), REG_REVIEW_DECIDED_FALSE by its "
    "message, REG_SIDE_KEY_RULE over every certificate it names, "
    "REG_REVIEW_DEEP_CASES by their outcome, and REG_REVIEW_PLANTED_BUGS in "
    "a child process.",
)

# ---------------------------------------------------------------------------
# 19. int_parts, and ftc at an occurrence (int_parts spec 2026-09-25)
#
# The owner, 2026-09-25: the items the course needs come before the API's
# client. The course integrates by parts from the readiness sheet on
# (P1(1)'s rung 2, "a polynomial times a sine, which is a job for parts")
# and "heavily in 09, 11, 19". E67 deferred int_parts from the regularity
# step; this step builds it. Written from DESIGN.md §6.4 ("Around ftc:
# int_parts"), §8's by-parts row ("u and v: computes u', checks v',
# assembles both halves"), and int_subst's rule (section 12), whose
# selector, scope, under-D and orientation steps it reuses unchanged.
# Specified before any code. The mathematics of every accepted case was
# checked with SymPy 1.14 in a scratch venv (INT_PARTS_VERIFIED).

INT_PARTS_MOVE = "int_parts"
INT_PARTS_ARGS = ("var", "u", "v", "check", "facts")
INT_PARTS_OPTIONAL = ("occurrence",)
FTC_OPTIONAL = ("occurrence",)  # E73

DECISIONS_INT_PARTS = {
    "E71": "int_parts is §6.4's rule read left to right: for u, v in C^1 on "
           "the closed range [a, b], Int[x = a .. b] u*v' == (u(b)*v(b) - "
           "u(a)*v(a)) - Int[x = a .. b] u'*v. The learner supplies u and v "
           "(§8's row); the kernel computes u' and v' by deriv on the closed "
           "range, never takes them as arguments, and checks the selected "
           "integrand == u*v' by `check` (ring or field, with facts, as "
           "ftc's check). A failed check refuses 'int-parts-check-failed' "
           "with the residual body - u*v'. The identity holds for either "
           "order of a and b (both sides change sign), so the limits are "
           "kept as written and the premises sit on the range E56 builds.",
    "E72": "What it owes, on the closed range D = P + (the old range): u's "
           "and v's formers; deriv's side conditions for u' and for v' "
           "(closed, as int_subst's step 10: u' stands in the new "
           "integrand, which must be defined at the ends); the discharged "
           "integrand equation (source 'int_parts_integrand', tag "
           "('deriv+' + check, the facts' entries)); u in C^1 and v in C^1 "
           "on D (sources 'int_parts_u_C1', 'int_parts_v_C1'), decided by "
           "regularity; and the new term's formers at P, which include the "
           "new integral's own C^0 former. A u or v undefined or not C^1 "
           "somewhere on the closed range is therefore refused by "
           "discharge ('obligation-decided-false') wherever a point shows "
           "it, and never admitted as a plain Proved.",
    "E73": "ftc gains an optional 'occurrence', int_flip's selector (E51 "
           "step 2): the k-th Integral node of the non-?A side in "
           "REWRITE_RULE's pre-order. Without it ftc is unchanged, the "
           "goal's lhs must be an Int, and 'ftc-no-integral' otherwise. With "
           "it, the selected Int is replaced in place by F(b) - F(a), its "
           "premises stated at its position domain P (decided by E56 as "
           "int_subst's are), and E48's under-D test applied to it and F, "
           "reusing 'rewrite-under-D-needs-open-domain'. An occurrence past "
           "the last Int is 'ftc-no-integral'. This is what lets the "
           "integral int_parts leaves inside an expression be finished: "
           "ftc as built could only act on a bare Int lhs.",
    "E74": "Out of this step, recorded: the cycle case (I = Int[x = 0 .. pi] "
           "exp x * sin x by parts twice) needs the goal to keep I while "
           "its expansion is formed, i.e. an equation move ('have' or "
           "'solve for I'); after two int_parts steps the remaining Int's "
           "body is -(sin x)*exp x, a different atom to ring than exp x * "
           "sin x. The owner's course needs it (unit 06, unit 19); it is "
           "the next step's, not this one's. Also out: parts over an "
           "infinite range (int_improper's) and symbolic-n recurrences "
           "(unit 10 P3), which need an integer-parameter judgement.",
    "E75": "The selector, scope and under-D steps are int_subst's with the "
           "code prefix 'int-parts-': 'int-parts-no-integral', "
           "'int-parts-wrong-variable', 'int-parts-ambiguous', "
           "'int-parts-infinite-endpoint', 'int-parts-scope' (u and v may "
           "mention the goal's free names, the enclosing Ints' binders and "
           "var). No fresh variable is introduced, so there is no "
           "not-fresh check.",
}

INT_PARTS_RULE = (
    "Step 1, args: exactly INT_PARTS_ARGS plus optionally 'occurrence' (an "
    "int >= 0); var names a variable; u and v are terms without ?A or oo; "
    "check is ring or field and ring takes no facts. Else 'bad-args'.",
    "Step 2, select: int_subst's step 2 on var (E48), codes per E75.",
    "Step 3: a limit of the selected Int that is oo or -oo is "
    "'int-parts-infinite-endpoint'; an Int or D in a limit is refused by "
    "SECOND_REVIEW_RULE as in every step.",
    "Step 4, scope: fv(u) and fv(v) are within the position's scope plus "
    "{var}, else 'int-parts-scope' naming the part ('u' or 'v').",
    "Step 5, under D: E48's test on the selected Int and u, v.",
    "Step 6, orientation: P decided (E56_AMENDMENTS), then the old range by "
    "_range at P, owing its order when its ends are not two literals; "
    "neither order proved is 'orientation-undecided'. D = P + (range,).",
    "Step 7, formers: u's, then v's, on D.",
    "Step 8, derivatives: deriv(u, var, D), then deriv(v, var, D), each "
    "emission owed.",
    "Step 9, check: body == u * v' at D by `check`; failure is "
    "'int-parts-check-failed' with the residual; success emits the "
    "equation discharged (E72).",
    "Step 10, premises: u in C^1 on D, then v in C^1 on D (E72).",
    "Step 11, new term: (u[var := b]*v[var := b] - u[var := a]*v[var := a]) "
    "- Int[var = a .. b] u' * v, limits as written, u' as deriv gave it; put "
    "at the selected path; its formers charged at P; check_goal.",
)

REFUSAL_CODES_INT_PARTS = {
    "int-parts-no-integral": "E75: no Int, or none at the occurrence",
    "int-parts-wrong-variable": "E75: the selected Int does not bind var",
    "int-parts-ambiguous": "E75: no occurrence and two Ints bind var",
    "int-parts-infinite-endpoint": "E75: a limit is oo or -oo",
    "int-parts-scope": "E75: u or v mentions a name not in scope",
    "int-parts-check-failed": "E71: body is not u*v'. Carries the residual",
}
INT_PARTS_MESSAGES = {
    "int-parts-check-failed": "the integrand is not u*v' for u := {u}, "
                              "v := {v}",
    "int-parts-infinite-endpoint": "int_parts needs finite limits, and "
                                   "{limit} is not (int_improper is the "
                                   "route)",
    "int-parts-scope": "{part} {term} mentions {name}, which is not in scope",
}
SOURCES_INT_PARTS = {
    "int_parts_integrand": "int_parts: the selected integrand == u*v', "
                           "decided in-step (E71)",
    "int_parts_u_C1": "int_parts premise: u in C^1 on the closed range (E72)",
    "int_parts_v_C1": "int_parts premise: v in C^1 on the closed range (E72)",
}

# Accepted proofs: each step's goal as show() prints it is not fixed here
# (the build prints deriv's output as it gives it); what is fixed is that
# every step is accepted, the final report, and the theorem.
INT_PARTS_PROOFS = {
    "PARTS1": {
        "goal": "Int[t = 0 .. pi/2] t*sin t == ?A",
        "why": "readiness P1(1)'s parts route: t*sin t, u := t, v := -cos t",
        "steps": [
            ("int_parts", {"var": "t", "u": "t", "v": "-cos t",
                           "check": "ring", "facts": []}),
            ("ftc", {"F": "-sin t", "check": "ring", "facts": [],
                     "occurrence": 0}),
            ("rewrite", {"entry": "cos_pi_half", "inst": {},
                         "at": "cos(pi/2)"}),
            ("rewrite", {"entry": "cos_zero", "inst": {}, "at": "cos 0"}),
            ("rewrite", {"entry": "sin_pi_half", "inst": {},
                         "at": "sin(pi/2)"}),
            ("rewrite", {"entry": "sin_zero", "inst": {}, "at": "sin 0"}),
            ("close", {"value": "1", "check": "ring", "facts": []}),
        ],
        "report": "Proved.",
        "theorem": "Int[t = 0 .. pi/2] t*sin t == 1",
    },
    "PARTS_REVERSED": {
        "goal": "Int[t = pi/2 .. 0] t*sin t == ?A",
        "why": "E71: reversed literal limits, kept as written",
        "steps": "PARTS1's, with close's value -1",
        "report": "Proved.",
        "theorem": "Int[t = pi/2 .. 0] t*sin t == -1",
    },
    "PARTS_NESTED": {
        "goal": "2*(Int[t = 0 .. pi/2] t*sin t) == ?A",
        "why": "int_parts on an Int inside an expression, then ftc at "
               "occurrence 0 (E73)",
        "steps": "PARTS1's, with close's value 2",
        "report": "Proved.",
        "theorem": "2*(Int[t = 0 .. pi/2] t*sin t) == 2",
    },
    "PARTS_LN": {
        "goal": "Int[x = 1 .. e_const] ln x == ?A",
        "why": "u := ln x, v := x; its former x > 0 discharged on [1, e]; "
               "ftc's check needs field, 1 == (1/x)*x at x # 0",
        "steps": [
            ("int_parts", {"var": "x", "u": "ln x", "v": "x",
                           "check": "ring", "facts": []}),
            ("ftc", {"F": "x", "check": "field", "facts": [],
                     "occurrence": 0}),
            ("rewrite", {"entry": "ln_e", "inst": {}, "at": "ln e_const"}),
            ("rewrite", {"entry": "ln_one", "inst": {}, "at": "ln 1"}),
            ("close", {"value": "1", "check": "ring", "facts": []}),
        ],
        "report": "Proved.",
        "theorem": "Int[x = 1 .. e_const] ln x == 1",
    },
}

# Refused moves: (goal, move, args, code). A residual is asserted non-zero
# where the code carries one.
INT_PARTS_BAD_MOVES = [
    {"id": "parts_sign_lost", "goal": "Int[t = 0 .. pi/2] t*sin t == ?A",
     "move": "int_parts", "args": {"var": "t", "u": "t", "v": "cos t",
                                   "check": "ring", "facts": []},
     "refusal": "int-parts-check-failed", "residual": True,
     "why": "v' = -sin t: the sign the learner loses"},
    {"id": "parts_no_integral", "goal": "1 + 1 == ?A",
     "move": "int_parts", "args": {"var": "x", "u": "x", "v": "x",
                                   "check": "ring", "facts": []},
     "refusal": "int-parts-no-integral"},
    {"id": "parts_wrong_variable", "goal": "Int[t = 0 .. 1] t == ?A",
     "move": "int_parts", "args": {"var": "x", "u": "x", "v": "x",
                                   "check": "ring", "facts": []},
     "refusal": "int-parts-wrong-variable"},
    {"id": "parts_infinite", "goal": "Int[x = 1 .. oo] x == ?A",
     "move": "int_parts", "args": {"var": "x", "u": "x", "v": "x",
                                   "check": "ring", "facts": []},
     "refusal": "int-parts-infinite-endpoint"},
    {"id": "parts_scope", "goal": "Int[x = 0 .. 1] x == ?A",
     "move": "int_parts", "args": {"var": "x", "u": "y", "v": "x",
                                   "check": "ring", "facts": []},
     "refusal": "int-parts-scope"},
    {"id": "parts_u_pole", "goal": "Int[x = -1 .. 1] x == ?A",
     "move": "int_parts", "args": {"var": "x", "u": "1/x", "v": "x^3/3",
                                   "check": "field", "facts": []},
     "refusal": "obligation-decided-false",
     "why": "E72, soundness: u*v' == x by field, but u's former x # 0 is "
            "false at 0 inside [-1, 1]"},
    {"id": "parts_u_not_C1_at_end", "goal": "Int[x = 0 .. 1] sqrt x == ?A",
     "move": "int_parts", "args": {"var": "x", "u": "sqrt x", "v": "x",
                                   "check": "ring", "facts": []},
     "refusal": "obligation-decided-false",
     "why": "E72: d_sqrt owes x > 0 on the closed [0, 1]; u' would make "
            "the new integral improper at 0"},
    {"id": "parts_ring_with_facts", "goal": "Int[t = 0 .. 1] t == ?A",
     "move": "int_parts", "args": {"var": "t", "u": "t", "v": "t",
                                   "check": "ring",
                                   "facts": ["FACT"]},
     "refusal": "bad-args", "why": "step 1; FACT is any minted handle"},
    {"id": "parts_under_D", "goal": "D[y] (Int[x = 0 .. 1] x*y) == ?A",
     "move": "int_parts", "args": {"var": "x", "u": "x*y", "v": "x",
                                   "check": "ring", "facts": []},
     "refusal": "rewrite-under-D-needs-open-domain", "why": "E48, step 5"},
    {"id": "ftc_occurrence_none", "goal": "Int[t = 0 .. 1] t == ?A",
     "move": "ftc", "args": {"F": "t^2/2", "check": "ring", "facts": [],
                             "occurrence": 1},
     "refusal": "ftc-no-integral", "why": "E73"},
    {"id": "ftc_occurrence_under_D", "goal": "D[y] (Int[x = 0 .. 1] x*y) "
                                             "== ?A",
     "move": "ftc", "args": {"F": "x^2*y/2", "check": "ring", "facts": [],
                             "occurrence": 0},
     "refusal": "rewrite-under-D-needs-open-domain", "why": "E73, E48"},
    {"id": "ftc_no_occurrence_unchanged", "goal": "2*(Int[t = 0 .. 1] t) "
                                                  "== ?A",
     "move": "ftc", "args": {"F": "t^2/2", "check": "ring", "facts": []},
     "refusal": "ftc-no-integral", "why": "E73: without an occurrence, "
                                          "ftc is unchanged"},
]

INT_PARTS_VERIFIED = (
    "SymPy 1.14, 2026-09-25: Int(t*sin t, 0, pi/2) = 1, reversed = -1, "
    "twice = 2; Int(ln x, 1, E) = 1; (t*(-cos t))|_0^{pi/2} - Int(-cos t, "
    "0, pi/2) = 1.",
)
INT_PARTS_SWITCH = (
    "At the build: MOVES gains 'int_parts'; the refusal codes and sources "
    "merge into the suite's coverage; proof_of_life gains item 'P', which "
    "drives INT_PARTS_PROOFS (each step accepted, report and theorem) and "
    "INT_PARTS_BAD_MOVES (code, state unchanged, residual non-zero where "
    "stated). Every earlier table is unchanged: ftc without an occurrence "
    "behaves exactly as before.",
)

# E57_PRINCIPLE gains int_parts (INT_PARTS_SWITCH): every move is named there.
E57_PRINCIPLE["int_parts"] = (
    "complies: it replaces one Int by a boundary term and another Int under "
    "its premises. An Int or D in u or v is refused by deriv (E12, E26 (b)); "
    "one in a limit by SECOND_REVIEW_RULE; one inside the integrand can only "
    "be cancelled by the check's ring as an atom whose own former (Q23) was "
    "owed where it entered, which is ftc's case since regularity")

# ---------------------------------------------------------------------------
# 20. int_improper at an infinite limit (improper spec 2026-09-25)
#
# The owner, 2026-09-25: the items the course needs come first. Readiness
# P2 integrates over (-oo, oo) and P5 over [0, oo) ("improper limits" is a
# skill P5 names). E65 deferred convergence because convergence is not
# continuity. This step builds §6.4's int_improper for an INFINITE limit,
# as a limit of ftc, with convergence proved in the step as part of its
# conclusion, so no conv obligation and no new judgement form is needed.
# Specified before any code; SymPy-checked (IMPROPER_VERIFIED).

INT_IMPROPER_MOVE = "int_improper"
INT_IMPROPER_ARGS = ("F", "check", "facts")
INT_IMPROPER_OPTIONAL = ("occurrence",)

DECISIONS_IMPROPER = {
    "E76": "The rule. For an Int[x = a .. b] f with at least one of a, b "
           "infinite, and F with: f in C^0 on the range (closed at a finite "
           "end, open at an infinite one), F in C^0 on the same range, F in "
           "C^1 on its interior, D[x] F == f on its interior (deriv and "
           "`check`, as ftc), and at each infinite end e the limit of F as "
           "x -> e FINITE and equal to L_e, the integral converges and "
           "equals V(b) - V(a), where V(e) is L_e at an infinite end and "
           "F[x := e] at a finite one. True for either order of a and b "
           "(both sides change sign). Convergence is the step's conclusion: "
           "the defining limit of the partial integrals is F(t) - F(a) -> "
           "L - F(a) by ftc on each [a, t]. The selected Int is replaced "
           "by that value in place (ftc's selection, E73: the lhs Int, or "
           "the occurrence).",
    "E77": "Limits are computed by a new TRUSTED module, limits.py, never "
           "supplied by the learner: lim(t, x, s) for s = +1 (x -> oo) or "
           "-1 (x -> -oo) returns a finite Term L, +oo, -oo, or fails. Its "
           "rules are the textbook limit laws, each with its side condition "
           "returned for the kernel to emit (LIMIT_RULES). A failure refuses "
           "'int-improper-limit-unknown'; an infinite limit refuses "
           "'int-improper-diverges', which is a true statement (an "
           "antiderivative with an infinite limit at an infinite end means "
           "the integral diverges) and the refutation §5.2 wanted, stated "
           "as a refusal because the diverges judgement is not built.",
    "E78": "Side conditions. The evaluator assumes only x-free facts: a "
           "constant is > 0, < 0 or # 0 (a leading coefficient, a finite "
           "limit that ln, a division or a sign rule needs). Each is "
           "emitted at the goal's domain G with source "
           "'int_improper_limit' and discharged, refuted or admitted like "
           "any obligation, so a false one refuses the step and an "
           "undecided one is an admission, never silent. The evaluator's "
           "correctness also uses that F is defined on the whole range, "
           "which the step owes (F's formers and F in C^0).",
    "E79": "Out of this step, recorded: an integrand singular at a FINITE "
           "end (unit 00 P7's turning points, Int[x = 0 .. 1] x^(-1/2)), "
           "whose Int is refused at install by its C^0 former today; the "
           "diverges judgement and its rules (div_compare, div_power, "
           "div_pole); int_compare; oo - oo and oo/oo beyond rational "
           "functions (the learner writes ln(x/(x + 1)), not ln x - "
           "ln(x + 1)); and int_parts or int_subst over an infinite range.",
    "E80": "A new §6.8 entry, atan_zero: atan 0 == 0, trusted like "
           "sin_zero, for the value F(0) that atan antiderivatives leave.",
}

LIMIT_RULES = (
    "x-free t: t (continuity of a constant).",
    "Rational in x (x, x-free constants, +, -, *, /, integer powers): the "
    "leading form c*x^k, built bottom-up: x is 1*x^1; a constant c is "
    "c*x^0; products and quotients multiply and divide c and add and "
    "subtract k; t^n gives c^n*x^(k*n); a sum keeps the higher k, and at "
    "equal k gives (c1 + c2)*x^k owing c1 + c2 # 0. Every leading "
    "coefficient c of a divisor or of the result owes c # 0. Then k = 0 "
    "gives c, k < 0 gives 0, and k > 0 gives the infinity whose sign is "
    "sign(c) times s^k, owing c > 0 or c < 0 (whichever the evaluator "
    "asks, the first it can decide).",
    "Otherwise by the algebra of limits: sums (finite + finite; an "
    "infinity plus a finite; two like infinities; unlike infinities "
    "fail), negation, products (finite * finite; an infinity times a "
    "finite L owing L > 0 or L < 0; two infinities), quotients (finite / "
    "finite owing the denominator's L # 0; finite / infinity is 0; an "
    "infinity / finite owing its sign; infinity / infinity fails), and "
    "integer powers.",
    "Continuous functions of a finite limit L: sin L, cos L, atan L, "
    "exp L; ln L owing L > 0; sqrt L owing L >= 0.",
    "At infinity: exp(+oo) = +oo, exp(-oo) = 0; ln(+oo) = +oo; sqrt(+oo) = "
    "+oo; atan(+oo) = pi/2, atan(-oo) = -pi/2; sin and cos of an infinity "
    "fail.",
    "Anything else (an Int, a D, RPow with x, a declared function, tan, "
    "asin, acos, acosh, atanh) fails.",
)

REFUSAL_CODES_IMPROPER = {
    "int-improper-no-integral": "E76: no Int at the lhs or the occurrence",
    "int-improper-finite": "E76: both limits finite; ftc is the move",
    "int-improper-check-failed": "E76: D[x] F is not f. Carries the "
                                 "residual (ftc-check-failed's twin)",
    "int-improper-limit-unknown": "E77: the evaluator cannot compute a "
                                  "limit of F at an infinite end",
    "int-improper-diverges": "E77: the limit of F at an infinite end is "
                             "infinite, so the integral diverges",
}
SOURCES_IMPROPER = {
    "int_improper_f_C0": "premise: f in C^0 on the range (E76)",
    "int_improper_F_C0": "premise: F in C^0 on the range (E76)",
    "int_improper_F_C1": "premise: F in C^1 on the interior (E76)",
    "int_improper_D": "premise: D[x] F == f on the interior, decided in "
                      "step (E76)",
    "int_improper_limit": "a limit law's x-free side condition (E78)",
}

INT_IMPROPER_PROOFS = {
    "IMP_POWER": {"goal": "Int[x = 1 .. oo] 1/x^2 == ?A",
                  "steps": [("int_improper", {"F": "-1/x", "check": "field",
                                              "facts": []}),
                            ("close", {"value": "1", "check": "field",
                                       "facts": []})],
                  "report": "Proved.",
                  "theorem": "Int[x = 1 .. oo] 1/x^2 == 1"},
    "IMP_REVERSED": {"goal": "Int[x = oo .. 1] 1/x^2 == ?A",
                     "steps": [("int_improper", {"F": "-1/x",
                                                 "check": "field",
                                                 "facts": []}),
                               ("close", {"value": "-1", "check": "field",
                                          "facts": []})],
                     "report": "Proved.",
                     "theorem": "Int[x = oo .. 1] 1/x^2 == -1"},
    "IMP_ATAN": {"goal": "Int[x = 0 .. oo] 1/(1 + x^2) == ?A",
                 "steps": [("int_improper", {"F": "atan x", "check": "field",
                                             "facts": []}),
                           ("rewrite", {"entry": "atan_zero", "inst": {},
                                        "at": "atan 0"}),
                           ("close", {"value": "pi/2", "check": "ring",
                                      "facts": []})],
                 "report": "Proved.",
                 "theorem": "Int[x = 0 .. oo] 1/(1 + x^2) == pi/2"},
    "IMP_BOTH": {"goal": "Int[x = -oo .. oo] 1/(1 + x^2) == ?A",
                 "steps": [("int_improper", {"F": "atan x", "check": "field",
                                             "facts": []}),
                           ("close", {"value": "pi", "check": "ring",
                                      "facts": []})],
                 "report": "Proved.",
                 "theorem": "Int[x = -oo .. oo] 1/(1 + x^2) == pi"},
    "IMP_EXP": {"goal": "Int[x = 0 .. oo] exp(-x) == ?A",
                "steps": [("int_improper", {"F": "-exp(-x)", "check": "ring",
                                            "facts": []}),
                          ("rewrite", {"entry": "exp_zero", "inst": {},
                                       "at": "exp(-0)"}),
                          ("close", {"value": "1", "check": "ring",
                                     "facts": []})],
                "report": "Proved.",
                "theorem": "Int[x = 0 .. oo] exp(-x) == 1"},
    "IMP_NESTED": {"goal": "2*(Int[x = 1 .. oo] 1/x^2) == ?A",
                   "steps": [("int_improper", {"F": "-1/x", "check": "field",
                                               "facts": [],
                                               "occurrence": 0}),
                             ("close", {"value": "2", "check": "field",
                                        "facts": []})],
                   "report": "Proved.",
                   "theorem": "2*(Int[x = 1 .. oo] 1/x^2) == 2"},
}

INT_IMPROPER_BAD_MOVES = [
    {"id": "imp_diverges", "goal": "Int[x = 1 .. oo] 1/x == ?A",
     "move": "int_improper", "args": {"F": "ln x", "check": "ring",
                                      "facts": []},
     "refusal": "int-improper-diverges",
     "why": "E77: lim ln x = oo; E65's own example, now refused for the "
            "right reason"},
    {"id": "imp_limit_unknown", "goal": "Int[x = 0 .. oo] cos x == ?A",
     "move": "int_improper", "args": {"F": "sin x", "check": "ring",
                                      "facts": []},
     "refusal": "int-improper-limit-unknown"},
    {"id": "imp_finite", "goal": "Int[x = 0 .. 1] x == ?A",
     "move": "int_improper", "args": {"F": "x^2/2", "check": "ring",
                                      "facts": []},
     "refusal": "int-improper-finite"},
    {"id": "imp_check_failed", "goal": "Int[x = 1 .. oo] 1/x^2 == ?A",
     "move": "int_improper", "args": {"F": "1/x", "check": "field",
                                      "facts": []},
     "refusal": "int-improper-check-failed", "residual": True},
    {"id": "imp_F_pole", "goal": "Int[x = 0 .. oo] 1/(1 + x^2) == ?A",
     "move": "int_improper", "args": {"F": "atan x + 1/(x - 1) - 1/(x - 1)",
                                      "check": "field", "facts": []},
     "refusal": "obligation-decided-false",
     "why": "E76, soundness: F's former x - 1 # 0 fails at 1 in [0, oo)"},
    {"id": "imp_oo_minus_oo", "goal": "Int[x = 1 .. oo] 1/(x*(x + 1)) == ?A",
     "move": "int_improper", "args": {"F": "ln x - ln(x + 1)",
                                      "check": "field", "facts": []},
     "refusal": "int-improper-limit-unknown",
     "why": "E79: oo - oo fails; ln(x/(x + 1)) is the form that works"},
    {"id": "ftc_still_refuses_oo", "goal": "Int[x = 1 .. oo] 1/x^2 == ?A",
     "move": "ftc", "args": {"F": "-1/x", "check": "field", "facts": []},
     "refusal": "ftc-infinite-endpoint"},
    {"id": "imp_ring_still_refuses", "goal": "Int[x = 1 .. oo] 1/x^2 == ?A",
     "move": "close", "args": {"value": "1", "check": "ring", "facts": []},
     "refusal": "Int-or-D-not-normalisable",
     "why": "E65 stands for an Int no step has evaluated"},
]

# The evaluator called directly: (term, direction, expected) where
# expected is a GRAMMAR string for a finite limit (compared by ring after
# the side conditions), 'oo', '-oo' or None for a failure.
LIMIT_CASES = [
    ("-1/x", +1, "0"),
    ("atan x", +1, "pi/2"),
    ("atan x", -1, "-pi/2"),
    ("(x^2 + sqrt 2 * x + 1)/(x^2 - sqrt 2 * x + 1)", +1, "1"),
    ("(2*x^3 - x)/(x^3 + 5)", -1, "2"),
    ("(x^2 + 1)/x", +1, "oo"),
    ("(x^2 + 1)/x", -1, "-oo"),
    ("x^3", -1, "-oo"),
    ("x^2 - x^2 + x", +1, None),  # equal-degree cancellation: 1 - 1 # 0 is false
    ("exp(-x)", +1, "0"),
    ("exp x", -1, "0"),
    ("ln(x/(x + 1))", +1, "ln 1"),
    ("ln x", +1, "oo"),
    ("ln x - ln(x + 1)", +1, None),
    ("sin x", +1, None),
    ("sqrt(x^2 + 1)", +1, "oo"),
    ("atan(sqrt 2 * x + 1)", +1, "pi/2"),
    ("x*exp(-x)", +1, None),  # oo * 0: fails, incomplete never unsound
    ("1/x + atan x", +1, "pi/2"),
]

IMPROPER_VERIFIED = (
    "SymPy 1.14, 2026-09-25: Int(1/x^2, 1, oo) = 1; Int(1/(1+x^2), 0, oo) "
    "= pi/2; over (-oo, oo) = pi; Int(exp(-x), 0, oo) = 1; Int(1/x, 1, oo) "
    "= oo; every LIMIT_CASES finite value and infinity.",
)
IMPROPER_SWITCH = (
    "At the build: MOVES gains 'int_improper' after 'int_parts'; entries "
    "gain atan_zero (E80); E57_PRINCIPLE gains int_improper; "
    "proof_of_life item 'I' drives INT_IMPROPER_PROOFS, "
    "INT_IMPROPER_BAD_MOVES and LIMIT_CASES; readiness P5 as a problem "
    "file if its admissions can be discharged, else recorded with them.",
)

# Section 20, amended before its build (improper spec, second part): P5 and
# P2 both stop at the sign of a QUOTIENT, which no §5.3 method decides:
# P5's ln argument ((x + sqrt 2/2)^2 + 1/2)/((x - sqrt 2/2)^2 + 1/2) > 0,
# and P2's limit side sqrt((a - e)/(a + e)) > 0, whose cite of sqrt_pos
# owes (a - e)/(a + e) > 0.
DECISIONS_IMPROPER["E81"] = (
    "A §5.3 method 5b, 'sign quotient', trusted checker plus untrusted "
    "search. A key g > 0, g >= 0 (or 0 < g, 0 <= g) with g = n/d "
    "syntactically, or 0 > g, 0 >= g (g < 0, g <= 0) with g = n/d, is "
    "accepted from two sub-certificates at the key's own domain: d > 0 or "
    "d < 0 (always strict), and n r 0 with r strict under a strict target "
    "and any ordering under a non-strict one; the product of their signs "
    "must be the target's. A key n/d # 0 is accepted from n # 0, n > 0 or "
    "n < 0 alone. Sound where the key's terms are defined: there d # 0, "
    "and sign(n/d) = sign(n)*sign(d). The search tries it after sign "
    "product and before cite.")
QUOTIENT_CASES = [
    # (key as a goal string, discharged?)
    ("((x + 1)^2 + 1/2)/((x - 1)^2 + 1/2) > 0 @ x >= 0", True),
    ("(x^2 + 1)/(0 - x^2 - 1) < 0", True),
    ("x/(x^2 + 1) >= 0 @ x >= 0", True),
    ("(a - e1)/(a + e1) > 0 @ a > e1, e1 > 0", True),
    ("x/(x^2 + 1) > 0 @ x >= 0", False),  # x = 0: a strict target needs n > 0
    ("(x + 1)/(x - 1) # 0 @ x > 1", True),
]
QUOTIENT_MUST_REJECT = [
    # (key, certificate) that the checker must refuse
    ("x/(x^2 + 1) > 0 @ x >= 0",
     {"method": "sign quotient", "num": (">=", "x >= 0 @ x >= 0"),
      "den": (">", "x^2 + 1 > 0 @ x >= 0")},
     "a non-strict numerator under a strict target"),
    ("(x - 2)/(x^2 + 1) > 0 @ x >= 0",
     {"method": "sign quotient", "num": ("<", "x - 2 < 0 @ x >= 0"),
      "den": (">", "x^2 + 1 > 0 @ x >= 0")},
     "parity: the signs multiply to -1"),
]

# Section 20, second amendment before its build: P2's admissions are signs
# of syntactic sums and products under parametric hypotheses (a + e1 +
# (a - e1)*t^2 # 0, (a + e1)*sqrt((a - e1)/(a + e1)) # 0) and P5's last is a
# square, ((x - sqrt 2/2)^2 + 1/2)^2 # 0. E81's quotient generalises.
DECISIONS_IMPROPER["E82"] = (
    "E81's method becomes 'sign node' (the name 'sign quotient' is "
    "retired before any build used it): a key whose g (as E81 reads it: "
    "the node itself for # 0, n/d > 0 style readings for orderings, now "
    "any node) is a Div, Mul, Pow or Add is accepted from one sub-"
    "certificate per child, at the key's own domain, each child with a "
    "relation in {>, >=, <, <=, # 0}. Each relation is the set of signs "
    "it allows ('>' {+}, '>=' {+, 0}, '<' {-}, '<=' {-, 0}, '# 0' {+, -}); "
    "the node's set is computed exactly: a product or quotient multiplies "
    "the sets (a divisor's 0 removed, since it is non-zero where the key's "
    "terms are defined), b^n is b's set to the n (0 removed from b's set "
    "for n < 0; for even n a Pow may take NO sub-certificate, its set "
    "then {+, 0}), and a sum of two sets is {+} for {+} with {+} or {+, "
    "0}, {+, 0} for two {+, 0}, the same for minus, and otherwise not "
    "accepted. The key is accepted when the node's set is inside the "
    "target's ({+} for a strict positive target, {+, 0} for a non-strict "
    "one, likewise negative, {+, -} for # 0). Sound where the key's terms "
    "are defined, which is all a certificate ever claims.")
SIGN_NODE_CASES = X_SIGN_NODE_CASES = [
    ("a + e1 + (a - e1)*t^2 # 0 @ a > e1, e1 > 0", True),
    ("(a + e1)*sqrt((a - e1)/(a + e1)) # 0 @ a > e1, e1 > 0", True),
    ("((x - 1)^2 + 1/2)^2 # 0", True),
    ("x^2 + y^2 >= 0", True),
    ("x^2 + y^2 > 0", False),  # (0, 0): the strict sum needs one strict part
    ("(x - 1)*(x + 1) > 0 @ x > 1", True),
]
