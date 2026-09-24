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
    "reg": "§6.9 closure rules via §7's reg tactic (regularity is only "
           "listed in this milestone)",
}
DISCHARGE_METHODS = {
    "norm_num": "§6.2, closes a goal over rational literals exactly (E7)",
    "deriv+ring": "§6.3 deriv then §6.2 ring, run inside the ftc step (E9)",
    "deriv+field": "§6.3 deriv then §6.2 field, facts as cited (E9)",
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

    "reg. A regularity judgement e in C^k(D) is tagged ('reg', ()) by its "
    "shape alone. Regularity is only listed in this milestone (WHAT.md Out, "
    "§6.9). No other method sees a regularity judgement, and reg sees "
    "nothing else.",

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
              "base > 0 (E6), and a partial builtin its natural domain "
              "(E26: ln u owes u > 0, sqrt u owes u >= 0, tan u owes "
              "cos u # 0, and so on)",
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
                      ("BAD_MOVES", "match_refuses_Int"),
                      ("BAD_MOVES", "ftc_check_refuses_Int")],
        "admissions": _P1_UNCHANGED,
    },
    "ring_reads_D_as_atom": {
        "mutation": "ring_nf treats a Deriv node as an opaque atom",
        "caught_by": [("BAD_MOVES", "ring_refuses_D"),
                      ("BAD_MOVES", "close_D_goal_scope_passes"),
                      ("BAD_MOVES", "divisor_test_refuses_D"),
                      ("BAD_MOVES", "match_refuses_D"),
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
          "emits lo <= hi (§5.1, §5.3 method 2, §6.1, §6.4)",
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
        # every range certificate using a lower end is then rejected, so
        # each proof's range keys fall back to admissions
        "caught_by": [("DISCHARGE_MUST_REJECT",
                       "farkas_constant_not_contradiction"),
                      ("N", "P1.1"), ("N", "P1.1-fallback"), ("N", "P1.2"),
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
