# The proof-of-life — what was built, what was decided, what the design owes

The record of `WHAT.md`'s proof-of-life milestone (built 2026-09-23 to
2026-09-24), in the way `STAGE0.md` records stage 0. The code lives in
`kernel/`; the detailed sources are `kernel/GRAMMAR.md` (syntax, D1–D18),
`kernel/p1_expected.py` (behaviour, E1–E26) and `kernel/ARCHITECTURE.md`
(modules and contracts). This file summarises them and lists what they found
wrong in `DESIGN.md`, for folding in. It is not the place any of those facts
lives only once.

## Result

**All six Done-when items pass.** `python3 kernel/proof_of_life.py` →
`PASS: 225 of 225 checks passed` for items 1–6, exit 0. The unit tests
(`python3 -m unittest discover -s kernel`) pass 69 of 69. Both were re-run
independently after the last change, on 2026-09-24. Since then the suite has
grown to 882: item 7 added the problem files, E27 the evaluated-answer
cases, discharge its certificate checks, `int_subst` its moves and files,
the consolidation step its moves, entries and review cases, and
regularity its checker, formers and review cases.

| Proof | Verdict |
|---|---|
| P1.1 ∫₀^{π/2} sin(√(t²))·2t = 2 | Proved modulo 6 admissions |
| P1.1, direct fallback on x | Proved modulo 9 admissions |
| P1.2 ∫₀¹ 1/(1+x³) = ⅓ ln 2 + π/(3√3) | Proved modulo 14 admissions |
| P1.2 as ⅓ ln 2 + π√3/9 | Proved modulo 13 admissions |

- Every obligation list, with its domains, matches the list written by hand
  before any code existed, and no P1 admission is tagged `none`.
- Five planted bugs are caught: the three `WHAT.md` names and two more the
  data added. So are 30 definedness mutations, each of which removes or
  weakens one domain condition.
- The three wrong answers are rejected with their residuals: −t·sin t,
  −(2x−1)/(6(x²−x+1)), and §11.2's unreduced (√3)² form.
- Every bad move and every handle forgery is refused with its code, and the
  parser round-trips its whole term set.

**How the data was kept honest.** `GRAMMAR.md` and `p1_expected.py` were
written first, then reviewed in three rounds against the design, SymPy, an
independent derivation of the obligations, and the Done-when list. After that
they were frozen. During implementation, a request to change them was
approved only when the data was shown to be wrong, and never because it was
inconvenient for the code. Most requests were rejected. The approved ones,
and the changes for your decisions of 2026-09-24, are logged in
`p1_expected.DATA_CHANGES`. No kernel file imports the expected data.

**What was not verified.** Every round of review and attack upheld findings.
Neither the build nor the definedness change ever produced a clean round, and
the last round's fixes were applied and re-run green but not reviewed again.
The late findings were almost all bugs planted to test the suite, which it
failed to catch. They were fixed by adding tests, with no change to kernel
behaviour.

## Decided 2026-09-24

1. **Undefined terms owe their domain (option a).** Before this change,
   `0*ln(-1) == ?A` and `tan(pi/2) - tan(pi/2) == ?A` closed as a plain
   `Proved.`, because partial functions were opaque atoms that `ring`
   cancelled. Now each partial builtin owes its natural domain when it
   enters, just as `1/u` owes `u # 0` (E26):
   - `ln u` owes `u > 0`;
   - `sqrt u` owes `u ≥ 0`;
   - `tan u` owes `cos u # 0`;
   - `asin u` and `acos u` owe `u ≥ −1` and `u ≤ 1`;
   - `acosh u` owes `u ≥ 1`;
   - `atanh u` owes `u > −1` and `u < 1`.

   `ring`, `field` and `norm_num` refuse integrals and derivatives, because
   their definedness cannot be stated until regularity and `diverges` exist.
   The same conditions are charged in goal hypotheses and in a fact's
   instance values, which the attack rounds found as two more ways in.
   - **Now refused:** `0*ln(-1)`, `sqrt(-1)`, `asin 2`, `acosh 0` and
     `atanh 1`, each because its domain condition is a false literal. An
     integral minus itself is refused as not normalisable.
   - **Behaviour kept:** `0*ln 2` still proves, since it owes `2 > 0`.
   - **P1's new obligations were already in the design.** They are §11's own
     lines: `t^2 ≥ 0 @ [0, π/2]`, and `1 + x > 0` and `x^2 − x + 1 > 0` on
     [0, 1].
2. **No line-count budgets.** The per-module ceilings, the "over" flags and
   the trusted-base size line are gone from `ARCHITECTURE.md` and the script.
   The trusted base is kept small because it has to be auditable, and that is
   argued from what the code does.
3. **Protection model: both, stated honestly.** Facts use handles. Proof
   states use the sentinel: a finished state is only ever produced by
   `step()`, and the sentinel stops the realistic threat, a buggy tactic
   building a result object. §16.3's API boundary will replace in-process
   states with ids. `HANDLES_IN_FORCE`, the script's header and
   `ARCHITECTURE.md` all say this.

**One caveat to know.** `tan(pi/2) - tan(pi/2) == ?A` now reads
`Proved modulo 1 admissions`, owing `cos(pi/2) # 0` tagged `none`. That
obligation is false, but no §5.3 method can decide `cos(pi/2)`, so it is
admitted rather than refuted until discharge exists. **An admission tagged
`none` may be false**, and that is exactly what the tag is for.

## Decisions made on your behalf

The full text and reasons are in `GRAMMAR.md` §1 (D1–D18) and
`p1_expected.DECISIONS` (E1–E26). These are the ones that carry weight.

**Syntax.**
- **D1:** no decimal literals.
- **D3:** bare `e` is refused, with a pointer to `exp` or `e_const`.
- **D4:** variable names are one letter or a spelled Greek letter, plus
  digits or a suffix, so `sinx` is refused rather than read as a variable.
- **D5:** there is no implicit multiplication, and only declared symbols may
  be called.
- **D6:** `sin x^2` means sin(x²), and `sin(x)^2` is refused as ambiguous.
- **D8:** `^` is non-associative, so `x^2^3` is refused.
- **D10:** `D[x] e` leaves x free, since it is evaluated at x.
- **D11:** no name may be both bound and free in one goal.

**Rules.**
- **E1–E2:** `rewrite` matches after ring-normalising atom arguments (§18
  Q21's default), and with no position given it rewrites every occurrence.
- **E4:** every step over a range owes `lo ≤ hi`. This closes the
  reversed-limit hole listed under *Soundness* below.
- **E6 and E26:** divisors and partial builtins owe their conditions when
  they enter the proof.
- **E8:** obligations are keyed by (proposition, domain), in each rule's own
  orientation, with no subsumption.
- **E11:** under `D[x]`, `# 0` counts as an open condition.
- **E17:** a handle is honoured only by identity, and its lineage is checked.
- **E19:** close's scope check runs against the *original* goal.
- **E23:** the closed whitelist admits variables.
- **E24:** each admission's tag is the first §5.3 method whose cheap check
  passes. Tags are computed, never looked up.

**Scope.**
- **E16:** `refl`, `trans` and `cong` are internal to `rewrite` and `close`,
  not moves.
- **E18:** method 5 may split off a rational content.
- **E20:** method 4 accepts non-strict goals.
- **E25:** a divisor that normalises to zero is refused.

## For `DESIGN.md` — what the milestone found wrong

*Folded into `DESIGN.md` revision 10 (commit `516d6c7`). Kept here as the
record of what the milestone found.*

**Soundness.**
- **§6.4:** `ftc` never requires a ≤ b. With b < a both intervals are empty,
  all four premises hold vacuously, and it proves ∫₁⁻¹ 1/x² = 2. Rewriting
  under `Int` (§6.1) has the same hole. The kernel emits `lo ≤ hi` (E4); the
  rule should say so.
- **§5.1, §6.2 and §15.4:** partial builtins carried no definedness
  obligation, so §15.4's claim that the total and partial readings agree was
  false. Fold in *Decided* 1:
  - the formers and their natural domains;
  - the refusal of `Int` and `D` inside `ring`, `field` and `norm_num`;
  - charging in hypotheses and in fact instance values.
- **§5.1:** it lists `D[x]` as a binder, but `D[x] F ≐ f @ (a,b)` needs x
  free. `D[x]` binds inside e and evaluates at x, and substitution on `D`
  must be defined. The kernel follows D10.

**Underspecified, resolved by a recorded decision.**
- **§6.1 rev 9 against §6.3 rev 7:** "strict inequalities only" under
  `D[x]` forbids the `u/v` routing, which holds only at `v # 0`, so
  `D[x](x/(x+1))` would have no route (E11).
- **§5.1:** it never says *when* `/` is charged (E6).
- **§6.2:** "division is an opaque atom" doesn't say whether the atom is
  a/d or 1/d, and matching `atan_odd` needs a·inv(d) (E3).
- **§5.3 method 5:** the degree precondition fails for `3*sqrt 3 # 0` and
  `2*sqrt x # 0`, both of which §11.2 and the fallback need (E18).
- **§5.3 method 4:** it doesn't say whether it closes `≥ 0`, and the
  fallback's `0 ≤ pi^2/4` needs it (E20).
- **§5.1:** it lists `e^n` twice next to `e ^ e` without saying how a parser
  tells them apart (D8).
- **§16.3:** `/step` has no shape for a refusal. The kernel returns
  `Refusal(code, message, residual)`.
- **§15.2:** it doesn't place the tagger, the closed whitelist or residual
  rendering. All three are untrusted code called from trusted code, which
  should be named as a pattern with its argument, as `ARCHITECTURE.md` §1
  gives it.
- **§15.3:** it asks for one mechanism to be named, but both are in force,
  for the reasons in *Decided* 3.
- **§6.3:** it calls `deriv` a tactic, which makes it untrusted. In this
  milestone `ftc` accepts its output directly, so `deriv` is trusted
  (§15.2 item 2).

**Stale or inconsistent text.**
- **§11.2:** the obligation block mixes sources and domains.
  - `1 + x > 0 @ [0,1]` is ln's own domain condition (now charged, E26),
    while `d_ln` gives it on (0,1).
  - `x^2 - x + 1 > 0` has no domain.
  - `field`'s divisors `1 + x`, `x^2 - x + 1` and `1 + x^3` on (0,1) are
    missing.
- **§11.1 against §6.8:** §11.1 shows `sqrt_sq`'s obligation as `0 ≤ t` and
  §6.8 as `t ≥ 0`, and these are different keys. §6.8 also names its schema
  variable t, the same as §11.1's bound variable.
- **§6.8:** it mixes sequent and domain notation for the same kind of fact.
- **§6.9:** it still says `abs` is kept out of goals, which is stale since
  revision 6.
- **§6.3:** `d_pow_int` and `d_chain` are written in schema notation with no
  term syntax, so they are built in code.
- **§11.2:** `approx` uses decimal and scientific literals, which the term
  grammar refuses (D1). Stage 2's `approx` needs its own numeric syntax.
- **§15.2 and §17:** their line-count estimates (1,300–1,400 for the trusted
  base, and the stage-1 size rows) are the kind of budget dropped in
  *Decided* 2, and can go.

**For `WHAT.md`.**
- Literal obligations that are not divisors, such as `3 >= 0` and `2 > 0`,
  also close by `norm_num` (E7).
- P1.2's second form closes only by `field [sqrt_sq_val 3]`.
- The P1 admission counts are now 6, 9, 14 and 13.
- The status line "the tool itself is not built" is out of date.

**For the spike.** `spike/ring/test_field.py` writes `sqrt(3)^2`, which D6
now refuses. The ported tests in `kernel/test_field.py` use `(sqrt 3)^2`.

## Since: the first problem files, S1–S3 (2026-09-24)

`WHAT.md`'s next step after the milestone. The problem files are
`kernel/problems/stage0/S1.json`, `S2.json` and `S3.json`, in §16.4's `.json`
format, each carrying its reference proof. The same discipline applied:
`expected.py` was written by hand from the rules before any code ran against
it. After that, `kernel/loader.py` (untrusted) and four new §6.8 entries
(`ln_e`, `e_gt_one`, `exp_zero`, `exp_one`) were built, and item 7 of the
suite checks the files.

| Proof | Answer | Verdict |
|---|---|---|
| S1 ∫₀¹ 3x²+2x | 2 | Proved modulo 3 admissions |
| S2 ∫₀¹ x·exp(x²) | (e − 1)/2 | Proved modulo 3 admissions |
| S3 ∫₁^e (ln x)/x | 1/2 | Proved modulo 9 admissions (8 when the check is `ring`) |

**The kernel matched the hand-written lists on every assertion, first
time.** A clean first run can mean toothless checks, so it was tested in
three ways:
- The builder fed item 7 about 30 single mutations of the data, and every
  one was caught.
- A skeptic re-derived S3's list independently. It matched key for key.
- The skeptic planted 18 bugs in copies of the kernel and loader, and item 7
  caught all 18. Five of them, items 1–6 miss.

The skeptic's minor findings are fixed:
- the loader now refuses malformed files outright;
- item 7 checks that it covers every problem file;
- items 1–6 no longer depend on stage 0 importing.

One point cannot be proved: `expected.py` was edited in place after the code
existed. The builder says the only edit was an empty change log. The first
run's saved output agrees, but the timestamps cannot rule out anything else.
Next time the spec should be committed before the code.

**Open, for `DESIGN.md`** (full text in `expected.py`'s `FINDINGS`):
- **§9 and §6.8: the `closed` schema accepted an unevaluated answer.**
  **Resolved by E27**, below.
- **`WHAT.md`'s S3 sketch was wrong in three ways:**
  - it missed four obligations: the integrand's `x # 0 @ [1, e]`,
    `e_const > 0`, `1 > 0` and `2 # 0`;
  - its "by range, e_gt_one" annotation was misattributed, since `e_gt_one`
    closes the orientation `1 ≤ e_const`, not `d_ln`'s `x > 0`;
  - it used two moves the kernel does not have, a multi-entry `rewrite` and a
    `close` checked by `norm_num`.
- **§5.3 method 2 against TAG_RULES and E4.** Method 2 says it "adds
  nothing" when the range's order is unknown. The kernel instead always adds
  [lo, hi] and owes the orientation separately.
- **§6.2 against E12 on division by a literal.** `deriv` routes `u/2`
  through `u*(1/2)`, owing `2 # 0`. P1 never tested this; S2 and S3 pin it.
- **A `ring` check owes no divisors.** `ARCHITECTURE.md` §4 should say so.
- **§16.4 names no field for the reference proof and gives `declarations`
  no shape.** The files decide both, in PF1 and PF2.
- **§6.8 names `ln_e`, `exp_zero` and `exp_one` without their statements.**
  They are now pinned in `entries.py`.

## Since: closed answers must be fully evaluated, E27 (2026-09-24)

The owner decided that a value closing a `closed` goal must be simplified.
An unevaluated F(b) − F(a) such as `(exp 1 − exp 0)/2` is no longer accepted.
"Fully evaluated" is a checkable property, not a canonical form. No subterm
can still be evaluated by a §6.8 entry in force, and no unreduced literal
arithmetic is left. The full rule is in `DESIGN.md` §9 and in
`p1_expected.EVALUATED_RULE`.

The check is untrusted, in `schema.py`, and runs last in `close`. It can only
refuse, with `close-not-evaluated`, and it names the move still available.
The kernel never simplifies anything itself.

**Process.** The spec was committed before any code (`224b891`). A skeptic's
amendments were committed the same way (`303036e`). The code matched the spec
on the first run both times. The suite checks 38 refusals, 29 accepted values
and an ordering case, and stands at 334 of 334. A skeptic found:
- no way for the check to change a trusted verdict;
- no wrong refusal of the answers a learner would write, such as `3*pi/4`,
  `2*sqrt 3/3` and `1 − 1/e_const`.

Its findings were folded in:
- unevaluated sums like `2*(pi + 1) − 2` slipped through, and a monomial
  count now catches them;
- negative powers of `sqrt` are now caught;
- four suite gaps are closed;
- a deep chain of minus signs crashed the error-message printer, which is
  now iterative, fixing an older crash on the same path too.

**Limitations, by design.** The check is only as strong as the §6.8 table.
`cos 0`, `exp(ln 2)`, `sin(pi)` and `atan 1` pass until their entries are
built, and `ln 2 + ln 3` passes because no entry reduces it.

## Since: real discharge (2026-09-24)

`WHAT.md`'s next stage-1 piece. Obligations are no longer only admitted;
they are proved by certificates. The design is in `DESIGN.md` §5.3, §5.4,
§15.2 and §18 Q22, and the decisions are E28–E35 in `p1_expected.py`.
- **The split of trust.** The untrusted `search.py` proposes one
  certificate per obligation. The trusted `discharge.py` rebuilds the
  constraints from the obligation and checks it. The methods are:
  - hypothesis;
  - Farkas, over the range and linear constraints;
  - sign, a sum of squares;
  - sign product, a factorisation;
  - cite, an entry instance.

  Exact values from §6.8 are applied first.
- **Fourier–Motzkin is in stage 1** (owner's decision). It searches, and
  its Farkas combination is what gets checked.
- **Decided false refuses** (Q22, and the owner's answers). The untrusted
  `refute.py` decides an obligation false by F1, F2 or F3; F3 uses a
  bounded rational counter-point search. The step is then refused with
  `obligation-decided-false`, and the message says how it was decided.
- **What is still admitted:** regularity, which is not built yet;
  obligations no method decides; and certificates the checker rejects.

| Proof | Before discharge | After |
|---|---|---|
| P1.1 / fallback | modulo 6 / 9 | modulo 3 |
| P1.2 / alt | modulo 14 / 13 | modulo 3 |
| S1, S2 | modulo 3 | modulo 3 |
| S3 / ring | modulo 9 / 8 | modulo 3 |

The three left are always `ftc`'s regularity premises.

**Now refused outright:**
- `tan(pi/2) − tan(pi/2)`, since `cos(pi/2) # 0` reads `0 # 0`;
- the integral of 1/x² over [−1, 1], since x² # 0 is false at 0;
- `ln x * 0` with no stated domain;
- a `sqrt_sq` rewrite over [−1, 0].

**Process.** The spec went in first (`a36c466`). The build came in two
commits: first the checkers alone, then the wiring. Twice the builder showed
a planted-bug expectation in the spec was wrong, and I checked each claim
before the spec was changed and logged.

The skeptic found **no false discharge**: about 2,700 fuzzed obligations
were checked against an independent evaluator, and about 12,000 random
kernel runs. Its findings are fixed, in `ec3f693`:
- deep terms crashed `install` and `step`, a regression;
- a wrong refusal at a point where a hypothesis was undefined;
- mutable stored certificates;
- refutation exponential in the number of variables, now bounded.

The suite is at 481 of 481.

## Since: `int_subst`, substitution in an integral (2026-09-24)

The substitution move in §6.4, with decisions E36–E50 in `p1_expected.py`.
Where the owner decided, it is noted:
- **Forward mode**, x := φ(t). φ′ comes from `deriv`, never from the
  learner. The endpoint equations are decided in the step, and a mismatch
  is refused with its residual, for example "pi^2 == pi^2/4 fails at the
  upper limit".
- **Reverse mode**, u := g(x) (owner). The learner supplies f, and the
  kernel checks the integrand ≐ f(g(x))·g′(x) by `ring` or `field`. S2 goes
  through as u := x².
- **Decreasing φ with symbolic ends** (owner). When discharge decides the
  order, the step emits the flipped, oriented integral, by §5.1's
  definition. Otherwise it is refused.
- **Occurrence selector** (owner), the same one `rewrite` uses, so the
  move acts on any integral in the goal.
- **The √ sign fact** (owner). `sqrt a ≥ 0` is read by the linear method,
  which makes ∫₀⁴ 1/(1+√x) provable.

| Proof | Verdict |
|---|---|
| P1.1 from the sheet's goal, ∫₀^{π²/4} sin √x ≐ 2 | Proved modulo 5 admissions (2 from the substitution, 3 from `ftc`, all regularity) |
| SUB1 ∫₀¹ x√(1−x) ≐ 4/15, by a decreasing φ | Proved modulo 5 admissions |
| S2R, S2 by u := x² | Proved modulo 4 admissions |
| SUB2 ∫₀⁴ 1/(1+√x) ≐ 4 − 2 ln 3 | Proved modulo 5 admissions |

**The review.** A skeptic could not make a substitution step prove a
false equation from true obligations. It did produce a false theorem
reported *Proved modulo 9 admissions*. There, x := 5/(2t − 5) created a pole
at t = 5/2, and the false `2t − 5 # 0` was admitted, tagged `none`, among
the regularity admissions. `ftc` alone had the same hole.
- **The fix, E50:** F3 now also tries the rational roots of an
  obligation's one-variable polynomial pieces. That case is refused at the
  substitution.
- **Still undecided:** irrational poles such as `t² − 2 # 0` stay admitted,
  tagged `none`. Sturm sequences are the future exact method.
- **Also fixed:** a crash on huge literal powers (`t^20000`), and one on
  very deep substitutions. The iterative `subst` agrees with the old one on
  all 1,010 cases of a differential test.

**Design errors found**, folded into `DESIGN.md`:
- §8.1's worked example `x := sin t`, marked "✓ legal", is refused, since
  its endpoint gives 1 ≠ π²/4. §8.6's probe value for it was wrong too.
- §6.4 did not say where φ′'s side conditions live.
- §11.1's endpoint obligation is two obligations, not one.

## Since: consolidation, and a false `Proved` caught in review (2026-09-24)

Decisions E51–E58 in `p1_expected.py`. Where the owner decided, it is noted:
- **P1.1 from the sheet's goal** (E52) joins the main proofs as the
  official route. Every planted bug and mutation is re-traced against it.
- **Reversed ranges everywhere** (E56, owner). With non-literal ends, a
  range's interval is built from whichever order discharge proves. If
  neither order is proved, the step is refused with `orientation-undecided`.
  Orders are decided only when a key uses the range, and each decision is
  memoised. So ∫_{π/2}^0 2x installs and is proved by `ftc` alone.
- **`int_flip`** (E51, owner): ∫_a^b f → ∫_b^a −f.
- **The non-strict sign product** (E53). 1 − x² ≥ 0 on [0, 1] is
  −(x − 1)(x + 1).
- **Six entries** (E54): `pyth`, `pyth_cos`, `sin_nonneg_on`,
  `cos_nonneg_on`, `cos_le_one` and `cos_ge_neg_one`.
- **QC1**: ∫₀¹ √(1 − x²) = π/4 by x := cos θ, Proved modulo 5 admissions,
  all regularity.

**A false `Proved.` reached the committed kernel, and review caught it
before any push.** `rewrite pyth` with u := D[x](|x|), or with a divergent
integral, erased the term, and `close 1` then reported a plain `Proved.`.
`pyth` is the first entry whose right side drops its variable, and
`rewrite`'s exact-match path skipped the check that refuses an Int or D.
- **E57, the fix:** no rule may erase an Int or D node unless its
  definedness is owed, which means never until regularity lands. The check
  runs on every match path, and `ftc`, `int_subst` and `int_flip` also
  refuse an Int or D in an integral's limits.
- **The second review:** it was independent and covered the whole erasure
  class, including `ln(−1)`, `1/0` and `tan(π/2)` hidden in an
  instantiation. It found no remaining way to a false `Proved`.
- **Its minor findings are fixed:**
  - each half of E57's check is now tested on its own;
  - 0⁰ is 1 for an integer exponent 0 (E58);
  - a memo stability issue.
- **Also fixed:** a 33-second install caused by deciding orders eagerly now
  takes under a millisecond.

The suite is at 655 of 655.

## Since: regularity, and stage 1's kernel complete (2026-09-25)

Decisions E59–E70 in `p1_expected.py`, with section 18 holding the review
items. The owner delegated the open design calls; the ones taken on that
basis are marked as such in the data and below.
- **What `e ∈ Cᵏ(D)` means** (E59): k is 0 or 1. C¹ means C¹ on a
  neighbourhood of every point, so it is the stronger reading at a closed
  end.
- **Regularity is a certificate-checked discharge method** (E60–E63).
  - The untrusted search proposes a derivation that follows the term's
    structure.
  - The trusted checker in `discharge.py` takes each rule from the term's
    head, never from the certificate. It rebuilds every side condition from
    one natural-domain table, `kernel/domains.py`, shared with the formers,
    and decides each on exactly the Reg's own domain.
  - A Reg is refuted only through a definedness side. A failed C¹-only
    condition decides nothing.
- **Q23's formers** (E64 and E66, the owner's direction). A statable
  integral owes its integrand in C⁰ on its range, and `D[x] e` owes e in C¹
  at its position. `ring` and `field` then read both as atoms, keyed by
  their tree. Improper integrals are still refused.
- **Deferred, on the owner's delegation:**
  - convergence and `diverges` (E65), since 1/x is continuous on [1, ∞) but
    its integral diverges;
  - integration by parts (E67). "Solve for I" is shown on hand-built goals,
    with I = ∫₀^π eˣ sin x's integrability owed and discharged.

**Every proof reads a plain `Proved.`, with 0 admissions:** P1.1 (from the
sheet's goal, and the t-form), the fallback, P1.2 in both forms, S1–S3,
S3-ring, SUB1, S2R, SUB2 and QC1.

**The review** found no false `Proved`. It tried:
- hand-built false certificates, and a fuzz of 15,000 mutated ones;
- poles and kinks in `ftc` and `int_subst`;
- atoms owed at one domain and cancelled at another.

Its findings are fixed:
- a crash freezing very deep certificates, a regression, now iterative
  with an overflow read as "no certificate";
- a test gap: one soundness mutation of the trusted checker, letting a side
  be assumed in its own domain, survived the whole suite, and it is now
  pinned by must-reject cases;
- the parser crashing on very deep nesting, now refused with
  `nesting-too-deep`.

A vacuously true Reg whose closed side is false is refused on purpose, as
closed formers always were.

**Stage 1's kernel is complete.** The suite was at 882 of 882 then. The
API followed, and then (2026-09-25) items P, I and T: `int_parts`,
`int_improper` with `limits.py` and the sign node, and `trig_norm`
(p1_expected sections 19-23). The suite was at 992 of 992 then. Item L
followed (section 25): order goals, `taylor_lagrange`, `bound` and C^k,
for readiness P3 part 1, at 1027 of 1027. Item U followed (section 26,
2026-09-26): `verify`, the hyperbolic derivative rules and entries, and
unit 00's eleven goals (UNIT00.md), at 1068 of 1068. Item G followed
(section 27): field reads an atom's argument up to exact cancellation
(UNIT00.md G8), at 1088. Item K followed (section 28): strict Taylor
bounds and bound's scale, for unit 00 P3(b), at 1097. Item Q followed
(section 29): discharge method 7, clearing a denominator of certified
sign (UNIT00.md G9), at 1111. Item O followed (section 30): assumptions
about declared functions and §6.5's `quad_t`, `sep_autonomous` and
`energy_integral` (UNIT00.md G6), with the section 29 review folded in
(E158). The suite is at 1134 of 1134 on Python 3.12.

## What is in `kernel/`

| File | Role |
|---|---|
| `GRAMMAR.md` | the concrete grammar, frozen |
| `p1_expected.py` | both proofs as (move, args) data, expected obligations, cases, mutation expectations, frozen with a change log |
| `ARCHITECTURE.md` | modules, trust tiers, contracts, planted-bug mechanism |
| `terms.py` | trusted: nodes, parser, printer, goal checks |
| `entries.py`, `poly.py`, `field.py`, `deriv.py`, `kernel.py` | trusted: the §6.8 entries, `ring`/`field` (copied from the spike), §6.3, rules/tracker/handles/`step` |
| `discharge.py` | trusted: the certificate checkers (regularity and the sign node included) and the exact-value rewrite |
| `limits.py` | trusted: limits at an infinite end, for `int_improper` (p1_expected section 20) |
| `domains.py` | trusted: the one natural-domain table the formers and the regularity checker share |
| `tagger.py`, `search.py`, `refute.py`, `residual.py`, `schema.py` | untrusted: admission tags, certificate search, decided-false, residual rendering, the closed whitelist and E27 |
| `trig_norm.py` | untrusted: the §8.9 normaliser's proposal of entry instances, fenced and re-checked by the kernel (E88) |
| `proof_of_life.py` | the done script and regression suite (items 1–6 for P1, item 7 for the problem files) |
| `loader.py` | untrusted: reads a §16.4 problem file and drives its reference proof through `step()` |
| `problems/stage1/` | SUB1, S2R and SUB2, the substitution problem files |
| `problems/parts/`, `problems/improper/`, `problems/trig/` | readiness P1(1) by parts, readiness P5 and P2, and ∫₀^{π/2} cos²t |
| `problems/stage0/` | S1–S3 as problem files, and `expected.py`, their hand-written expected results |
| `test_field.py`, `test_grammar.py` | unit and property tests |

`spike/` is untouched.
