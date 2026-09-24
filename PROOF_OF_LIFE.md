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
`PASS: 225 of 225 checks passed`, exit 0; the unit tests
(`python3 -m unittest discover -s kernel`) pass 69 of 69. Both were re-run
independently after the last change, on 2026-09-24.

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

## What is in `kernel/`

| File | Role |
|---|---|
| `GRAMMAR.md` | the concrete grammar, frozen |
| `p1_expected.py` | both proofs as (move, args) data, expected obligations, cases, mutation expectations, frozen with a change log |
| `ARCHITECTURE.md` | modules, trust tiers, contracts, planted-bug mechanism |
| `terms.py` | trusted: nodes, parser, printer, goal checks |
| `entries.py`, `poly.py`, `field.py`, `deriv.py`, `kernel.py` | trusted: the §6.8 entries, `ring`/`field` (copied from the spike), §6.3, rules/tracker/handles/`step` |
| `tagger.py`, `residual.py`, `schema.py` | untrusted: admission tags, residual rendering, the closed whitelist |
| `proof_of_life.py` | the done script and regression suite |
| `test_field.py`, `test_grammar.py` | unit and property tests |

`spike/` is untouched.
