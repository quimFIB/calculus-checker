A calculus exploration environment — a single .html page where you try a substitution, see the goal change, retract it for free, and get told what the new shape matches, with a kernel that refuses any move that is not actually valid. A tool in its own right; `mechanics-to-relativity` is its first corpus and its acceptance target.

**It graduates to `tools/`**, with `mechanics-to-relativity` pointing at it —
one way, course to tool (§18 Q6, settled revision 6). The course problems are a
separable package `./calc` loads, not part of the tool, which is §1's
replaceability test made operational.

Design, plus two spikes: the tool itself is not built. Design 2026-09-20,
stage 0b first pass 2026-09-21, decoupling pass and stage 0 first pass
2026-09-22, the stage 0c `ring`/`field` spike (`spike/ring/`) and a recognizer
spike (`spike/recognizer/`) 2026-09-23.

`DESIGN.md` is the design; `STAGE0.md` is the first attempt to *use* it —
forty-one goals and two table sweeps, fourteen gaps, all folded back in.

`DESIGN.md` is **revision 9** (2026-09-23), and is **the whole record** — the adversarial review
that produced revision 2 and the revision-1 draft were folded into it and
deleted before the project was under version control. Its closing sections
carry what the review established, what was attacked and held, and how much to
trust what the document states.

**The idea that drives it (§1).** The learner has CS, logic and formal methods,
and no calculus. So they already own the loop — goal, tactic, backtrack — and
own none of the vocabulary. The gap is *which move to make*, not sign-and-factor
bookkeeping, and the readiness sheet's cure (volume) is right but unaffordable
without feedback. The tool makes each attempt cost seconds and say why it
failed. **A fluency trainer, not a fluency substitute.**

**The boundary (§1).** The course is the corpus and the motivation, not the
specification. It determines *what must work*; it must not determine *how the
tool works*. The test: if the course were replaced tomorrow, only the problem
files, §13's coverage claims and the recognizer's row priorities should change.

**What v1 is and is not.** In: the move palette, the antiderivative card, the
recognizer, the progress signal, the attempt tree, the hint ladder, the
speculative probe, `ftc` by differentiate-and-check, residual reporting, the
obligation pane, `trig_norm` (§8.9), **`abs` in goals** and the **`diverges`
judgement** — the last of which makes the FTC-across-a-pole error refutable
rather than merely unprovable. Out, deliberately and on pedagogical rather than architectural
grounds: **`auto`, `solve` and the integrator** — prepared for, not built (§2,
§8.2). Also out for now: certified numerics, dimensions, series.

**How it is built (§16).** Three tiers: a **Python kernel** (terms, rules,
`ring`/`field`, `ftc`, obligations), a **Python assistance layer** (recognizer,
palette, progress signal, attempt tree), and a **browser UI** over a local JSON
API. `./calc` starts it. Standard library only in v1 — `fractions.Fraction`,
`http.server`, vendored KaTeX — which is how the `./mr` house rule survives:
*a thing untouched for six months must still open.*

**One rule that must not bend (§15.5).** SymPy never enters the kernel.
`sympy.simplify` is a heuristic normaliser and §3 is the argument for why one
cannot be trusted with an equality. `ring`/`field` are bespoke and reflective;
SymPy lives in tier 2 and at build time.

**Verification is deferred and unbound from any prover** (§14): a possibility
the design stays open to, not a plan. §14 separates **(A)** the rules being
true theorems — the cheap 80%, and all §15's claim rests on — from **(B)** a
verified kernel program, which would be a rewrite in a prover's extraction
target and is not planned. The first implementation is not formally verified
and says so in its own UI; §15.4 states what carries soundness instead.

**The falsifier.** §17's gate: work readiness P1–P5 and unit 00's quadrature
cases, and plot the maximum hint rung per problem against time. If the average
does not fall, the tool is a crutch rather than a trainer and §1's claim has
failed. ~4,300 lines to find out.

Read `DESIGN.md` §1, §8.5 and §17 first — the idea, the product, and what would
kill it. Nothing else is required reading before stage 1; Waterproof's course
evaluations are optional, since adoption evidence for the class is not this
tool's falsifier.

## Start here: the proof-of-life (chosen 2026-09-23, reviewed the same day)

The next step is the first real code: **a headless kernel that proves
readiness P1** (`DESIGN.md` §11.1 and §11.2). It is the smallest thing that
runs the whole check-mode loop end to end, and it should land inside the
roughly four-month motivation window §17 warns about. A six-dimension review,
with each finding checked by a skeptic, shaped what follows. Its design-level
findings are `DESIGN.md` revision 9.

`ring`/`field` are promoted from the ring spike rather than rewritten (see
*Scope*).

**Read for this milestone**, beyond §1, §8.5 and §17:
- §5.3–§5.4 (discharge, obligations);
- §6.1–§6.4 (structural rules, algebra, derivatives, `ftc`);
- §6.8 (the named entries);
- §9 (`?A` and `close`);
- §11 (the two proofs);
- §15.3 (handles);
- §18 Q21 (the matcher).

**Where things go, by default:** the kernel in `kernel/` and the done script
as `kernel/proof_of_life.py`. `spike/` stays untouched as the record.

### Before any code

1. **Write the concrete grammar**: precedence, reserved names (`e` vs
   `e_const`), declared function symbols only, binders, `?A`, endpoints and
   domains. The spike's `terms.py` reads `e^x` with `e` as a variable,
   `x(x+1)` as a call to an undeclared function, and `x^2^3` as a real power.
2. **Write both P1 proofs out step by step** as (move, args) data, before any
   code:
   - every §6.8 entry pinned by its exact statement
     (`atan_one_sqrt3 : atan(1/sqrt 3) ≐ pi/6`);
   - every rewrite explicitly instantiated;
   - `rewrite`'s matching settled, which is §18 Q21. The default to trial is
     that the left-hand side and target agree after **ring**-normalising atom
     arguments.
3. **Write the expected obligation lists by hand**, each obligation with its
   domain and open and closed intervals kept distinct. Take them from §6.3,
   §6.4's four split `ftc` premises, and §11 as revision 9 corrected it. With
   discharge stubbed, these lists are the only thing the milestone shows about
   soundness.

### The route

**P1.1 starts from §11.1's substituted goal**
`Int[t = 0 .. pi/2] sin(sqrt(t^2)) * (2*t) ≐ ?A`. It runs §11.1's remaining
steps: `rewrite sqrt_sq`, owing `0 ≤ t` by range and `pi_pos`; then `ftc`
with F := 2 sin t − 2t cos t; then the endpoint rewrites; then `close`.
`int_subst` waits for the next step.

This route exercises `sqrt_sq` on a bound variable, which §11 calls the whole
argument for the design, and the matcher's binder case. *(A direct route on
x, with F = 2 sin√x − 2√x cos√x, also works: `field` owes `2·sqrt x # 0`,
`d_sqrt` owes `x > 0`, both on (0, π²/4), and `sqrt(pi^2/4)` still needs
`pi_pos`. It never touches `sqrt_sq` on a bound variable, so it is the
fallback.)*

**P1.2 is §11.2 as revision 9 states it**: `ftc` with the partial-fraction
F, the check `field [sqrt_sq_val 3]`, the endpoint rewrites, and `close`
owing `3*sqrt 3 # 0`.

### Scope

**In:**
- **Terms, parser and plain-text printer**, rewritten against §5.1. The spike's
  are spike-grade.
- **`ring`/`field` with facts.** `poly.py` and `field.py`'s normaliser and fact
  reduction are near kernel quality; copy them, do not move them. Their
  *interface* is not:
  - facts become theorem handles, and the result inherits each fact's
    obligations (`3 ≥ 0` from `sqrt_sq_val 3`);
  - obligations become (term, domain) pairs keyed structurally, not strings;
  - there is no public `holds` flag;
  - residual formatting moves out of the trusted files.
- **`deriv` as kernel steps that collect side conditions** (§6.3, with revision
  7's `d_const`, and `-u` and `u/v` routed through `ring`/`field`).
- **`ftc`** with §6.4's four premises.
- **§6.1's `refl`, `trans` and `cong`, `norm_num`, and `rewrite`** per the
  Q21 default, with revision 9's restriction under `D[x]`.
- **`close` for `?A`**, with the trusted scope check and the `closed`
  whitelist (§9).
- **A minimal linear proof state**: the goal (which may carry `?A`), live
  obligations and handles. Moves go through an in-process
  `step(state, move, args)` shaped like §16.3's `/step`, so the script survives
  as the regression suite.
- **The §6.8 entries P1 uses:** `sqrt_sq`, `pi_pos`, `sin_pi_half`,
  `cos_pi_half`, `sin_zero`, `ln_one`, `atan_one_sqrt3`, `atan_odd`,
  `sqrt_sq_val` and `sqrt_pos`. `sqrt_pos` is named but not used until
  discharge exists.
- **§15.3's handles by default**, with the sentinel only if handles prove
  awkward. The script's header says which is in force.

**Stubbed:** discharge (§5.3). The obligation tracker keeps §5.4's three
states. Each undischarged side condition becomes a kernel-minted
**admission** with reason `discharge not built`, tagged with the §5.3 method or
§6.8 cite expected to close it. **An obligation tagged `none` fails the
milestone**, which is how the π gap would have shown up. The result reads
`Proved modulo N admissions`, never `Proved`. Literal divisors closed by
`norm_num` count as discharged.

**Out:** `int_subst`, real discharge, regularity beyond listing it, the HTTP
API, the UI, the recognizer, and §11.2's `approx` step, which is stage 2.

### Done when

A script with no UI, which stays as the regression suite, does all of this:

1. **Proves** P1.1 ≐ 2 and P1.2 ≐ ⅓ ln 2 + π/(3√3). It also accepts P1.2 in
   the form ⅓ ln 2 + π√3/9.
2. **Asserts each obligation list**, with domains, against the list written
   before coding, and checks every admission's tag.
3. **Fails on three planted bugs:** `d_ln` emitting nothing; `ftc`'s derivative
   premise attached to [a,b] instead of (a,b); the tracker dropping one
   obligation.
4. **Rejects wrong answers, asserting the residual each time:**
   - P1.1 with F := sin t − t cos t (residual −t·sin t);
   - P1.2 with ln coefficient 1/3 in place of 1/6;
   - P1.2 without the `sqrt_sq_val` fact.
5. **Refuses bad moves:**
   - rewriting `D[x] sqrt(x^2)` with `sqrt_sq` (§6.1, revision 9);
   - `close ?A := t` with t bound;
   - `close ?A := Int[x = 0 .. 1] 1/(1 + x^3)`;
   - a raw equation passed to `field` as a fact;
   - the handle forgeries: constructing a theorem directly or through
     `object.__new__`, a copy or pickle round trip used as a handle, a
     fabricated handle id, a direct write to the tracker, and printing
     `Proved.` while N > 0.
6. **Round-trips the parser**: `parse(print(t)) ≡ t` as structure, over every
   term in the script plus `-x^2`, `sin x^2`, `1/sqrt 3*x` and `pi^2/4`. Each
   parsed goal is echoed before it is proved, and undeclared function symbols
   are refused.

**Then:** run the first course goals through the kernel as its first problem
files (§16.4), fixing each encoding until the kernel accepts it with a correct
obligation list. Seed them with `STAGE0.md`'s S1–S3:

- S1 is ∫₀¹ 3x²+2x;
- S2 is ∫₀¹ x·exp(x²);
- S3's current encoding is below.

`STAGE0.md` is a frozen record, and its S3 is the revision-5 version.

```
problem stage0.S3                         -- nontrivial domain obligation
  answer schema  closed
  goal  Int[x = 1 .. e_const] (ln x)/x  ≐  ?A
proof
  step ftc  F := (ln x)^2 / 2
       obl  F ∈ C⁰([1,e_const]) ∧ F ∈ C¹((1,e_const))   by reg
            ⤷ obl  x > 0      @ [1,e_const]  by range, e_gt_one; linear
       obl  D[x] F ≐ (ln x)/x    @ (1,e_const)  by deriv; field
            ⤷ obl  x > 0      @ (1,e_const)  (d_ln)    by range, e_gt_one; linear
            ⤷ obl  x # 0      @ (1,e_const)  (field)   by range, e_gt_one; linear
       obl  (ln x)/x ∈ C⁰([1,e_const])                  by reg
            ⤷ obl  x > 0      @ [1,e_const]  by range, e_gt_one; linear
  step rewrite [ln_e, ln_one]
  step close  ?A := 1/2                     by norm_num
qed
```

Restated for revision 9, and checked against `spike/ring/`: `field` closes
the derivative owing `x # 0`, and the close needs `ln_e` and `ln_one`. It
needs `e_gt_one` (§6.8), so add that to the §6.8 entries when S3 is used.

**After it:** the rest of stage 1 (real discharge, `int_subst`, regularity),
then the in-process `step` becomes §16.3's API, then the recognizer table
scored on a held-out set (revision 8), then the UI.

## What has been done, in order

1. **§17 stage 0 — first pass done 2026-09-22, see `STAGE0.md`.** Fifteen goals
   encoded against §5.1 and §6 as they stand, every one SymPy-verified; seven
   gaps; a second pass took it to **thirty goals and ten gaps**, three of them
   design defects. **Nine are folded into `DESIGN.md`** with no mechanism
   changed. It also **reframed the stage**, and §17 is rewritten to match: the
   decision-relevant output is the gap list, not the authoring rate, because
   the drafting is mechanical once the course has supplied the mathematics.
   The two table sweeps it left owed are also run: §6.3 now states all
   twenty-three derivative right-hand sides, and §6.8 enumerates to **64
   entries** against the recount's "20 or 45". Both decisions are taken: §5.3
   gains a `by sign product` method (gap 11), and §8.9 adds **`trig_norm`**,
   a trig canonicaliser that makes the FTC residual check decidable for one
   base angle (gap 9) — the only new component, untrusted, stage 1. A third
   pass tested it on eleven multiple-angle goals: it holds, with the correction
   that it is a **fallback after `field` fails**, not a preprocessor.
2. **The `ring` spike** (§17 stage 0c) — sparse polynomials over ℚ[atoms] with
   `field`'s nonvanishing obligations, in Python, against §11.2's flagship
   residual. It is the one component whose bug is a false `Proved`.
   **Closed 2026-09-23** — `spike/ring/`, folded into `DESIGN.md` as
   revision 7. It closes §11.2 with 28 tests passing, including property
   tests against exact evaluation. The finding that mattered: §11.2's
   `rewrite sqrt_sq_val` could never fire, so `field` now takes proven facts.
   Timings settle §18 Q18: §11.2 runs in ~1 ms, and every corpus-shaped case
   is ≥10× inside the 100 ms budget.
3. **The recognizer table** — content rather than code, and where the work
   pays most. **Spiked 2026-09-23** (`spike/recognizer/README.md`, folded into
   `DESIGN.md` as revision 8). §8.5's table as written names the course's technique for 15
   of 22 target integrals, and 3 of 9 held out from units 01–10. Five rows
   fitted to the misses took the first set to 22/22 and the held-out set
   nowhere. So the cost is not writing rows. It is matchers that see through
   algebra (normal forms, `trig_norm`) and a chain-rule row §8.5 lacks. Both
   want stage 1's kernel first, so revision 8 puts **stage 1's headless
   kernel next**, and this table after it.

**Stage 0b is closed** (2026-09-21 and 2026-09-22; setup and notes in
`_scratch/holpy-trial/` — outside this tool, and a dangling pointer if it is ever published; findings in §4.2). Its verdict: reimplement the core
rather than reuse it, take four things from HolPy as inputs to weigh, and do
not take its interaction as inspiration — that last is a verdict on HolPy, not
on §16's request-per-move boundary.
