A calculus exploration environment — a single .html page where you try a substitution, see the goal change, retract it for free, and get told what the new shape matches, with a kernel that refuses any move that is not actually valid. A tool in its own right; `mechanics-to-relativity` is its first corpus and its acceptance target.

**It graduates to `tools/`**, with `mechanics-to-relativity` pointing at it —
one way, course to tool (§18 Q6, settled revision 6). The course problems are a
separable package `./calc` loads, not part of the tool, which is §1's
replaceability test made operational.

A design, two spikes, and **a headless kernel that proves readiness P1**
(`kernel/`, the proof-of-life, 2026-09-24). The tool a learner would use is not
built yet: there is no API, UI or assistance tier, and discharge is stubbed.
Design 2026-09-20, stage 0b first pass 2026-09-21, decoupling pass and stage 0
first pass 2026-09-22, the stage 0c `ring`/`field` spike (`spike/ring/`) and a
recognizer spike (`spike/recognizer/`) 2026-09-23, the proof-of-life kernel
2026-09-23 to 2026-09-24.

`DESIGN.md` is the design; `STAGE0.md` is the first attempt to *use* it —
forty-one goals and two table sweeps, fourteen gaps, all folded back in.
`PROOF_OF_LIFE.md` is the record of the first code against it: what was
built, what was decided, and what it found wrong in the design.

`DESIGN.md` is **revision 10** (2026-09-24), and is **the whole record** — the adversarial review
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
failed.

Read `DESIGN.md` §1, §8.5 and §17 first — the idea, the product, and what would
kill it. Nothing else is required reading before stage 1; Waterproof's course
evaluations are optional, since adoption evidence for the class is not this
tool's falsifier.

## Start here: the first problem files (S1–S3)

The proof-of-life is done: `python3 kernel/proof_of_life.py` proves both parts
of readiness P1 and passes 225 checks (`PROOF_OF_LIFE.md`). The next step is
the one it was built to unlock. **Run the first course goals through the
kernel as its first problem files** (§16.4), and fix each encoding until the
kernel accepts it with a correct obligation list. §17 says the kernel, not a
reader, is the right reviewer of an encoding.

**Read for this step**, beyond §1, §8.5 and §17:
- `PROOF_OF_LIFE.md`, for what the kernel does now and its caveats;
- `kernel/ARCHITECTURE.md`, for the `step()` contract and the tracker;
- §16.4, for the problem files;
- §6.8, for the named entries S3 needs.

**What it involves:**
1. **A problem-file format and loader**, the `problem … proof … qed` shape
   below, driving `step()`. The loader is untrusted: it only feeds moves to
   the kernel. The goal still parses through `terms.parse_goal`.
2. **The goals as files, seeded with `STAGE0.md`'s S1–S3:**
   - S1 is ∫₀¹ 3x²+2x;
   - S2 is ∫₀¹ x·exp(x²), which `ftc` closes with F := exp(x²)/2 and no
     substitution;
   - S3's current encoding is below.
3. **For each goal, write the expected obligation list by hand before
   running it**, as the proof-of-life did. The mismatches are the output:
   either the encoding or the kernel is wrong, and each one is a finding.
4. **Add the §6.8 entries they need** (`ln_e`, `e_gt_one`) to
   `kernel/entries.py`, pinned by their exact statements.

**Done when** each of S1–S3 is accepted with its hand-written obligation list,
that list is asserted by the regression suite, and every mismatch found along
the way is either fixed or listed for `DESIGN.md`.

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
Revision 10 adds more: `ln x` now owes `x > 0` where it enters (E26), so the
goal owes it on [1, e_const] at installation. The range also owes its
orientation `1 ≤ e_const` (E4). Neither is in the block above, which is why
step 3 writes the list by hand before running it.

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
4. **The proof-of-life — done 2026-09-24, see `PROOF_OF_LIFE.md`.** A
   headless kernel in `kernel/` proves readiness P1: P1.1 ≐ 2 modulo 6
   admissions, and P1.2 ≐ ⅓ ln 2 + π/(3√3), in both forms, modulo 14 and 13.
   Discharge is stubbed, so the verdict is never a bare `Proved`.
   `python3 kernel/proof_of_life.py` stays as the regression suite, with 225
   checks. It covers the obligation lists written before any code, planted
   bugs, wrong answers with residuals, refused moves and handle forgeries. The
   spec came first and was frozen (`kernel/GRAMMAR.md`,
   `kernel/p1_expected.py`). It found holes in the design, folded in as
   revision 10:
   - `ftc` did not require a ≤ b, so it proved the divergent ∫₁⁻¹ 1/x² = 2;
   - partial functions owed nothing, so `0*ln(-1)` proved. They now owe
     their natural domain (E26).

**Stage 0b is closed** (2026-09-21 and 2026-09-22; setup and notes in
`_scratch/holpy-trial/` — outside this tool, and a dangling pointer if it is ever published; findings in §4.2). Its verdict: reimplement the core
rather than reuse it, take four things from HolPy as inputs to weigh, and do
not take its interaction as inspiration — that last is a verdict on HolPy, not
on §16's request-per-move boundary.
