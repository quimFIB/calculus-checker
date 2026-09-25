A calculus exploration environment — a single .html page where you try a substitution, see the goal change, retract it for free, and get told what the new shape matches, with a kernel that refuses any move that is not actually valid. A tool in its own right; `mechanics-to-relativity` is its first corpus and its acceptance target.

**It graduates to `tools/`**, with `mechanics-to-relativity` pointing at it —
one way, course to tool (§18 Q6, settled revision 6). The course problems are a
separable package `./calc` loads, not part of the tool, which is §1's
replaceability test made operational.

A design, two spikes, and **a complete stage-1 headless kernel** that proves
readiness P1 from the sheet's own goal and stage 0's S1–S3 as plain
`Proved.`, with every obligation discharged by a checked certificate
(`kernel/`, 2026-09-23 to 2026-09-25). The tool a learner would use is not
built yet: there is a JSON API (`app/`), but no UI or assistance tier.
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

## Start here: stage 1's kernel is complete

**Every proof reads a plain `Proved.`**, with nothing admitted. That covers
readiness P1 from the sheet's own goal, stage 0's S1–S3, three substitution
files, ∫₀¹ √(1 − x²) = π/4, readiness P1(1) by parts, readiness P5 and P2
(improper integrals over infinite ranges), and ∫₀^{π/2} cos²t = π/4.
`python3.12 kernel/proof_of_life.py` passes 992 checks (`PROOF_OF_LIFE.md`).
Discharge, `int_subst`, `int_flip` and regularity are built, and so are
§18 Q23's formers: integrals and derivatives owe their own definedness.

**Built 2026-09-25 for the mechanics course** (p1_expected sections 19–23),
each spec-first and then reviewed by an independent skeptic:
- `int_parts`, and `ftc` at any Int by occurrence;
- `int_improper` over an infinite end, with a trusted limit evaluator
  (`kernel/limits.py`) and discharge's `sign node` method for quotients,
  sums and powers;
- `trig_norm` (§8.9) as ftc's fallback after `field` fails, with `field`'s
  facts reduced in order (E86) and seven trig entries (E87).

**Deliberately not built yet:**
- the `diverges` judgement, and integrands singular at a FINITE end (unit
  00 P7);
- `int_improper` for trig integrands (e^-x sin x needs a squeeze law);
- the cycle case of `int_parts` (E74), hyperbolic atoms in `trig_norm`;
- Sturm sequences, for exact sign decisions on irrational poles (not in
  the mechanics course).

**The JSON API is up** (`app/API.md`, 2026-09-25): `./calc` serves §16.3's
routes on 127.0.0.1, over the attempt tree, with `/palette` refusing
`not-built`. `python3 -m unittest discover -s app` replays every
problem file through it against the loader.

**The check-mode page is up** (`app/PAGE.md`, revision 2, 2026-09-25):
`./calc` serves it at `http://127.0.0.1:8765/`, laid out like rocq-mode. You
type a tactic script in the centre (`app/SCRIPT.md`, e.g. `ftc x^3 + x^2 by
ring.`), step through it with Alt+↓ / Alt+↑ / Ctrl+Enter, and the goals,
obligations and the last response show on the right. The checked region
is shaded, and editing inside it retracts to that sentence. The attempt
tree keeps retracted branches. The `?`, `??` and `???` buttons show hint
rungs 1–3 (below). No palette or KaTeX yet.
`app/test_page.py` drives it in a headless browser when Playwright is
installed.

**The recognizer table is built** (`app/assist/RECOGNIZER.md`, revision 1,
2026-09-25): §8.5's fifteen rows, read on the kernel's `field` normal
form, answer `GET /hint` rungs 1–3. **Held-out score, table version 1:
strict 18/28 (64%), lenient 20/28 (71%)** on 31 integrals from units
11–26 (3 labelled "other", which has no row), labelled by a separate
agent before any row was written and committed unread. Of the 10 misses,
6 are silent and 2 wrong: 4 silent and 2 lenient are "identity first"
labels, where row 1's unbuilt `trig_norm` clause is the likely gap; the
other misses are one chain-rule and one standard silent, a trig
substitution read as hyperbolic (a symbol's sign, as U09-P1 in the
development set), and a parts integrand read as root substitution. The
development set scores strict 28/30. Per revision 8, no row changes
because of the held-out set; version 2 is scored on a fresh one.
`python3.12 app/assist/score.py heldout` prints it.

**Next,** per §17: the full UI (palette, progress, KaTeX), and recognizer
version 2 (the `trig_norm` clause of row 1) with a fresh held-out set.

**Python version:** the suite passes 992 of 992 on Python 3.12.
On 3.11 five deep-term checks fail with `RecursionError` in dataclass
`__eq__`, so 3.12 is the floor in practice.

**Pushing:** commits land locally. Push to `origin`
(`github.com/quimFIB/calculus-checker`) only with the owner's explicit
approval, each time.

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
5. **The first problem files, S1–S3 — done 2026-09-24.** They are §16.4's
   `.json` problem files in `kernel/problems/stage0/`, each carrying its
   reference proof. An untrusted `kernel/loader.py` drives them through
   `step()`, and item 7 of the regression suite checks them against
   `expected.py`, which was written by hand before any code ran. The kernel
   matched it on every assertion first time, and a skeptic's 18 planted bugs
   were all caught. S1 and S2 are proved modulo 3 admissions each, and S3
   modulo 9. The step added four §6.8 entries: `ln_e`, `e_gt_one`,
   `exp_zero` and `exp_one`. Its findings are in `expected.py`'s
   `FINDINGS`:
   - `WHAT.md`'s S3 sketch missed four obligations and misattributed
     `e_gt_one`;
   - §9's `closed` schema accepts an unevaluated F(b) − F(a), so the §6.8
     entries are never actually required.
6. **Closed answers must be fully evaluated (E27) — done 2026-09-24.** By
   the owner's decision, an unevaluated F(b) − F(a) is refused with
   `close-not-evaluated`, which names the §6.8 move still available. The
   check is untrusted and runs last in `close`. The spec was committed before
   the code, and a skeptic's review was folded in. See `DESIGN.md` §9 and
   `PROOF_OF_LIFE.md`.
7. **Real discharge (§5.3) — done 2026-09-24.** Obligations are now proved
   by certificates. An untrusted search proposes one (Fourier–Motzkin for
   linear goals, by the owner's decision to bring it into stage 1), and a
   small trusted checker verifies it. An obligation decided false refuses
   the step (§18 Q22, settled). Every P1 and stage-0 proof went from
   modulo 6–14 admissions to modulo 3, leaving only regularity. The spec was
   committed before the code. A skeptic found no false discharge across
   about 2,700 fuzzed obligations, and its findings are fixed: a crash on
   deep terms, one wrong refusal, mutable certificates, and slow
   refutation.
8. **`int_subst`, substitution in an integral (§6.4) — done 2026-09-24.**
   - **Both modes:** forward x := φ(t), and reverse u := g(x) (the learner's
     "let u = x²"), where the kernel checks integrand ≐ f(g(x))·g′(x).
   - **Endpoints and orientation:** the endpoints are decided in the step.
     A decreasing φ with symbolic ends becomes the flipped, oriented
     integral.
   - **Occurrence selector:** the same one `rewrite` uses.
   - **A √ sign fact** for the linear method.
   - **P1.1:** it now proves from the sheet's own goal, modulo 5
     admissions, all regularity.
   - **Problem files:** SUB1, S2R and SUB2 in `kernel/problems/stage1/`.
   - **Review:** a skeptic found no false substitution step. It did expose
     a missed pole, now refused by trying rational roots as counter-points
     (E50), and two crashes, now fixed.
9. **Consolidation — done 2026-09-24.**
   - **P1.1 from the sheet's own goal** is now the official route.
   - **Reversed ranges work everywhere** (E56, owner): the interval is built
     from whichever order discharge proves.
   - **`int_flip`** (owner): ∫_a^b f → ∫_b^a −f.
   - **The sign product closes non-strict goals.**
   - **Six trig entries:** `pyth`, `pyth_cos`, sign facts for sin and cos,
     and cos bounds.
   - **QC1:** ∫₀¹ √(1 − x²) = π/4 by x := cos θ.

   The skeptic found a **false plain `Proved.`**, caught before any push.
   `rewrite pyth` could erase an undefined `D` or a divergent `Int`. It is
   fixed by E57: no rule may erase an Int or D node. An independent second
   review found no further way to a false `Proved`. Its minors are fixed,
   including 0⁰ = 1 (E58).
10. **Regularity (§6.9) and §18 Q23's formers — done 2026-09-25. Stage 1's
    kernel is complete.**
    - **Checked certificates:** continuity and differentiability are
      discharged by certificates. The untrusted search proposes a derivation,
      and a trusted checker verifies it, taking each rule from the term's
      head and rebuilding every side condition from one shared table of
      natural domains.
    - **Q23:** integrals owe their integrand continuous on the range, and
      derivatives owe C¹. After that, `ring` treats both as atoms.
    - **Result:** every proof reads a plain `Proved.`
    - **Decisions taken on the owner's delegation:** convergence is deferred
      (continuity is not convergence), and integration by parts is out of
      scope.
    - **Review:** a skeptic found no false `Proved`. Its findings are fixed:
      a crash on deep certificates, a test gap where a soundness mutation
      survived, and a parser crash on very deep nesting.

11. **§16.3's JSON API — done 2026-09-25.** Spec first (`app/API.md`), then
    `app/`: the attempt tree (`session.py`, forks and retraction that keeps
    what it retracts, fact handles scoped to their path), the routes
    (`api.py`) and a localhost `http.server` (`server.py`). All untrusted:
    no proof state crosses the API, and every verdict is `kernel.report`'s.
    Not in this cut: the per-step timeout, progress and probe, persistence,
    and KaTeX (`/parse` returns the plain echo).

**Stage 0b is closed** (2026-09-21 and 2026-09-22; setup and notes in
`_scratch/holpy-trial/` — outside this tool, and a dangling pointer if it is ever published; findings in §4.2). Its verdict: reimplement the core
rather than reuse it, take four things from HolPy as inputs to weigh, and do
not take its interaction as inspiration — that last is a verdict on HolPy, not
on §16's request-per-move boundary.
