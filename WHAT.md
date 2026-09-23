A calculus exploration environment — a single .html page where you try a substitution, see the goal change, retract it for free, and get told what the new shape matches, with a kernel that refuses any move that is not actually valid. A tool in its own right; `mechanics-to-relativity` is its first corpus and its acceptance target.

**It graduates to `tools/`**, with `mechanics-to-relativity` pointing at it —
one way, course to tool (§18 Q6, settled revision 6). The course problems are a
separable package `./calc` loads, not part of the tool, which is §1's
replaceability test made operational.

Design, plus one spike: the tool itself is not built. Design 2026-09-20,
stage 0b first pass 2026-09-21, decoupling pass and stage 0 first pass
2026-09-22, the stage 0c `ring`/`field` spike (`spike/ring/`) and a recognizer
spike (`spike/recognizer/`) 2026-09-23.

`DESIGN.md` is the design; `STAGE0.md` is the first attempt to *use* it —
forty-one goals and two table sweeps, fourteen gaps, all folded back in.

`DESIGN.md` is **revision 8** (2026-09-23), and is **the whole record** — the adversarial review
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
failed. ~4,300 lines and 436–767 hours to find out.

Read `DESIGN.md` §1, §8.5 and §17 first — the idea, the product, and what would
kill it. Nothing else is required reading before stage 1; Waterproof's course
evaluations are optional, since adoption evidence for the class is not this
tool's falsifier.

Next, in order:

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
   residual. A few days; it is the widest single range in §17 and the one
   component whose bug is a false `Proved`.
   **Closed 2026-09-23** — `spike/ring/`, folded into `DESIGN.md` as
   revision 7. It closes §11.2 with 28 tests passing, including property
   tests against exact evaluation. The finding that mattered: §11.2's
   `rewrite sqrt_sq_val` could never fire, so `field` now takes proven facts.
   Timings settle §18 Q18: §11.2 runs in ~1 ms, and every corpus-shaped case
   is ≥10× inside the 100 ms budget. It does *not* price writing `ring`/`field`
   by hand, since Claude wrote it.
3. Then the recognizer table, which is content rather than code and is where
   hours buy the most.
   **Spiked 2026-09-23** (`spike/recognizer/README.md`, folded into
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
