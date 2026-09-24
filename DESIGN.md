# A calculus proof checker

**Status: design, revision 10, 2026-09-24. The tool is not built, but its
kernel's first milestone is:** `WHAT.md`'s proof-of-life in `kernel/`, a
headless kernel that proves readiness P1. Two spikes sit beside it: stage 0c's
`ring`/`field` in `spike/ring/`, and the recognizer in `spike/recognizer/`
(§8.5, §17). This proposes a
system, states exactly what it would and would not guarantee, tests the design
against real problems from the course, and ends with what it would cost and
what would show it was the wrong idea.

**A tool in its own right**, and an addition for anyone undertaking
`mechanics-to-relativity`, which is its first corpus and its acceptance target
rather than its specification (§1, §18 Q6). The course problems are content
`./calc` loads, not part of the tool.

**Revision 6 is the first one written against use rather than review.**
Revisions 2–5 were shaped by an adversarial reading of the document; revision 6
is shaped by forty-one goals someone tried to *encode* in it (§17 stage 0,
`STAGE0.md`). That found fourteen gaps, four of them design defects, in a
document that had already survived 108 review findings — including an `ftc`
that could not close ∫₀¹ √(1−x²) and an `ode_verify` that named the wrong
normaliser. **The reading that matters: a rule table looks finished long before
it is, and the cheap way to find out is to try to use it.**

**What revision 2 changed.** An eleven-dimension adversarial review of
revision 1 produced 51 findings, of which 48 survived two rounds of adversarial
verification; its measurements are quoted throughout and its residue — what was
attacked and held, and how much to trust what is stated here — is in the
colophon. They are folded in here.
Three changes are large enough to name at the top:

1. **The scope is smaller.** "Units 00–21" and "the readiness sheet in full"
   were both rated optimistically, in places from unit titles. The honest
   target is the readiness sheet's **P1–P5**, **unit 00 complete**, and the
   scalar parts of 06/08/09 (§13).
2. **The kernel is not formally verified in the first implementation.** The
   rule ledger of §14 was revision 1's answer to "why trust the kernel". It
   is now explicitly **deferred until the tool has been used and found
   useful** (§14, §15.4). What carries soundness in v1 instead is stated
   exactly, including what that costs.
3. **The term language does not reach the plan's own stage-1 targets**, and
   the numeric representation does not terminate usefully on this document's
   own headline example. Both are cheap to fix and both are decisions that
   belong before any code (§5.1, §10).

**What revision 3 changed.** §1 was rewritten around a sharper statement of who
this is for, and the change propagates further than a framing usually does. The
gap is not *mechanical reliability over long chains*, as revision 1 had it from
the readiness sheet; it is **knowing which move to make**, in a learner who
already owns the goal-tactic-backtrack loop from formal methods and owns none
of the calculus vocabulary. So the tool's object is to make each attempt cost
seconds and say why it failed, which promotes the recognizer and the move
palette from stage-1b conveniences (§8.5) to the product, adds four components
revision 2 did not have — a **progress signal**, a **speculative probe**, an
**attempt tree** and a **hint ladder** — and moves `auto`, `solve` and the
integrator out of the first implementation on pedagogical rather than
architectural grounds (§2, §8.2). §17's stage plan and its gate were redone
against that: the gate now asks whether the average hint rung *falls* over a
corpus, which is a falsifier for §1's central claim and arrives at the end of
stage 1.

**What revisions 4–6 changed** is in the colophon in full. In short: revision 4
chose OCaml and revision 5 withdrew the premise, settling on **Python in three
tiers with a browser UI** and unbinding §14's verification from any prover.
**Revision 6** closed stage 0 and stage 0b, corrected two rule statements
(§6.4's `ftc`, §6.5's `ode_verify`), added a discharge method (§5.3's *sign
product*) and one component (§8.9's `trig_norm`), enumerated §6.8 to **70
entries** against a recount that had argued "20 or 45", and settled the three
grammar questions that were blocking the parser — **`abs` is admitted to
goals**, the **`diverges` judgement** is in, and limsup is deferred with a
trigger (§18 Q9–Q11). Nothing entered the trusted base and no part of §15's
claim moved.

**Revision 7 is the first one written against code.** Stage 0c built `ring`
and `field` (§17) and ran §11.2 through them, and the result corrects the
worked example this document calls its flagship. §11.2's script said
`deriv; rewrite sqrt_sq_val; field`, and **no such rewrite can fire**: the √3
that has to be squared is inside `((2x − 1)/sqrt 3)^2`, and *s*² only appears
once `field` has normalised the term. So **`field` now takes proven facts**
(§6.2) — a parameter on a trusted rule, stated with its soundness argument.
Smaller corrections: what `field` owes is specified as *every divisor in its
input* (§6.2); `ring`'s treatment of division is stated; `d_const` covers any
term free of x (§6.3); and §5.3's sign certificate tries the goal as written
first. **§18 Q18 is answered**: every case the corpus is shaped like runs at
least 10× inside §8.6's 100 ms, and §11.2 itself in about a millisecond, so
none of §16.2's mitigations is needed yet.

**Revision 8 measures the product half.** A recognizer spike ran §8.5's table
against the technique the course's own solutions use (§17's recognizer
corpus). **As written, it names the right technique for 15 of 22 target
integrals and for 3 of 9 held out from units 01–10.** Five rows fitted to the
first set's misses took it to 22/22 and moved the held-out score not at all.
The table's problem is not missing rows. It is that rows match the written form
rather than the mathematics, and that §8.5 has no row for the chain rule. So
§8.5 now matches on normalised goals, gains the chain-rule row and four
others, and states row 5 as ln|f| (§8.5). §17 now requires a held-out score,
and puts stage 1's kernel before the table. Nothing in §15 moved, and no rule
or trusted component changed.

**Revision 9 comes from reviewing the plan for the first milestone.** Six
reviewers, each checked by a skeptic, went over the proof-of-life handoff in
`WHAT.md`. They found four things wrong in the design itself, not just in the
handoff:
- **π and e have no sign.** §5.3 claimed `t ≥ 0` follows on [0, π/2]. It
  does not while π enters Fourier–Motzkin with no magnitude, and both parts of
  readiness P1 need it. The same holds for e_const over stage 0's [1, e].
  §6.8 gains `pi_pos` and `e_gt_one`. §5.3's justification of its
  satisfiability pre-check was also false (`pi < 3`); the pre-check is safe,
  for the converse reason, now stated.
- **§6.1 allowed an unsound rewrite.** It let `rewrite` carry a domain-limited
  equation under `D[x]`, which proves `D[x] sqrt(x^2) ≐ 1` at 0. It is now
  restricted to open domains.
- **§11's obligation lists were stale.** They still showed the closed-interval
  `ftc` of revision 5.

What `rewrite` matches up to was left open (§18 Q21), to be settled by
writing the P1 scripts out first. Revision 10 settles it.

**Revision 10 is the first one written against the kernel.** `WHAT.md`'s
proof-of-life is built in `kernel/`: a headless kernel, standard library only,
that proves both parts of readiness P1 — P1.1 ≐ 2, and P1.2 ≐ ⅓ ln 2 + π/(3√3)
in both of its accepted forms — **modulo 6 and 14 admissions**, because
discharge is stubbed and every undischarged obligation is admitted, tagged
with the §5.3 method expected to close it. Its regression script passes 225
checks: every obligation list against one written by hand before the code,
planted bugs, wrong answers with their residuals, refusals, and handle
forgeries. Building it found:
- **Two unsound rules.** §6.4's `ftc` never required a ≤ b, so with reversed
  limits its four premises held vacuously and it proved ∫₁⁻¹ 1/x² ≐ 2. Every
  step over a range was made to owe `lo ≤ hi` (§6.1, §6.4). *(The
  consolidation replaced that rule: every step now builds the range from
  whichever order discharge proves, and refuses when neither is proved, §6.4.)*
  And **partial functions
  owed nothing**: `0*ln(-1) ≐ ?A` and `tan(pi/2) − tan(pi/2) ≐ ?A` closed as
  a plain `Proved.`, because `ring` cancelled atoms that denote nothing. Each
  partial builtin is now a former that owes its natural domain, and `ring`,
  `field` and `norm_num` refuse integrals and derivatives, whose definedness
  cannot be stated yet (§5.1, §6.2). §14's claim that the total and partial
  readings agree had silently depended on both.
- **`D[x]` is not a plain binder** (§5.1). It binds inside its body and is
  evaluated at x, so x stays free.
- **Ten underspecified points, each now decided**: when `/` is charged, which
  atom a/d is, `# 0` under `D[x]`, two §5.3 method preconditions, how `^` is
  parsed, what `deriv`'s trust status is while `ftc` accepts its output, the
  refusal shape §16.3 lacked, where untrusted code called from trusted code
  sits (§15.2), and which of §15.3's two mechanisms is in force (both).
- **§11's obligation lists were still incomplete.** They now show what the
  kernel emits.

§18 Q21 is settled. The line-count estimates are gone from §15.2 and §17: the
trusted base is kept small because it has to be audited, and that is argued
from what each part does. The record is `PROOF_OF_LIFE.md`, and the frozen
specification the kernel was built against is `kernel/GRAMMAR.md` (D1–D18)
and `kernel/p1_expected.py` (E1–E26).

Scope agreed at the outset, and revised since: it targets **scalar real
analysis** as §13 now bounds it; it is a design document, not a prototype; and
it has graduated out of `_scratch/` to `tools/`, which §18 Q6 settles and which
the original scope note deferred until it "checks something".

---

## 1. Who this is for, and what the gap actually is

The learner has computer science, logic and formal methods. They are fluent in
the loop that a proof assistant runs on — state a goal, apply a tactic, read
the new goal, back out and try another — and fluent in reading a rule with its
hypotheses attached, which is the part of this subject most calculus learners
find alien. What they do not have is **calculus**: not the algebra, and more to
the point not the trained eye that looks at ∫ dθ/(a + e cos θ) and thinks
*Weierstrass*.

The course's own readiness sheet is precise about the gap and about its cure:

> Calculus fluency went badly — you knew the method but got stuck in the
> algebra, or lost signs and factors, or took much longer than the guide.
> **This is the gap that matters.** The cure is volume, not reading: 15–25
> integrals, expansions or series a day for three to six weeks.

**The sheet is describing a different learner, and the difference decides the
design.** It assumes you knew the method and lost the algebra. Here the method
is the harder half: the move is not obvious, and the algebra is *also* long
enough to lose. So the cure — volume — is right, and volume alone is the wrong
prescription, because without the trained eye each attempt is expensive and
uninformative. You stare, you guess a substitution, you grind four lines, you
reach something worse, and the answer in the back of the book tells you only
that you were wrong. That is a slow and demoralising way to acquire an
intuition, and it is what "three to six weeks" is really costing.

**So the design's object is to make each attempt cost seconds and say why it
failed.** Try the substitution; the goal is rewritten for you; if it made
things worse you retract it and the cost was one keystroke; if the shape you
now have matches a standard form, the tool says so. What you are doing is still
the exercise — you chose the move, and choosing is the skill — but the loop
runs at the speed of a proof assistant instead of the speed of paper.

> **This is a fluency trainer, not a fluency substitute.** It does not remove
> the volume the sheet prescribes. It makes the volume affordable, and it makes
> each repetition instructive instead of merely wrong.

That is also why `solve` is **not in the first implementation** (§2). Every
other form of assistance here leaves the choosing to you; pressing `solve` is
the one action that produces no fluency at all. It is designed for, prepared
for, and deliberately unbuilt until the rest has been used.

### The bet on this particular learner

**Calculus, presented as a tactic language.** Goals, moves, side conditions,
backtracking, a rule table you can search — the learner already owns every one
of those concepts and has to learn none of them. What they get handed is the
vocabulary they lack: which move the shape of an integrand is asking for, and
what each move demands in return. §8.5 is where that vocabulary lives, and
under this framing it is not a convenience feature, it is the product.

The corollary is that the domain obligations (§5.3) are an **asset** rather
than a tax. For most learners "√(u²) = u needs u ≥ 0" is pedantry to be
tolerated; for this one it is the familiar shape of a hypothesis discharge, and
it is the part of calculus that will feel like coming home.

### What the course asked for

The readiness sheet also has a line about tools, worth quoting because it
frames the thing this system is better at than a CAS:

> A computer algebra system **may check a final answer; it may not produce
> one.**

The interesting half is the first. Checking an answer is something a CAS does
*badly* — it gives you a second number to trust rather than a reason — and it
is exactly what a proof checker does well. This tool will eventually produce an
answer too (§8.2); the difference from a CAS is that whatever it produces
arrives with a checked derivation attached, and that in the meantime it is
better employed telling you whether the move you just tried was a good one.

**What it gives you:** a cheap search, a named reason when a move fails, the
technique that the shape of the problem is asking for, long chains carried
without a dropped sign, and a refusal when the step is not actually valid.
**What it does not give you:** the answer, in v1, unless you find it. §8.8
notes that it can also generate practice, which under this framing is rather
more interesting than it first appeared.

### What it will be tested against, and how far that reaches

**Problems from `mechanics-to-relativity`, and nothing else.** The readiness
sheet's P1–P5 and unit 00 are the acceptance corpus, they are what §17's stage 0
samples from and what the recognizer corpus is built against, and they are the
reason §13 spends its length on what the course actually contains rather than on
calculus in general. (**Not** the falsifier bank, which §17 generates
mechanically from the rule table so that its coverage tracks the table rather
than the corpus.) A tool that works on a textbook's exercises and not on
this course's has not met the requirement.

**And that is the whole of the course's authority here.** The distinction is
worth stating because it is easy to lose:

> The corpus determines **what must work**. It must not determine **how the
> tool works**.

A course problem needing `artanh` is a requirement, and §5.1 adds `artanh`
(§13 is a whole section of this kind, and so is the recognizer's row list).
A course problem being *presented* a certain way is not a requirement, and no
mechanism in this document may be derived from one. The two look similar on the
page and they are not the same thing at all: the first is a corpus defining a
target, the second is a tool taking its shape from something that has no reason
to constrain it.

**The test, when it is unclear which one you are looking at:** *if the course
were replaced tomorrow by a different calculus course, what would have to
change?* The answer should be the problem `.json` files, §13's coverage claims,
and the priority order of §8.5's recognizer rows — nothing else. Anything else
that would have to change is coupling, and it is a defect to be removed rather
than a design decision to be defended.

Two things this rules out that revision 3 had to remove: a hint ladder whose
shape was taken from the course's hint rungs (§2 — the layers it exposes come
from §8.5's structure, and the course's rungs are corroboration at most), and a
dependency rule justified by what the course's own page happens to load (§16 —
the rule is *no build step*, and matching the course is a consequence). Both
were defensible-sounding and both were backwards.

---

## 2. How much of the work you do is your choice

Two things about this system are fixed. How much of the work it does for you is
not one of them.

> **Fixed: it never lies.** Every result the tool reports as proved carries a
> derivation the kernel checked. This is not negotiable and is the whole point.
> §15 states exactly what that guarantee rests on, and §15.4 states what it
> does *not* rest on in the first implementation.
>
> **Fixed: some things are impossible.** Equality of these expressions is
> undecidable (§3); some integrals have no elementary antiderivative at all;
> and the kernel proves only positive statements, so "this diverges" and "your
> answer is wrong" are outside it (§13). Those limits are real and §13 lists
> them.
>
> **Yours: everything else.** How much you do by hand, how much you delegate,
> and how far up the hint ladder you go before you go back to thinking.

An earlier draft of this document drew a "line between what must and must not
be automated", on the theory that a tool which integrates for you defeats the
course. That was wrong twice, and the second way is the interesting one.

It was wrong because it is not the tool's call. And it was wrong because **no
part of it was ever required by soundness.** Every restriction in that draft
was pedagogical, and removing all of them changes nothing in §15 — because of
the asymmetry in §6.4: an antiderivative is expensive to *find* and cheap to
*check*. So an integrator can be shipped, run, and have its answer **proved**,
without a single line of it entering the trusted base. The architecture is
permissive, and it stays permissive.

### The five ways of working, and which exist in v1

| Mode | You supply | The tool supplies | v1 |
|---|---|---|---|
| **by hand** | every move and its data | the algebra, the derivatives, the domain conditions | **yes** |
| **assisted** | which move to make | carries it out; proposes moves; says what the new shape matches | **yes — the default** |
| **check** | a finished answer | a proof it is right, or a rejection naming the discrepancy | **yes**, for exact answers |
| **auto** | `auto.` | a bounded search over the rule table | prepared, not built |
| **solve** | `solve.` | the entire derivation, checked, for you to read | prepared, not built |

All five end in a kernel-checked proof. The only difference is who did the
finding — and a proof found by `solve` is exactly as sound as one you wrote,
because the kernel cannot tell them apart and does not try.

**`auto` and `solve` are deliberately absent from the first implementation**
(§1), and the reason is pedagogical rather than architectural, which is why it
is stated here rather than in §15. They are also the most expensive things in
§17's plan, so deferring them is what makes v1 affordable — but that is the
second reason, not the first.

**What "prepared" means, concretely.** Five decisions in v1 exist so that `auto`
and `solve` are an addition rather than a rewrite:

1. **The rule table is data behind one interface** (§14), so it is already an
   enumerable search space rather than code.
2. **§7's tactic boundary is real from day one**: every move is an untrusted
   proposer emitting candidate kernel steps. A search is one more proposer.
3. **The integrator sits behind one entry point** (§8.2), so the v1 fallback
   and a later bespoke integrator and `solve` all call the same interface.
4. **The attempt tree** (§16) is the shape a search produces. A state model
   that can branch for a human can display a machine's derivation.
5. **Move records are uniform** whether a human or a machine produced them
   (the work log, below), which is what makes §17's gate answerable at all.

### The hint ladder

Between *stuck* and *solved* there is a staircase, and **it comes out of the
tool's own structure rather than from anywhere else.** §8.5 holds four layers
of strictly increasing specificity: what is legal here, what *kind* of move the
shape wants, which named technique, and that technique with its parameters
filled in against this goal. Those layers exist because the recognizer has to
be built that way to work at all. Revealing them one at a time is then not a
feature that had to be designed — it is the layers, exposed on request:

| Rung | | What you get | Which layer |
|---|---|---|---|
| 0 | *always on* | the palette: which rules match this goal's shape | legality |
| 1 | `?` | the **kind** of move — "this integrand wants a substitution" | category |
| 2 | `??` | the **technique**, named — "Weierstrass, t = tan(θ/2)" | row |
| 3 | `???` | the **parameters** — "x := t², over t in [0, π/2]" | instantiation |
| 4 | `!` | it performs the move | application |

So the rung count is not a choice and neither is their order; both are
determined by how many layers §8.5 has. If the recognizer were ever
restructured into three layers or five, the ladder would follow it without
argument.

Rung 4 is not `solve`: it does one step, and you are looking at a new goal with
the choosing still ahead of you. That distinction is the whole reason the
ladder exists and `solve` does not.

*(The course's own worked solutions happen to be organised into hint rungs too
— §11 and §12 quote Rung 2 and Rung 5. That is worth one sentence as weak
corroboration that graduated disclosure suits this material, and it is not a
reason for anything. An earlier draft of this section derived the ladder from
the course's rungs, which is the coupling §1 forbids: had that been the only
justification, the ladder would not be here.)*

### The work log, and what it is not

Every proof records how it was obtained: which mode, how many steps you wrote,
how far up the ladder you went, what was retracted, what was admitted, and the
provenance of each rule (§14). That record exists **for you**, because six
months on it is genuinely useful to know whether you worked unit 08 or climbed
to rung 4 through all of it.

It is not an assessment. Nobody else sees it, it never blocks anything, and it
produces no warnings.

It has a second purpose, which revision 1 left unstated while depending on it:
**this record is the sole evidence for the largest scope decision in the plan**
(§17's gate). That is an argument for *recording* it, which costs nothing;
whether it is *displayed*, which costs UI space, is a separate question and is
§18 Q3.

*(Naming: revision 1 used "ledger" for four different objects. They are now the
**work log** here, the **obligation pane** in §5.4 and §16, the **provenance
report** that §14 prints per proof, and the **rule ledger** that is §14's
deferred deliverable — the machine-checked table and the tags it earns.)*

### Defaults

`assisted` is the default, and under §1's framing that is no longer a close
call: it is the mode in which the loop runs. `check` is one keystroke away for
when you arrive with an answer already. The mode is sticky, and the tool never
comments on your choice.

---

## 3. Why not a CAS: the architectural argument

The obvious cheap design is "normalise both sides and compare". It is unsound,
and not by accident.

**Richardson's theorem (1968).** For expressions built from the rationals,
π and ln 2, a variable *x*, the field operations, composition, `sin`, `exp`
and `abs`, the predicate "this expression is identically zero" is **undecidable**.
Adding `abs` is what pushes it over; the exact boundary moves with the function
set (the Richardson–Matiyasevich results, and Risch's decidability result for
the integration problem over restricted classes), but the message is stable: no
algorithm decides equality of the expressions this course actually writes.

A CAS therefore answers with a *heuristic*. Heuristics fail in both directions,
and one direction is fatal:

- failing to prove a true equality is **incompleteness** — annoying, honest;
- reporting an equality that is false is **unsoundness** — it marks a wrong
  answer right, which is worse than no checker at all.

Real CAS systems are unsound in exactly the places this course lives:
`sqrt(t^2) → t` (true only for *t* ≥ 0), `x/x → 1` (false at 0),
`(x^a)^b → x^(ab)` (false for negative bases), branch cuts of `log` and
`arctan` silently crossed, and a definite integral evaluated by an
antiderivative with a pole inside the range. Every one of those is a **dropped
sign or a lost domain condition** — the same failure mode the readiness sheet
names as the learner's gap. A tool that fails the way you fail is worthless as
a check on you.

**This is measured, not asserted.** Revision 1 argued it; the review ran it.
Sixteen of this course's own integrands through the two shippable JavaScript
computer-algebra systems:

- **Algebrite 1.4.0** (850 KB): 12/16. Fails on 1/(1+x⁴) — readiness P5 — on
  1/(x²−x+1), a bare arctan, and on e^{−x} sin x, the parts-with-cycle case
  §8.2 names. On 1/(a + e·cos θ) — readiness P3 — it silently reinterprets the
  eccentricity `e` as Euler's number and returns an expression containing
  exp(2).
- **nerdamer-prime 1.4.0** (483 KB): 13/16 "successes", of which **three are
  wrong answers** — `1/(a + b·cos θ) → log(a + b·cos θ)/b`, which needs
  tan(θ/2); `1/(x² − x + 1)` returned with a prefactor that is identically
  zero; and √(1−x²) with a wrong coefficient.

A heuristic normaliser confidently returns falsehoods on undergraduate
integrals and does not know it. Under §15 that costs a rejected step rather
than a wrong grade, which is precisely the vindication this design was built
for — and precisely why a shipped JS CAS is not worth 850 KB (§15.5).

So: no global normal form, no simplifier. Instead, a **fixed table of named
inference rules, each of which is a theorem of real analysis with its
hypotheses made explicit**, and a kernel that will only compose them. Equalities
that the rules cannot reach are simply not provable — the system is
*incomplete*, by construction and on purpose. The one place a normal form is
permitted is where a genuine decision procedure exists, and those are named in
§6.2.

**This is an argument about the kernel, not about what the tool will do for
you.** It does not conclude "therefore no integrator". It concludes that an
integrator must not be *believed* — which is why §8.2 ships one and has the
kernel check its output. The result is a system that does what a CAS does and
additionally tells you, soundly, when it has got it wrong; and every unsound
rewrite listed above (√(*t*²) → *t*, *x*/*x* → 1, the pole inside the range) is
caught by that check rather than argued away.

---

## 4. Why not something that already exists

Three candidates, in increasing order of how close they get. Revision 1 asked
only the first and the third; the second is the one a reader asks about first,
and leaving it out was the largest omission in the document.

### 4.1 Why not Rocq itself

The learner has Rocq, `rocq-mode.el` in this workspace, and the background to
use it. The honest question is why not write the problems in Rocq with
Coquelicot and be done.

1. **Real analysis in Rocq is brutally laborious.** Proving
   ∫₀^{π²/4} sin √x dx = 2 in Coquelicot is not a fifteen-minute job; routine
   undergraduate integrals take hours, mostly spent on integrability side
   conditions and `Rbar` coercions. The learner would be doing formalisation
   engineering, not mechanics. Over 41 units that is not a course, it is a
   career change.
2. **The vocabulary is wrong, and — this is the correction — the *interaction
   model* is exactly right.** Revision 1 said the abstraction level was wrong,
   on the grounds that the learner's difficulty is sign-and-factor bookkeeping
   while Rocq's is dependent types and library search. §1 now states the gap
   differently: the difficulty is **which move to make**, and goal-tactic-
   backtrack is precisely the loop in which that gets learned. So the argument
   is not against the model. It is that Rocq's tactics for real analysis are
   about `Rbar` coercions, `ex_derive` side goals and finding the right
   `Coquelicot` lemma name, when what is wanted is *substitute*, *by parts*,
   *recognise the form*. The right conclusion is not "don't build a proof
   assistant"; it is **"build one whose tactic vocabulary is the calculus
   techniques chapter"** — which is §8.5, and which is the product.

Both reasons are about **per-proof cost** and per-proof vocabulary. Note what
they do *not* argue against: a fixed lemma file proved once, where the cost is
amortised over every problem. That is why §14 survives them — and why §14 is a
later option rather than a prerequisite.

### 4.2 Why not the systems that already sit between a CAS and a prover

This design is not novel in its architecture. Untrusted search proposing,
trusted kernel checking, with side conditions as explicit obligations, has been
built at least twice, and one of those is close enough that it should be read
before a line of code is written.

**The nearest neighbour: Iscalc / HolPy.** Xu, Li & Zhan, *Verified Interactive
Computation of Definite Integrals* (CADE-28, 2021), generalised as **Iscalc**
(CADE-29, 2023). The overlap is structural, not thematic:

- Step-by-step definite-integral computation "in a familiar user interface,
  while also verifying the computation by translating it to proofs in
  higher-order logic". Substitution and integration by parts are user-chosen
  moves. Slagle's method is available as the `solve` equivalent.
- Side conditions are first-class: continuity, differentiability, nonvanishing
  denominators, discharged by proof automation. Their rational-function rule
  "checks that denom is nonzero in the domain of integration".
- Their motivating example is Maple evaluating ∫₋₁¹ √(x²) dx as **zero**, and
  they name the systematic cause as "neglect of checking side conditions,
  involving concepts such as well-definedness of expressions, singularities,
  convergence". That is §5.3 of this document, and √(x²) is `sqrt_sq`, the
  running example of §11.1.
- A JavaScript web front end over a Python backend, on HolPy.

Their evaluation is the most useful empirical fact available to this project.
**183 undergraduate integrals** — Tongji exam-prep (36), D. Kouba's problem
lists (122, split by technique), MIT Integration Bee 2013 (25):

| | Solved |
|---|---|
| With human-provided steps | 161/183 (**88%**) |
| Automatic (Slagle's method) | 109/183 (**60%**) |

And the sentence that matters most here: *"Most of the failures are due to
unable to show equality after simplification, and during inequality checking."*
That is an independent, measured confirmation of the two hardest predictions in
this document — the residual needing an identity `field` cannot see (§6.4), and
an obligation none of §5.3's discharge methods can produce (§5.3, §6.9). Someone
built the thing and found exactly those two walls, at roughly 12% of
undergraduate integrals. Plan for them; do not be surprised by them.

**This is the thing to try before building anything** — §17 stage 0b makes it a
day of work, placed before the API of §16.3 is designed, because §16's shape
(a typed-language kernel behind a local API with a browser client, one request
per move) is architecturally theirs and
the protocol is the decision most easily got wrong and least easily changed.

**Why it does not settle the question.** Three differences, and the first is
the one that matters:

- **Its trust story is weaker than the one proposed here.** They ported the
  statements of over a thousand HOL Light theorems, proved about 40% of them,
  and say plainly that "the statements of the theorems need to be trusted". The
  construction of the reals, the gauge integral and *the fundamental theorem of
  calculus itself* are not formalised. This document's §15 — a small kernel
  whose every rule is stated with its hypotheses, whose discharge procedures
  emit re-checkable certificates, and whose rule table is designed to be
  machine-checked later — is a stronger claim even in v1, and much stronger
  once §14 lands.
- **No dimensions, no ODEs, no certified numerics.** `buckingham`,
  `ode_verify`/`sep_autonomous` and `approx` to five significant figures via
  verified enclosures have no counterpart there.
- **Not offline, not one file, not this course.** A Python backend, a
  general-purpose tool, no problem files, no `check`-my-paper-work mode.

**What driving it found, and the verdict on reuse (stage 0b, first pass,
2026-09-21).** The repository was cloned at its last commit (`f36c1f0`,
2023-02-25; dormant since) and driven both through its Python API and its web
UI; the setup, the scripts and the full notes are in `_scratch/holpy-trial/`
in this workspace — **outside this tool, and a pointer a published copy could
not follow**, so everything this document relies on from that trial is stated
here rather than cited there.
It is one afternoon, not the planned day, and the day it did not spend was on
questions that turned out not to need it. **Both are now closed.** The
interaction was judged clunky and is **not taken as inspiration for §16.4's
client** — but that is a verdict on HolPy and not on the request-per-move
boundary §16 is built on. Each of the three defects below would feel clunky
over a perfect transport: the protocol resends the whole file every move, a
refusal surfaces as an unrendered HTTP 500, and there are no obligation objects
to display. This trial is therefore evidence neither for nor against that
boundary, which stands on §16.3's own argument and on a latency budget that is
a localhost round trip plus whatever `ring`/`field` costs — the second term
being what §17's stage 0c measures. And the corpus mapping onto P1–P5 was never
a blocker: it is filed below as a pointer with a trigger, not a question.

The code is weaker than the paper on exactly the axis that matters here. Three
side-condition traps were put straight through its kernel:

| Probe | HolPy returns | Truth |
|---|---|---|
| ∫₋₁¹ x² dx, substituting u = x² | `0` | 2/3 |
| ∫₋₁¹ 1/x² dx | `-2` | diverges |
| ∫₋₁¹ √(x²) dx | rewrites to `abs(x)` and stops | 1 — safe |

Two of three are false results accepted without complaint: `Substitution`
checks neither injectivity nor monotonicity on the interval, and
`DefiniteIntegralIdentity` applies FTC across a pole with no continuity check.
The second is the textbook error their own paper holds against Maple. Beyond
the probes: `Equation` accepts a rewrite when *any one* of several normalisers
agrees, which is §3's heuristic-normaliser problem; `inequality.py` calls
`sympy.factor` on the path that decides side conditions, which is the
arrangement §15.5 forbids; a refusal is a raised `AssertionError` that the UI
never shows (the request fails with HTTP 500 and the page does not change);
there are no obligation objects and no attempt tree; and the protocol resends
the whole file on every move.

**So the core is not salvaged; it is reimplemented.** The UI needing a rework
was not what decided it — §15.5 already builds the client either way. What
decided it is that the soundness property §15 exists to provide is absent in
the kernel's own rules, and retrofitting side conditions, obligations and an
attempt tree would replace most of it while inheriting someone else's
architecture and a 2023 dependency set that needed four patches to start.

**Worth taking into consideration** — as inputs to weigh when the relevant
section is designed, not as commitments, and none of them as code under §15's
line:

- **Its corpus.** `integral/examples/*.json` holds the 183 problems with
  human-provided step sequences. A candidate source for the acceptance half of
  §17's bank and for the recognizer corpus, subject to how much of it lands
  inside §13's scope. **How much does is unexamined, deliberately** — the
  trigger for finding out is wanting a benchmark, not building one, and until
  then this is a pointer rather than a task.
- **Its move inventory**, as a field-tested list of what a palette ends up
  needing: forward *and* backward substitution, rewriting to a user-typed form
  checked for equality, addressing a subterm by location, splitting a region.
  Corroboration for §8.5, not a specification of it — the palette's shape
  derives from §1, not from what HolPy happened to build.
- **Its step JSON**, which carries the rule, a plain string and LaTeX for both
  rule and result. One data point for §16.3's protocol, alongside the
  counter-example of its whole-file-per-move shape.
- **Its use as a build-time differential oracle**, in the role §15.5 gives
  SymPy: run a shared corpus through both and investigate every disagreement.
  The probes above suggest the disagreements would mostly be HolPy accepting
  what this kernel must refuse — which is itself a test that the refusals
  fire.

**Certified CAS inside a prover.** Kaliszyk & Wiedijk, *Certified Computer
Algebra on Top of an Interactive Theorem Prover* (2007) — the HOLCAS system —
put simplification, numeric approximation and **antiderivation** inside HOL
Light, with the prover proving each simplification. The architecture is the one
here; the artefact is a research prototype rather than a learner's tool, and it
has no domain-obligation pedagogy.

**Educational proof assistants.** **Waterproof** (TU Eindhoven, in the Analysis
1 course since 2019; piloted at Utrecht in 2025; since summer 2025 running on
vscode.dev with no server) is a controlled-natural-language layer over Rocq or
Lean. It is the closest existing artefact to the *interaction* §16 describes,
and its published evaluations are the only real evidence anyone has about
whether students use a thing like this — **which is worth reading, and is not
a prerequisite for anything** (revision 6; the closing section says why). It is
not a substitute: no `ftc`-by-differentiation kernel, no
certified `approx`, no dimensions, and it inherits exactly the per-proof cost
§4.1 rejects. **Lurch** (a word processor that checks the reasoning in a
document), **Diproche** (a natural-language checker for beginners' set-theory
and number-theory exercises), **ProofBuddy** and **CalcCheck** are all
proof-course tools rather than calculus tools.

**Assessment systems.** **STACK** (Maxima under Moodle) is the widely deployed
university answer-checker. It is answer-level rather than step-level, and
Maxima underneath means no soundness guarantee — its own documentation warns
that equality checking is unreliable once substitutions are made. **WeBWorK**
and **Möbius** are the same shape. **Rubi** is the state of the art in
rule-based integration (~7,000 rules) and has no verification layer at all;
**Wolfram|Alpha**, **Symbolab** and SymPy's `manualintegrate` show steps
heuristically — the 2021 paper above records SymPy 1.5 returning a *wrong*
answer on ∫₀^π √(1 + cos 2x) dx, which is §3's argument once more.

### 4.3 Why not a proof assistant in the browser

jsCoq exists and is a real option. Two facts decide it. It ships tens of
megabytes of WASM and boots slowly, against a requirement that is *a page that
opens*; and — the fact revision 1 got wrong — **Coquelicot is not in jsCoq's
addon list** (coq, mathcomp, elpi, equations, extlib, simpleio, quickchick,
software-foundations, hahn, paco), so the browser route means compiling it
yourself. Lean changes nothing here: lean4web runs server-side over a WebSocket
LSP proxy.

This was an argument about the *app*, and §16 has since moved the kernel out of
the browser entirely — only the UI tier runs there now — which makes it moot
for the deployment and leaves it standing for what it always really covered:
**a prover is not a thing you ship to a page.** It remains unrelated to §14,
which never ran a prover in a browser and would run one at authoring time, on
the developer's machine.

### 4.4 What is left that is unclaimed

Not the architecture. Honestly stated, what this project would add to the
systems above is **packaging and reach**: one course, one HTML file, offline,
no server; a kernel small enough to read in an afternoon rather than a prover
plus a partially-proved library; dimensions, ODEs and five-significant-figure
enclosures in the same tool as the symbolic side; and a `check` mode aimed at
work already done on paper.

That is a narrower claim of originality than "a sound proof checker for
calculus", and it is the one that survives contact with the literature. It is
also still worth building, for the reason §1 gives: the thing needed here is
not a general verified CAS, it is a page that opens beside a specific course
and checks that course's problems.

---

## 5. The system

### 5.1 Terms

One-sorted and first-order, over the reals. Binders occur only in the four
constructs that need them, which keeps capture-avoidance a solved problem
rather than a research one.

```
  e  ::=  q                     rational literal (exact, arbitrary precision)
       |  pi | e_const          the two named transcendental constants
       |  x                     variable
       |  e + e | e * e | -e | e^n          ring operations, n ≥ 0 integer literal
       |  e / e | e^n           field ops, n < 0; carry a nonvanishing obligation
       |  e ^ e                 real power, carries base > 0
       |  sin e | cos e | tan e | asin e | acos e | atan e
       |  exp e | ln e | sqrt e | abs e
       |  sinh e | cosh e | tanh e | asinh e | acosh e | atanh e
       |  f(e, ..., e)          declared function symbol
       |  D[x] e                derivative of e with respect to x
       |  Int[x = b .. b] e     definite integral
       |  Sum[n = b .. b] e     sum
       |  lim[x -> b^s] e       limit, s in {+, -, } (one-sided or two)

  b  ::=  e | oo | -oo          endpoint terms
```

**Four decisions revision 1 left open or got wrong, all of them cheap and all
of them load-bearing on stage 1's own targets.**

**Infinity is an endpoint, and only an endpoint.** Revision 1 had no production
for `oo` at all — it occurred once in 1,214 lines, in a comment. The
consequence was that readiness P5, ∫₀^∞ dx/(1+x⁴), which §17 names as a
stage-1 target, could not be *written down*; nor could `Sum[n = 1 .. oo]`,
which the same comment described; and §6.7's convergence tests all have
hypotheses about limits as n → ∞. `oo` and `-oo` are therefore terms of a
separate syntactic class `b`, admissible as `Int`/`Sum` limits and as a `lim`
target and **inadmissible as a subterm of an arithmetic expression**. That
restriction is what keeps `ring` and `field` working over a total ℝ with no
junk values, and it is why the fix costs a line rather than a sort.

**Reversed limits have a meaning, stated.** `Int[x = a .. b] e` when b < a
denotes −`Int[x = b .. a] e`; `Sum` over an empty range is 0. Revision 1 never
said, and the omission was a genuine unsoundness rather than a gap: §5.3's
by-range method extended the domain with `a ≤ t ≤ b` unconditionally, so a
reversed limit made the constraint set inconsistent, and Fourier–Motzkin proves
*every* linear goal from an inconsistent system. The worked exploit is
`Int[x = 1 .. -1] sqrt(x^2) ≐ Int[x = 1 .. -1] x`, where by-range supplies
1 ≤ x ≤ −1, derives 0 ≤ x, discharges `sqrt_sq`, and the kernel proves −1 ≐ 0.
Reversed limits are normal output of `int_subst` with a decreasing φ — `x = a
cos θ` is the canonical case — so this was reachable, not hypothetical.
*(Revision 10, int_subst: the claim holds, through a flip. Once every range
owed `lo ≤ hi` (§6.4, since replaced), a reversed range with symbolic ends
owed an order that is false, so x = cos θ over [π/2, 0] was at first refused
at the substitution itself. `int_subst` now builds the oriented form,
∫₀^{π/2} −(…) dθ, when discharge proves the ends' order the other way. That
is this paragraph's definition applied once. Literal ends, as in x := 1 − t over [1, 0], are kept
reversed, since every later step orders them the same way and owes nothing.
∫₀¹ √(1−x²) by x = cos θ is accepted as a move. It does not finish yet. The
goal still owes `1 − x^2 ≥ 0` and the new integrand owes `1 − (cos θ)^2 ≥ 0`,
both tagged `none`, and closing needs `pyth` and a sign fact for cos on
[0, π/2]. Neither gap is the substitution's.)*

*(Revision 10, consolidation, E56: reversed limits are now ordinary input to
every move, not only `int_subst`'s output. Owing `lo ≤ hi` was stronger than
this paragraph needs. It refused a correctly reversed symbolic range such as
∫_{π/2}^0 wherever a key used it, because `pi/2 ≤ 0` is false. Every step
that builds an interval from an integral's limits now orders two literal
ends by `norm_num` and otherwise builds the interval from whichever order
discharge proves, [lo, hi] or [hi, lo], and it is refused
`orientation-undecided` when neither is proved (§6.4). **This closes the
exploit above without assuming an order.** The exploit was a constraint set
that assumed a ≤ b when b < a, so the range was empty and every obligation on
it vacuous. A proved order cannot be wrong, because its certificate is
checked, so the interval built is exactly the set of points between the
limits and is never empty. An integral's value, by this paragraph's
definition, and its definedness depend only on the integrand on that set, so
every obligation stated on it is the right one for either order. Both gaps
above are closed too: ∫₀¹ √(1−x²) by x = cos θ now finishes, `Proved modulo 5
admissions` (§13).)*

**Inverse hyperbolics are in.** Separable ODEs with quadratic drag integrate
to `artanh`, and §8.5's recognizer row √(x²+a²) → x = a sinh u needs `asinh` to
state its inverse — so a grammar with `sinh`, `cosh` and `tanh` and no inverses
cannot express the closed forms its own rules produce, which is an internal
inconsistency rather than a coverage gap. *(§13: the corpus reaches this at
unit 00 P4, where a learner typing the sheet's own answer would get a parse
error.)*

**`abs` is admitted in goals** — revision 6, reversing revisions 1–5, which
confined it to side conditions and domains. The old restriction cost unit 00 P7
(the period of V = k|x|^n), left §8.5's `f′/f → ln|f|` row uncheckable by any
rule, and made `∫₋₁¹ |x| dx` **unstatable** — a failure the learner meets at the
keyboard rather than at a refusal, which is harsher than anything else §13
lists.

**What admitting it costs, stated exactly, because the old text implied it cost
decidability.** It does not. §3's undecidability argument is about equality in a
language containing `abs`, and §6.4 **already disclaims decidability** for the
`D[x] F ≐ f` check — the claim is soundness, plus completeness whenever the
residual lies in ℚ(atoms). `abs u` is an opaque atom to `ring` and `field`,
exactly like `sin u`, and every fact about it enters through a rule. Nothing in
§15 moves. What does get harder is `auto`'s search, and `auto` is stage 3.

**What it needs, and all of it is small:** `d_abs` in §6.3, the two rewrites
`abs_nonneg` and `abs_neg` in §6.8, and a regularity entry in §6.9 saying `abs`
preserves C⁰ and gives C¹ only where its argument is nonzero. Note that
`d_abs` needs no `sign` former — `D[x](abs u) ≐ (u / abs u) * D[x]u @ u # 0`
is written in the grammar as it stands.

**`∫₋₁¹ |x| dx` becomes statable, and still does not close in one step** —
which is the right outcome rather than a shortfall. F = |x|·x/2 is C⁰ on [−1,1]
but not C¹ on (−1,1), so §6.4's `ftc` refuses; the proof is `int_split` at 0,
then `abs_neg` on the left piece and `abs_nonneg` on the right, then `ftc`
twice. **Splitting at the kink is the exercise**, and the kernel now makes the
learner do it instead of making the problem unwritable.

**Negative integer exponents are field operations.** Revision 1 put `e^n` with
n an integer literal on the ring side, which makes the fragment Laurent
polynomials and lets `ring` prove x · x^(−1) ≐ 1 @ ⊤. Worse, it created a
*spelling asymmetry in the trusted base*: `deriv` on 1/x fires `d_inv` and
emits `x # 0`, while `deriv` on x^(−1) fired `d_pow_int` and emitted nothing.
Both spellings now emit the same obligation, and §17's bank tests both.
*(Revision 10: how a parser tells `e^n` from `e ^ e` is syntactic. The exponent
is an integer power exactly when it is a literal n or −n, and anything else is
a real power owing base > 0. `x^2^3` is refused as ambiguous rather than read
either way — `kernel/GRAMMAR.md` D8.)*

**`u^0` is 1 for every base, 0 included** *(revision 10, second review,
E58)*. An integer power is repeated multiplication, and `u^0` is the empty
product. That is the convention `ring` already implements, since it
normalises `u^0` to the constant 1, and it is the one that keeps `ring_nf` a
sound identity under every assignment of the atoms. So `0^0 ≐ ?A` and
`(x − x)^0 ≐ ?A` both prove 1: the convention is about the integer exponent,
not about the base. The real power `e ^ e` is untouched and still owes
base > 0. A limit of the form 0⁰ is §6.7's business, since it asks about a
limit and not about a term's value. `deriv` still refuses `d_pow_int` at
n = 0 (§6.3), which is incompleteness, not unsoundness.

A *function* is not a first-class object: "the function x ↦ e" is the pair
(variable, expression), and `D[x]`, `Int[x=..]`, `Sum[n=..]`, `lim[x->..]` bind
that variable. This is a real restriction — §13 says where it bites — and it is
what keeps the kernel small enough to review.

**The goal metavariable.** `?A` is admitted as a goal-level metavariable: a
goal state may carry one, a kernel theorem never does, and `?A` may not mention
a bound variable of the goal. §9 defines what it means and what `close` does
with it.

**`D[x]` binds inside its body and is evaluated outside it (revision 10).** The
grammar lists it beside the three binders, and within `e` the x of `D[x] e` is
bound. But `D[x] e` denotes the derivative *at* x, so x is also free in the
whole term: fv(`D[x] e`) = fv(e) ∪ {x}, and `D[x]` is not alpha-convertible.
§6.4's `D[x] F ≐ f @ (a,b)` needs exactly this, since its domain constrains x.
§9's scope check must not count that x as bound, or it would refuse
`?A := 2*x` for `D[x] x^2 ≐ ?A`. Substitution into `D[x] e`, which §15.2 item 1
puts in the trusted base, is defined accordingly in `kernel/GRAMMAR.md` §5
(D10).

**Every former is charged when its term enters the proof** (revision 10) —
at installation, in each new goal, in a `close` value, in a goal hypothesis
and in a fact's instance values — not when `field` happens to meet it. §5.1's
grammar says `/` and negative powers "carry a nonvanishing obligation", and
nothing said when.

**The partial builtins are formers too (revision 10).** Seven builtins are
defined on only part of ℝ, and each owes its natural domain exactly as
`e / d` owes `d # 0`:

| former | owes |
|---|---|
| `ln u` | `u > 0` |
| `sqrt u` | `u ≥ 0` |
| `tan u` | `cos u # 0` |
| `asin u`, `acos u` | `u ≥ -1` and `u ≤ 1` |
| `acosh u` | `u ≥ 1` |
| `atanh u` | `u > -1` and `u < 1` |

Each bound is one linear item, closed where the function is defined at the end
and open where it is not, and none is a divisor. `abs u ≤ 1` would be an
opaque atom no §5.3 method reads, and `1 - u^2 ≥ 0` would hide the linear
bounds that method 2 reads. A literal instance is decided by `norm_num` at
once, and a false one refuses the step: `0*ln(-1) ≐ ?A` is now refused because
`-1 > 0` is false, where before this revision `ring` cancelled the atom and
reported `Proved.`. A former is charged at its term's *position* domain, so
`ln(1 + x)` under `Int[x = 0 .. 1]` owes `1 + x > 0 @ [0, 1]`, which is a
different obligation from `d_ln`'s `1 + x > 0 @ (0, 1)`.

**`Int` and `D[x]` subterms have no statable definedness condition** until
§6.9's regularity and §5.2's `diverges` are built. So `ring`, `field` and
`norm_num` refuse any side that contains one, rather than treat it as an atom
that denotes (§6.2). No P1 step needs otherwise: `ftc` consumes the top-level
integral, and its derivative premise is decided on `deriv`'s output. *(Found
by the proof-of-life, `kernel/p1_expected.py` E6 and E26. One consequence to
know: `tan(pi/2) − tan(pi/2) ≐ ?A` now reads `Proved modulo 1 admissions`,
owing `cos(pi/2) # 0`, which is false and which no §5.3 method can decide. **An
admission tagged `none` may be false**, which is what the tag is for.)*

### 5.2 Judgements

The kernel proves these forms and no others:

```
  Γ ⊢ e₁ ≐ e₂    @ D        equality on domain D
  Γ ⊢ e₁ ≤ e₂    @ D        and <, with the same shape
  Γ ⊢ e # 0      @ D        nonvanishing
  Γ ⊢ e > 0      @ D        positivity
  Γ ⊢ e ∈ Cᵏ(D)             regularity, k ∈ {0, 1, ..., ω}
  Γ ⊢ dim(e) ≡ δ            dimension, δ a vector in ℚ^k
  Γ ⊢ conv(Int[...])        convergence of an improper integral
  Γ ⊢ conv(Sum[...])        convergence of a series (and absconv)
  Γ ⊢ exists(lim[...])      existence of a limit
  Γ ⊢ diverges(Int[...])    divergence of an improper integral
  Γ ⊢ diverges(Sum[...])    divergence of a series
```

Γ is a list of named hypotheses of these same forms, plus variable and function
declarations.

**A goal is a list of these, proved conjunct by conjunct.** Every goal in §11
and §12 carries a top-level ∧ and none of them was a judgement form in revision
1. `∀t.` in a hypothesis is a declaration-plus-body, not a new form.

**Tactic reports are not judgements.** `rank`, `ngroups`, `basis` and
`classify` are outputs of the untrusted layer, displayed and recorded; only the
scalar conclusion they justify enters the kernel. §12.2 is written that way.

**There is still no negation, and `diverges` is not one** — revision 6 adds the
judgement, and the distinction is the reason it is affordable. There is no `¬`,
no negation-introduction rule, and no excluded middle relating `conv` and
`diverges`; `# 0` remains a single hard-coded case. `diverges(I)` is a
**positive** statement about a limit — that the defining limit of the partial
integrals is infinite, or fails to exist — proved by its own rules exactly as
`conv(I)` is. It is a judgement and never a term, so it cannot occur inside
arithmetic and `ring` and `field` are untouched: the same discipline that keeps
`oo` to endpoints (§5.1).

**What it buys is larger than the four problems that asked for it.** Those are
unit 00 P8(b), unit 03 P1, unit 03 P2 and readiness P6 — *(revisions 1–5 said
"three" while listing four; the count was wrong, not the list)*. The bigger
gain is that **the classic FTC-across-a-pole error becomes refutable rather
than merely unprovable.** A learner who writes `∫₋₁¹ dx/x² ≐ -2` previously met
a refusal — `ftc`'s `f ∈ C⁰([a,b])` premise fails — which says *I cannot prove
this*, not *this is false*. With `diverges` the kernel proves the integral
diverges and the claim is **contradicted**. That is precisely the trap §4.2
found HolPy putting through its kernel and returning `-2` for, and the trap
their own paper holds against Maple; having no way to say so was a hole in this
document's own story about why it is different.

Two consequences in §13 soften accordingly: `check` on a wrong answer can now
reject in the divergence cases rather than always yielding `Stuck` (§18 Q20),
and §8.2's non-existence message stays a citation — *no elementary
antiderivative* is a different claim from *this integral diverges*, and only
the second is in reach.

### 5.3 Domains, and why they are the heart of it

Every judgement carries a domain **D**: a finite conjunction of atomic
constraints on the free variables (`0 ≤ t`, `t < pi/2`, `e # 0`, `a < x < b`).
This is not decoration — it is where soundness actually lives, because the
standard errors of calculus are all domain errors. `sqrt(u^2) ≐ u` is a *rule*
with the side condition `u ≥ 0`; using it without the condition is not a
"simplification", it is a rejected step.

A goal may first be `field`-normalised. Then, **in the order tried**:

1. **by hypothesis** — it is in Γ, or follows by the reflexive-transitive
   closure of the ordering hypotheses there. Matches disequalities as well as
   inequalities.
2. **by range** — inside `Int[t = a .. b] ...` the domain is extended with
   `min(a,b) ≤ t ≤ max(a,b)`, so a rewrite under the integral sign may use it.
   *(Revision 10: the step that uses a range was made to owe its orientation
   `a ≤ b` (§6.4), so the order method 2 needs is established rather than
   hoped for.)* *(Revision 10, consolidation, E56: it no longer owes `a ≤ b`
   outright. The step builds the range from whichever order discharge
   proves, [a, b] or [b, a], and is refused if neither is proved (§6.4). So
   a range item is never empty, its lower end is always the smaller, and
   method 2 never meets a range whose order is unknown.)*
3. **by linear arithmetic** — Fourier–Motzkin over ℚ on the linear constraints,
   complete for that fragment. **FM emits its Farkas witness** — the
   non-negative combination — and the kernel re-checks it with `norm_num`/`ring`.
   **`pi` and `e_const` enter as opaque free variables, not as values** — they
   are not rationals, so FM cannot use them as coefficients, and it is given no
   axiom about their magnitude. This is not a corner: readiness P1 integrates
   over [0, π/2], so method 2 puts `0 ≤ t ≤ pi/2` into the constraint set of
   the flagship example. Treating π as free is sound and keeps the fragment
   decidable, **but on its own it proves less than revisions 6–8 said**. Method
   2's constraint is `min(0, pi/2) ≤ t`, and with π unsigned that minimum is
   undetermined, so `t ≥ 0` does *not* follow. **Revision 9: each named
   constant brings its sign fact into the constraint set whenever it occurs:
   `pi_pos : pi > 0` and `e_gt_one : e_const > 1` (§6.8).** Then `t ≥ 0`
   follows and `t < 2` still does not. Both parts of readiness P1 need this:
   §11.1's `0 ≤ t` by range, and `sqrt(pi^2/4) ≐ pi/2`'s `pi/2 ≥ 0`. So does
   stage 0's S3, whose range [1, e] cannot be oriented until `e_const > 1` is
   known. More generally, method 2 can write its constraint as a linear
   `a ≤ t ≤ b` only once the order of a and b follows from the constraint set.
   Where it does not, method 2 adds nothing rather than a `min`/`max` that
   Fourier–Motzkin cannot read. *(Found by the proof-of-life review. Stage 0's
   gap 6 had called this sound as intended, which it is, and harmless for S3
   and P1, which it was not.)*

   *(Revision 10, int_subst, E49: each `sqrt` atom brings a sign fact the same
   way. It is `sqrt_nonneg : sqrt u ≥ 0` (§6.8), and the linear method reads it
   once for each `sqrt w` that occurs in the obligation or its domain, as it
   reads `pi_pos`. Its hypothesis `u ≥ 0` gets no child obligation. A
   certificate claims its obligation only where the obligation's terms are
   defined, and wherever `sqrt u` is defined, `u ≥ 0` holds; it is the former
   that was charged when the `sqrt` entered. This is what closes
   `1 + sqrt x # 0` on [0, 4], the divisor §8.5's kill-the-root row meets
   before any substitution.)*

   **The satisfiability pre-check below is safe with the constants free, but
   not for the reason revisions 6–8 gave.** They said a set satisfiable with
   π free is satisfiable with π at its value, and `pi < 3` shows that is false.
   What holds is the converse, and it is the direction the pre-check needs:
   - A set **unsatisfiable** with π free is unsatisfiable at π's value, so a
     refusal is never wrong.
   - A set that passes with π free but fails at π's value can only come from
     hypotheses that are false of the real π. By-range's intervals and the sign
     facts above are always true of it. Everything Fourier–Motzkin derives from
     such a set holds for every π satisfying it, so the judgement is vacuously
     true of the real π, not false.

   The exploit class the pre-check exists for, a constraint set the *kernel*
   made inconsistent (§5.1's reversed limits), is still closed. A goal that
   genuinely needs π's magnitude beyond its sign is out of this method's reach
   and belongs to a `cite` or, after stage 2, to §10's enclosures. *(Stage 0, `STAGE0.md` gap 6: sound as
   intended, and previously unstated.)*
4. **by sign certificate** — the goal is ring-normalised and a positivity
   witness is sought: a sum of even powers plus a positive rational; for a
   quadratic, positive leading coefficient and negative discriminant
   (`x² − x + 1 = (x − ½)² + ¾` is decided here). **The decomposition is
   emitted** and re-checked by `ring`. **The goal as written is tried as its
   own witness first**, before anything is normalised: `1 + u^2` is a positive
   rational plus an even power whatever u is, and normalising first loses
   that when u holds an opaque divisor. That is not hypothetical. It is
   `d_atan`'s own denominator in §11.2, `1 + ((2x − 1)/sqrt 3)^2 # 0`, which
   ring-normalises to a quadratic in x with coefficients in the atom
   `1/sqrt 3`, where the discriminant test no longer applies. *(Stage 0c,
   revision 7.)* **On a non-strict `≥ 0` goal**, a non-negative rational
   constant, zero included, also serves as the constant term: a non-negative
   combination of even powers is ≥ 0. Neither strict form reaches the
   fallback route's `0 ≤ pi^2/4`, which ring-normalises to `(1/4)*pi^2` with
   constant 0. *(Revision 10, E20.)* *(Discharge, E28–E30: the quadratic and
   discriminant conditions are rules for the untrusted **search**, not checks.
   The trusted checker needs only three things. The written decomposition must
   `ring`-equal the goal, every coefficient must be positive with every
   exponent even, and the constant must be positive, or non-negative on a
   non-strict goal.)*
5. **by sign product** — the goal is ring-normalised, a factorisation into
   strictly lower-degree factors is supplied, and the sign of the whole follows
   from the signs of the parts. **The factorisation is emitted and re-checked
   by `ring`**, like methods 3 and 4's witnesses; each factor's sign is an
   ordinary obligation and goes back through this same list, terminating
   because the factors are of strictly lower degree. It closes `> 0`, `< 0`
   and `# 0` goals alike — for `#` it is enough that every factor is nonzero
   — and, since the consolidation, non-strict ones (below).
   *(Discharge, E30: "strictly lower degree" is the search's rule. The
   checker checks the factorisation by `ring`, each factor's own certificate
   and the sign parity, and it terminates because every certificate is
   finite.)*
   The factorisation itself is untrusted input, from the learner or from
   §8.2's factoriser; the kernel checks it and never searches for it.
   **It may also split off a nonzero rational content**, c·p with p of the
   same degree, and take the sign of c times the sign of p. `3*sqrt 3 # 0`
   and `2*sqrt x # 0` need this: ring-normalised they are degree 1 in their
   atom, so the strict-degree precondition let neither through, and no other
   method reaches them alone. The split is not applied again to p, so the
   recursion still terminates. *(Revision 10, E18.)*

   **It closes non-strict goals too** *(revision 10, consolidation, E53)*.
   `1 − x^2 ≥ 0` on [0, 1] is the domain of every √(a² − x²) substitution,
   and no method reached it: a factor of 1 − x² is 0 at an end, so it has no
   strict sign there. Under a `≥ 0` or `≤ 0` target, each factor may now
   carry any of `>`, `<`, `≥`, `≤`. Under a strict target every factor must
   still be strict. The checker checks three things beside the `ring`
   identity and c ≠ 0:
   - the relations suit the target, as just stated;
   - the parity holds: with the target written g ≥ 0, sign(c) times (−1)
     to the number of `<` and `≤` factors is +1;
   - each factor's own obligation, fj rj 0 at the key's domain, holds by
     its own certificate.

   **Why it is sound.** At any point of the domain where the terms are
   defined, each factor has its certified sign, so the product's sign follows
   from the parity, zero included. A strict factor may serve a non-strict
   target, because it only strengthens it. A non-strict factor may never
   serve a strict one, because a factor that is 0 makes the product 0. The
   search tries each factor strict first, then non-strict. So 1 − x² is
   −(x − 1)(x + 1), with x − 1 ≤ 0 by the upper end (not < 0, since it is 0
   at 1) and x + 1 > 0 by the lower end, and the parity is (−1)(−1) = +1.
   **A content of −1 is not split off under a non-strict target**, because
   the one factor's goal would restate the key. The sign stays with the
   content in the certificate, as in −(x − 1)(x + 1).

   One consequence was missed by the consolidation's own specification, and
   found while re-tracing E56. π/2's sign now also closes as (1/2)·π with
   π > 0 by `cite pi_pos`, so a search that has lost the linear method's
   sign facts still proves `0 ≤ pi/2`. Two routes to one fact cost nothing in
   soundness. The cost is to the suite: the planted bug that drops `pi_pos`
   from the constraint set now shows only as a changed tag, where it used to
   change P1.1's admission count and refuse the sheet's substitution.
6. **by `cite`** — a named library fact (§6.8), with its own hypotheses
   emitted as obligations.

**Method 5 is new, and it regularises a move this document was already
making.** §11.2 closes `1 + x^3 # 0` as "a **product** of the two facts already
established above it, with `ring` certifying the factorisation" — which is
method 5 exactly, used before it was named. What forced naming it was §6.3's
sweep: `d_asin`, `d_acos`, `d_atanh` and `d_acosh` each emit a positivity goal
that **no other method on this list can reach**. `1 - u^2 > 0` under
`abs u < 1` is not linear, so method 3 does not see it; and it has no
sum-of-even-powers certificate, because none exists — the polynomial is
genuinely negative for |u| > 1, so method 4 is not being weak, it is being
correct. Factoring is what makes it linear again: `1 - u^2 = (1-u)(1+u)`, and
under `-1 < u < 1` both factors close by Fourier–Motzkin. `u^2 - 1 > 0` under
`u > 1` goes the same way through `(u-1)(u+1)`.

**Why this rather than four named lemmas in §6.8.** That was the cheaper-looking
fix and it is the wrong one, by §6.8's own admission criterion: its entries
exist because they are *positivity facts about an **opaque atom**, which `ring`
cannot know and `field` cannot derive*. `1 - u^2` is not an opaque atom. It is
a polynomial that `ring` understands completely, and the only thing missing was
a route from the domain to its sign. Putting it in §6.8 would file a fact about
a transparent term in the table reserved for facts about opaque ones, and would
leave the general shape open — the next integrand over `4 - x^2` or
`(1 - x^2)^3` would want another lemma. Method 5 closes the family.

**What it costs.** Nothing in the trusted base beyond the sign-combination
step, because the factorisation arrives from outside and is re-checked: a bug
in §8.2's factoriser costs a rejected step, never a false `Proved`, which is
§7's discipline applied unchanged.

**Before Fourier–Motzkin is consulted, the constraint set is checked
satisfiable.** This closes a class rather than an instance: *any* discharge
path that can consult an inconsistent constraint set proves everything, and the
reversed-limit exploit of §5.1 was one instance of it. *(Discharge, E28–E29,
owner's decision 2026-09-24: with checked witnesses, what carries soundness
has moved. An accepted Farkas certificate proves its obligation on its
domain, vacuously if the domain is empty. The danger was a wrongly built
constraint set. E4 closed that by owing every range's `lo ≤ hi`, and since
the consolidation E56 closes it more strongly: every range is built from a
proved order, so no range item is ever empty (§6.4). The
pre-check stays, **untrusted**, inside the search, so that the search never
reaches for a vacuous witness. It can only withhold a discharge. The checker
also demands a positive multiplier on the negated goal.)*

Methods 3, 4 and 5 emitting certificates — the Farkas combination, the
sum-of-squares decomposition, the factorisation — is what makes §7's claim true
rather than asserted: a bug in the Fourier–Motzkin implementation, or in
§8.2's factoriser, now costs a rejected step, because the kernel does not
believe the verdict, it checks the witness.
Without that, an obligation discharge is *terminal* — the kernel ticks and the
proof closes — and a bug there converts directly into a false `Proved`.

The list is **what is tried, in order, not an exhaustive account of what may
close an obligation**. A learner's third option is `have <name> : φ @ D by
<script>`, a nested proof of an ordinary §5.2 judgement — no new judgement
form, a convenience rather than a prerequisite, and its absence in revision 1
is why §12.1 reached for a method that did not exist.

Anything else is **not discharged**, and an undischarged obligation is
reported, never assumed. The list of live obligations is part of the proof
state the learner sees at all times (§16).

**One method is deliberately not here.** §10's enclosure engine could decide
sign and nonvanishing goals on compact domains — `cos t # 0` on [0, π/2 − ε],
and the `cosh u > 0` of §6.9. If it is ever wired in, it is a **trusted** rule
and belongs in §15's list as well as this one. Until then, the named positivity
facts of §6.8 cover the cases that actually block.

**Nor is there yet a method that decides an obligation false exactly**
*(revision 10, int_subst review, E50)*. Discharge refuses what it can show
false (§18 Q22), and one of its three ways is a rational counter-point. Since
the review, the candidates include the rational roots of the obligation's own
one-variable polynomials, so a rational pole inside a range is found (§5.4).
An irrational one is not. `t^2 − 2 # 0` on [0, 2] is false at √2, no
rational point shows it, and it stays admitted, tagged `none`. **Sturm
sequences are the recorded future method, not built.** They decide exactly
the sign of a one-variable polynomial on an interval, and they give a
certificate the trusted checker can re-check by counting sign changes. That
would make them the first method on this list that proves an obligation false,
rather than failing to prove it true.

### 5.4 Obligations and the obligation pane

Every rule application may emit obligations. The kernel maintains, for each
proof:

- **discharged** — with the method that discharged each one;
- **open** — blocking; the proof is `Stuck`, not `Proved`;
- **admitted** — the learner wrote `admit "reason"`. *(Revision 10: until
  discharge is built, the kernel itself admits every obligation it cannot
  discharge, with the reason `discharge not built` and a tag naming the §5.3
  method expected to close it, or `none` if no method can. The proof-of-life's
  verdicts all read `Proved modulo N admissions`.)* *(Discharge, E32–E33: the
  kernel now discharges at emission. It admits an obligation for one of four
  reasons: `regularity not built`, `no method decides it`,
  `domain inconsistent`, or `certificate not accepted`. An obligation
  discharge decides false refuses the step with `obligation-decided-false`
  instead of being admitted. An admission tagged `none` may still be false,
  such as `t^2 − 2 # 0` on [0, 2], which the bounded counter-point search
  misses.)* *(Revision 10, int_subst review, E50: the example was
  `x − 5 # 0` on [0, ∞), which is now refuted at x = 5. The search's
  candidates were a range's rational ends, its midpoint, and 0, 1 and −1,
  never a root of the obligation's own polynomial. So a pole strictly inside
  a range was admitted `none`. The skeptic's case: ∫ from −1 to 5/3 of 1/(x² + 1) by
  x := 5/(2t − 5) over [0, 4] puts one at t = 5/2, and it read
  `Proved modulo 9 admissions` for a false value. `ftc` alone has the same
  class. The search now also tries the rational roots of each one-variable
  polynomial piece of the obligation: the whole, each factor of a top-level
  product, and each base of an integer power. The roots are bounded as the
  tagger's factoriser is, and they are tried last, so no earlier refusal
  message changes. **An admission tagged `none` may be false exactly when no
  candidate refutes it.** The misses that remain are irrational roots, roots
  beyond the bound, and pieces in more than one variable. §5.3 names the
  exact method that would close the first.)*

A proof with admissions reports `Proved modulo 3 admissions`, listing them,
and never `Proved`. This is `Admitted` from Rocq, and it is what makes the
system usable without making it dishonest: incompleteness becomes a visible
debt rather than a silent lie.

---

## 6. The rule table

The rules are the trusted base. They are grouped below with their side
conditions.

**What selects a rule, and what states it.** These are different, they are
easy to run together, and §1's rule about coupling applies here more than
anywhere else in the document. *Which* rules the table contains is a question
about the target corpus, answered in §13 — a rule is here because something
that must work needs it. *How* each rule is stated — its conclusion, and
exactly which hypotheses it carries — is a question about the mathematics and
has no other input. Nothing in the corpus may weaken a side condition, and the
justification notes below ("without this, such-and-such is blocked") are
**selection notes, not derivations**. A rule that was selected for a bad reason
is clutter; a rule that was *stated* for a bad reason is unsound.

**Two counts, not one.** Revision 1 said "~60 rules" in four places. Counting
only what is named explicitly below gives 64 before §6.8's exact-value table,
before expanding "limit laws" into its actual six, and before §6.9's ~25
regularity rules; three independent recounts during review landed at ~80, ~100
and ~110, differing over how to count the table. The honest form is two
figures, and they behave differently:

- **analysis rules** — each a real theorem needing a real proof if §14 ever
  runs: on the order of 55–70;
- **an identity and exact-value table** — `sin_PI6`, `cos_PI4` and friends,
  which are already in Rocq's `Stdlib.Reals.Rtrigo_calc` and would mostly carry
  the `cited` tag: on the order of 25–45.

The recount is owed before §14 can be priced. **Enumerate the table before
committing to any estimate that depends on it** (§17).

Revision 1 claimed that the table's reviewability *is* the soundness argument.
That claim is dropped. Review is weak evidence — HOL Light's ~400-line kernel,
far smaller than this one, had genuine unsoundnesses found after years of
expert reading — and §15 now states what the argument actually is.

### 6.1 Structural

`hyp`, `refl`, `sym`, `trans`, `cong` (congruence under any term former),
`rewrite h at p` (rewriting with a proven equation at a position, carrying the
position's domain), `weaken` (from `φ @ D` and `D' ⊆ D` conclude `φ @ D'`),
`cases` (split on a decidable trichotomy), `close` (§9).

**Under a binder, a domain-limited equation is not enough (revision 9).**
Pointwise equality on D gives equal derivatives only where D contains an
open neighbourhood of the point. Unrestricted, `cong` and `rewrite` would
take `sqrt_sq : sqrt(x^2) ≐ x @ x ≥ 0` under `D[x]` to
`D[x] sqrt(x^2) ≐ 1 @ x ≥ 0`, which is false at 0. So:
- Under `D[x]`, the equation must hold `@ ⊤` or on an **open** domain (strict
  inequalities only), and the result carries that domain.
- Under `lim[x → c]`, it must hold on a punctured neighbourhood of c.
- Under `Int[x = a .. b]`, the range domain of §5.3's method 2 is enough,
  because the integral depends only on values on the range.

The proof-of-life review found this. No worked example needs the forbidden
case, which is why it had gone unnoticed; §17's bank now carries it as a
must-refuse.

**`# 0` counts as open, beside the strict inequalities (revision 10).** Read
literally, "strict inequalities only" forbids §6.3's own routing of `u / v`
through `u * (1/v)`, which holds at `v # 0`, and `D[x](x/(x+1))` would have no
route at all. For a term continuous on an open domain, the set where it is
`> 0`, `< 0` or `# 0` is open, so `# 0` is admitted too, and a domain item that
does not mention x does not count against the rule. A hypothesis mentioning x
must still avoid the non-open partial formers (`sqrt`, `asin`, `acos`,
`acosh`) and `Int` or `D` subterms, and so must anything the rewrite charges at the position
(`kernel/p1_expected.py` E11).

**Rewriting under `Int` owes the range's orientation (revision 10).** The range
domain `a ≤ t ≤ b` is only the range once `a ≤ b` is known; with the limits
reversed it is empty, and an empty domain makes every obligation on it
vacuous. So a rewrite whose position lies under an integral was made to owe
`a ≤ b`, exactly as `ftc` was (§6.4). *(Revision 10, consolidation, E56: it
now decides the order instead, as every step that builds a range does. The
position domain holds [a, b] or [b, a], whichever discharge proves, and the
step is refused `orientation-undecided` if neither is. That is enough,
because the integral depends only on the range as a set. The order of each
enclosing integral is decided, outermost first, before any key at the
position is emitted.)*

**`rewrite` matches up to ring-normalised atom arguments, and acts on every
occurrence it is given** (revision 10, settling §18 Q21). The rule is
instantiated explicitly. It fires where the instantiated left-hand side and the
target subterm agree once the arguments of their atoms are ring-normalised,
which is the congruence §6.2 already uses for atom identity. With no position
given, it rewrites every occurrence, which is the same as applying `rewrite h
at p` once at each, since each position carries its own domain and its own
side conditions. A bound variable is matched by the binder case, with the side
condition discharged from the enclosing integral's range; that is §11.1's
`sqrt_sq` on t. The full statement is `kernel/p1_expected.py`'s
`REWRITE_RULE`.

**No rule may erase an `Int` or `D` node unless its definedness is owed**
*(revision 10, consolidation review, E57)*. This principle was found through
a false `Proved.`. `rewrite` matches a left side that is not an application,
such as `pyth`'s sum, as a tree, and that branch never passed its instance
values through `ring_nf`. `ring_nf`'s refusal of `Int` and `D` (§6.2) was
what had kept those nodes out of every earlier rewrite. `pyth` was also the
first equation entry whose right side drops its schema variable. So
`(sin(D[x](abs x)))^2 + (cos(D[x](abs x)))^2 ≐ ?A` rewrote to `1`, owing
nothing, and `close 1` reported a plain `Proved.`, though |x|′ does not exist
at 0. With u := `Int[x = 1 .. oo] 1`, a divergent integral, it went the same
way. Until §18 Q23's formers land, nothing states when such a node denotes,
so "unless its definedness is owed" means never, except where the rule's own
premises owe it, as `ftc`'s do for the integral it consumes.
- **`rewrite` refuses at a new step 2a, on every match branch.** If any
  instance value, or the target position itself, holds an `Int` or `D` node,
  the step is refused `Int-or-D-not-normalisable` before anything is
  matched. `(sin z)^2 + (cos z)^2` still rewrites to 1 and proves, owing
  nothing, which is right.
- **Every other move was checked against the principle, and complies.**
  `close`'s whitelist refuses such a value, and its check's `ring` or `field`
  refuses any side holding one. `int_subst` and `int_flip` carry a nested
  node into the new body and drop nothing. A `fact` whose instance holds one
  keeps it in its conclusion, and every use refuses it. Field facts, exact
  values and every certificate checker go through `ring_nf`, which refuses
  the node.
- **A limit holding an `Int` or `D` node is refused outright by `ftc`,
  `int_subst` and `int_flip`** *(second review)*. Such a limit has no
  definedness the kernel can state, and each move would carry it into the
  goal (§6.4).

### 6.2 Algebra — the three places a normal form is allowed

These are decision procedures, complete for their fragment, implemented
reflectively: the normal form is computed by an algorithm over a small data
structure, and both sides are compared. Non-polynomial subterms (`sin x`,
`exp u`) are **opaque atoms**, which is what keeps this sound — the procedure
never claims to know anything about `sin`.

- **`ring`** — equality in the commutative ring ℚ[atoms]. Sparse multivariate
  polynomials, exact rational coefficients. Decides its fragment. Division
  by a nonzero literal is a coefficient. **Division by anything else is itself
  an opaque atom**, so `m * (1/m) ≐ 1` is not a `ring` fact, and neither is
  `1/x^2 ≐ (1/x)^2`. The atom is the inverse: `a / d` is read as
  `a * inv(d)`, with `inv(d)` keyed by d's normal form. Matching `atan_odd`
  against `atan((2*0 - 1)/sqrt 3)` needs exactly that reading (revision 10,
  E3). Relating them is `field`'s job, and `ring` emits no
  obligations because it cancels nothing.
- **`field`** — equality in the field of fractions. Normalises lhs − rhs to a
  numerator over a product of denominator factors and holds when the
  numerator is the zero polynomial. It **emits `d # 0` for every divisor `d`
  in its input**: every `e / d`, every `d ^ n` with n < 0, and those inside
  an atom's arguments. A literal divisor is discharged at once by `norm_num`.
  A divisor that normalises to zero is refused. This is the rule where a
  careless implementation becomes unsound, and it is the one to review
  hardest.
- **`norm_num`** — closes goals over rational literals exactly.
- **All three refuse a side containing `Int` or `D[x]`** (revision 10, §5.1).
  An opaque atom is assumed to denote, and neither of those can be shown to
  until regularity and `diverges` exist, so `ring` may not cancel
  `Int[…] - Int[…]` to 0.

**Why "every divisor" and not "every denominator it cancels".** Revisions
1–6 said the latter, and stage 0c found it cannot be implemented as a
specification: a normaliser has no well-defined record of which denominators
it cancelled. Every divisor is the conservative reading. It also coincides
exactly with what §5.1's `/` former already charges, so `field` never
introduces an obligation the term did not already owe, and reviewing it
reduces to checking that nothing is dropped.

**Facts.** `field [h₁, …]` takes proven equations of the shape `a^k ≐ r`, a
power of one opaque atom on the left and a right side mentioning no fact's
atom. Each is an instance of a §6.8 rule, usually `sqrt_sq_val`. The
numerator is reduced modulo them before the zero test: each `a^k` is replaced
by `r = P/Q`, and the result is multiplied through by the highest power of Q
used. Q ≠ 0 is among the fact's own obligations, so the reduced numerator is
zero exactly when the original is. **Soundness needs only that each fact is a
theorem**, and in the kernel it is one, passed as a handle (§15.3). This is
the step §11.2 needs and a rewrite cannot give it (see there). It is *not*
the extension of the coefficient field declined below: no algebraic number is
built in, and each fact is named, cited and visible in the proof. The
reduction is complete for the case that matters, `(sqrt c)^2 ≐ c` with c not
a rational square; it is not claimed complete in general.

**Atoms are identified up to their arguments' normal forms.** `sin(x + 1)`
and `sin(1 + x)` are one atom. That is congruence and nothing more.
Arguments that are equal only as rational functions *with different
representations* give two atoms, `sin(x/x)` and `sin 1` for instance. That
makes the procedure incomplete, not unsound.

`sin x + cos x ≐ cos x + sin x` is `ring`. `sin²x + cos²x ≐ 1` is **not** — it
needs the named identity `pyth`. That asymmetry is not a restriction on anyone;
it is the price of soundness. `ring` is sound precisely *because* it knows
nothing about `sin`, so every fact about `sin` has to enter through a rule that
is a theorem. Which rule to reach for is a question `auto` will happily answer
for you (§8.1) — the point is only that something has to answer it, and a
normalizer that guessed would be the unsound kind. *(Revision 10,
consolidation, E54: `pyth` as stated cannot be a `field` fact, because its
left side is a sum and a fact must be a^k ≐ r. `rewrite` can use it, at a
subterm that is the sum as a tree. The form both can use at (cos b)^2 is its
solved form `pyth_cos` (§6.8).)*

**The same property is what makes surds awkward, and §11.2 is where it bites.**
`sqrt 3` is an opaque atom, so `field` sees a free atom *s* unrelated to 3.
That is handled by naming the missing facts as rules (§6.8's `sqrt_sq_val` and
`sqrt_pos`) and handing them to `field` as facts (above), not by teaching
`field` about radicals. Extending the coefficient
field to ℚ(√d₁,…,√dₖ) is explicitly declined until someone argues it into
§15's trusted base.

### 6.3 Derivatives

**Twenty-four entries, each with its output form and its side condition.**
The chain factor is carried in the entry rather than by a separate rule, so
`d_chain` is left for declared function symbols.

```
  d_const     D[x] e         ≐  0                                @ x not free in e
  d_var       D[x] x         ≐  1
  d_add       D[x](u + v)    ≐  D[x]u + D[x]v
  d_mul       D[x](u * v)    ≐  D[x]u * v + u * D[x]v
  d_chain     D[x] f(u)      ≐  f'(u) * D[x]u                    -- declared symbols
  d_pow_int   D[x](u^n)      ≐  n * u^(n-1) * D[x]u              @ n ≠ 0; n < 0 ⟹ u # 0
  d_pow_real  D[x](u^v)      ≐  u^v * (D[x]v * ln u + v * D[x]u / u)   @ u > 0
  d_inv       D[x](1/u)      ≐  -(D[x]u) / u^2                   @ u # 0
  d_sqrt      D[x](sqrt u)   ≐  D[x]u / (2 * sqrt u)             @ u > 0
  d_ln        D[x](ln u)     ≐  D[x]u / u                        @ u > 0
  d_exp       D[x](exp u)    ≐  exp u * D[x]u
  d_sin       D[x](sin u)    ≐  cos u * D[x]u
  d_cos       D[x](cos u)    ≐  -(sin u) * D[x]u
  d_tan       D[x](tan u)    ≐  (1 + (tan u)^2) * D[x]u          @ cos u # 0
  d_asin      D[x](asin u)   ≐  D[x]u / sqrt(1 - u^2)            @ abs u < 1
  d_acos      D[x](acos u)   ≐  -(D[x]u) / sqrt(1 - u^2)         @ abs u < 1
  d_atan      D[x](atan u)   ≐  D[x]u / (1 + u^2)
  d_sinh      D[x](sinh u)   ≐  cosh u * D[x]u
  d_cosh      D[x](cosh u)   ≐  sinh u * D[x]u
  d_tanh      D[x](tanh u)   ≐  (1 - (tanh u)^2) * D[x]u
  d_asinh     D[x](asinh u)  ≐  D[x]u / sqrt(u^2 + 1)
  d_acosh     D[x](acosh u)  ≐  D[x]u / sqrt(u^2 - 1)            @ u > 1
  d_atanh     D[x](atanh u)  ≐  D[x]u / (1 - u^2)                @ abs u < 1
  d_abs       D[x](abs u)    ≐  (u / abs u) * D[x]u              @ u # 0
```

`d_abs` is new in revision 6 with `abs` admitted to goals (§5.1). It needs no
`sign` former: `u / abs u` *is* the sign, written in the grammar, and the
obligation `abs u # 0` follows from `u # 0` by §6.8's `abs_pos`. Twenty-four
entries.

**`d_const` covers any term free of x**, not only a rational literal
(revision 7). As first stated it left `D[x] pi`, `D[x] sqrt 3` and `D[x] y` for
another variable y without a rule, and §11.2's F has `1/sqrt 3` as a factor. Stage
0c's `deriv` also met two formers that have no entry, and they are
deliberately left without one: **`-u` and `u / v` are routed through the
algebra, not given rules**. `-u ≐ (-1) * u` is `ring`, and
`u / v ≐ u * (1/v)` is `field`, owing `v # 0`, which the term already owed.
After that, `d_mul` and `d_inv` apply. That keeps the table at twenty-four
entries and puts no new theorem in the trusted base.

Every entry carries its condition inline; revision 1 listed `d_pow_int` bare
and had no rule for `tanh`, which unit 00 P4's answer v(t) = v∞ tanh(gt/v∞)
needs in order to be checked at all.

**Each entry also has to pin its *output form*, not only its name and its side
condition** (stage 0, `STAGE0.md` gap 3). `sec` and `sech` are not in §5.1 and
are not going to be, so the textbook statements of `d_tan` and `d_tanh` —
sec²*u* and sech²*u* — name terms this language cannot hold. They are
`1 + (tan u)^2` and `1 − (tanh u)^2`, which are the same functions written in
the grammar's own vocabulary. The general rule is that **a derivative entry
whose usual statement reaches outside §5.1 is not yet stated**, and it applies
wherever sec, csc, cot or sech would appear. This is what the table costs for
keeping the grammar small, and it is cheap — but it is a sweep of §6.3 rather
than two patches, because a bare name in a table looks finished and is not.

**The sweep is now done, and it found one thing the thirty goals did not.**
Every right-hand side above parses under §5.1, so gap 3's two corrections were
the only ones of that kind. Two other things came out of writing them down:

- **`d_pow_int` needs `n ≠ 0`.** At n = 0 the stated form produces `u^(-1)`,
  which is a field operation carrying a nonvanishing obligation the rule has no
  business emitting — D[x](u^0) is D[x] 1, and belongs to `d_const`.
- **Four entries emitted a positivity obligation no §5.3 method could
  discharge, which is now fixed there.** `d_asin` and `d_acos` need
  `1 - u^2 > 0` to know their `sqrt` is nonzero, `d_atanh` needs `1 - u^2 # 0`,
  and `d_acosh` needs `u^2 - 1 > 0` — each from a hypothesis (`abs u < 1`, or
  `u > 1`) that is not linear in the goal. Fourier–Motzkin works over the
  *linear* fragment and does not see them, and no sum-of-even-powers
  certificate exists for `1 - u^2` because the polynomial really is negative
  for |u| > 1. **§5.3 gains a fifth method, `by sign product`**, which factors
  and multiplies signs: `1 - u^2 = (1-u)(1+u)`, both factors linear and both
  positive under `-1 < u < 1`. §11.2 was already making that move unnamed for
  `1 + x^3 # 0`; naming it closes the family rather than these four cases, and
  the alternative — four named lemmas in §6.8 — was rejected there because
  `1 - u^2` is not the opaque atom §6.8's admission criterion requires.

*That is the argument for sweeping a table rather than trusting the goals that
happen to use it. Thirty goals applied `d_asin` twice and never once asked how
its side condition gets discharged, because SymPy was doing the checking and
SymPy has no obligations.*

`deriv` is then a *tactic*, not a rule: it walks the syntax applying these,
emitting each application as a kernel step and collecting the side conditions.
It is untrusted — if it has a bug, the kernel rejects its output.

**That holds once a kernel step re-derives `ftc`'s derivative premise, and in
the proof-of-life none does** (revision 10). There, `ftc` accepts `deriv`'s
output and records the premise as discharged by `deriv; ring` or
`deriv; field`, so `deriv`'s output forms and side conditions *are* the rule
table and it is trusted, under §15.2 item 2. The planted bug `d_ln` emitting
nothing is exactly a false theorem from it. Two entries, `d_chain` (`f'`) and
`d_pow_int` (a literal n as a parameter), are written above in a schema
notation that has no term syntax, so they are built in code rather than parsed
from a pinned statement.

### 6.4 Integrals — the keystone

The single most important design decision in this document:

> **The system never integrates. It differentiates, and checks.**

```
   Γ ⊢ F ∈ C⁰([a,b])   Γ ⊢ F ∈ C¹((a,b))   Γ ⊢ D[x] F ≐ f @ (a,b)   Γ ⊢ f ∈ C⁰([a,b])
  ftc ─────────────────────────────────────────────────────────────────────────────────
                    Γ ⊢ Int[x = a .. b] f  ≐  F(b) − F(a)
```

**The range must be oriented (revision 10).** With b < a, [a,b] and (a,b) are
empty, all four premises hold vacuously, and the rule as drawn proves
∫₁⁻¹ 1/x² dx ≐ 2, which gives a divergent integral a value. §5.1 says what a
reversed integral denotes, and §5.3's method 2 guarded its own use of the
range, but `ftc` itself was unguarded, and so was rewriting under `Int` (§6.1).
**The first fix made every step that uses a range owe `a ≤ b`.** It was
decided by `norm_num` when both ends are literals, fixed by an infinite end,
and otherwise emitted as an ordinary obligation. `ftc` refuses an infinite
endpoint outright, since F(∞) is not a term, and `int_improper` is the route.
*(Found by the proof-of-life: `kernel/p1_expected.py` E4 and E9.)*

**Since the consolidation, the range is built from whichever order
discharge proves** *(revision 10, consolidation, E56, the owner's answer)*.
Owing `a ≤ b` outright was too strong. A correctly reversed symbolic range,
∫_{π/2}^0, owed `pi/2 ≤ 0`, which is false, so it was refused wherever a key
used the range, and only `int_subst` had a way round it. There is now one
rule for every step that builds an interval from an integral's limits:
installation's and every new goal's formers, `rewrite`'s position domain,
`ftc`'s premises, `int_subst`'s old and new ranges, and `int_flip`'s new one.
- **Two literal ends** are ordered by `norm_num`, and **an infinite end**
  fixes the order, as before.
- **Otherwise the kernel asks discharge for lo ≤ hi, then for hi ≤ lo**, at
  the integral's position domain, with no counter-point search. The first
  proved is emitted as the step's orientation key, already discharged, and
  the interval is [lo, hi] or [hi, lo] accordingly. Nothing more is owed
  about order. Readiness P1.1's key is `0 ≤ pi/2`, closed by linear
  arithmetic with `pi_pos`, as before.
- **If neither is proved, the step is refused `orientation-undecided`**,
  naming both ends and asking for the order in the goal's domain. That is
  one code for every step. `Int[t = 0 .. y] sqrt(t^2)` is refused at
  installation, because y is free. Under E4 it owed `0 ≤ y`, which the
  counter-point search refuted at y = −1, a refusal for the wrong reason.
- **Enclosing ranges are decided first** *(consolidation review)*. A position
  domain holds the range of every enclosing integral, so a step emitting any
  key there first decides each enclosing order, outermost first, and is
  refused on the first that no discharge decides. The skeptic's case,
  `Int[y = a .. b] (Int[x = a .. y] 1)` with `int_subst` on the inner
  integral, had emitted its premises on y ∈ [a, b] with a ≤ b never
  decided. It is refused now, and with `@ a ≤ b` on the goal it is accepted,
  that hypothesis certifying the order.
- **Orders are decided lazily, and memoised** *(consolidation review)*. An
  order is decided only when a key whose domain holds that interval is
  emitted, so a range no key uses is never decided. Each decision is
  memoised per key, which is safe because discharge is a function of the key
  and the entries alone. `Int[x = (a-1)^40 .. 0] sin 0 ≐ ?A` owes nothing at
  installation, and the first build took 30.5 s deciding its order anyway.
  It now decides nothing and installs at once.

**Why a proved order is enough.** §5.1's exploit was a constraint set that
assumed a ≤ b when b < a, so the range was empty and every obligation on it
vacuous. A proved order cannot be wrong, because its certificate is checked,
so the interval built is exactly the set of points between the limits, and
it is never empty. An integral's value (§5.1: ∫_a^b = −∫_b^a) and its
definedness depend only on the integrand on that set, so every former,
hypothesis and premise stated on it is the right one for either order.
`ftc`'s F(b) − F(a) holds for either order, since for b < a,
∫_a^b f = −(F(a) − F(b)), and its premises sit on [min, max] and
(min, max). Rewriting under an integral needs only the range as a set
(§6.1), and `int_subst`'s premises are on the closed interval between its
limits. Equal limits make both orders provable and give the same point. The
order key is still emitted, so what a proof relied on stays in its tracker.
So `Int[x = pi/2 .. 0] 2*x` closes to −π²/4 by `ftc` alone, and
`Int[t = pi/2 .. 0] sqrt(t^2)` to −π²/8 through `sqrt_sq` under the reversed
integral, both modulo their 3 regularity admissions.

**No tree in a limit** *(revision 10, second review, E57 amended)*. `ftc`,
`int_subst` and `int_flip` test the limits of the integral they act on, and
`int_subst` its new limits too, for an `Int` or `D` node, and refuse
`Int-or-D-not-normalisable` before anything is emitted and before any order
is decided. Such a limit has no definedness the kernel can state, and
`ftc`'s F(b) − F(a), `int_subst`'s endpoint images and `int_flip`'s new
integral would each carry it into the goal with nothing owed (§6.1). `ftc`
and `int_subst` did refuse `Int[x = 0 .. (Int[y = 1 .. oo] 1)] 0` before,
but only by accident. `ftc` and reverse `int_subst` read
`orientation-undecided`, because `norm_num` refused the orientation key
inside the order decision, and forward `int_subst` was stopped by its
endpoint check's `ring`. `int_flip` accepted it, since no key used the new
range. `int_flip` erased nothing, and is included by decision, so that one
rule covers the three moves.
Installation is unchanged: a goal may hold such an integral, and every key
holding the tree is refused as before.

**The regularity premises split across the closed and the open interval, and
that is a correction rather than a refinement** (stage 0, `STAGE0.md` gap 1).
Revision 5 asked for `F ∈ C¹([a,b])` throughout, and under that statement the
rule **cannot close ∫₀¹ √(1−x²)**: the antiderivative is
F = (x√(1−x²) + asin x)/2, and at the right endpoint `d_sqrt` wants u > 0 where
1−x² is 0, while `d_asin` wants |u| < 1 where |x| is 1. The integrand is
bounded and continuous on the closed interval and the value is π/4, so nothing
here is a convergence question — it was the rule demanding of *F* what only *f*
can be asked for. Every √(a²−x²) trig substitution lands on it, and §8.5 has
that as a recognizer row, so this was not an edge case. The split form is the
standard theorem: F continuous on [a,b], differentiable on the interior with
F′ = f there, and f continuous on [a,b] — which is what makes the last premise
**load-bearing rather than redundant**, since C¹ on the interior no longer
forces anything about f at the endpoints. §5.2's domains express `a < x < b`
already (§5.3), so this costs no new machinery. *(Two consequences to carry:
§15.5's `is_RInt_derive`/`RInt_Derive` citation was chosen against the closed
form and its hypotheses need re-checking against this one before §14 counts it
`cited`; and `int_improper`'s finite-singularity route, which was the other way
to reach this integral, is now reserved for genuinely improper cases rather
than being the detour a bounded continuous integrand has to take because its
antiderivative misbehaves.)*

Finding *F* is hard — undecidable in general. Checking `D[x] F ≐ f` is
**sound, cheap, and complete whenever the residual lies in ℚ(atoms)**; beyond
that it needs one of §6.8's identity rules, which `auto` searches for.

Revision 1 called the check *decidable*. It is not, and §3 had just said why:
`D[x] F ≐ f` is an instance of the very predicate Richardson's theorem rules
out. Two documented cases fall outside ℚ(atoms), and both are in this
document's own material:

- **Trig identities.** After §8.5's √(a²−x²) → x = a sin θ, matching
  (1 + cos²θ − sin²θ)/2 to cos²θ needs `pyth`; sin θ and cos θ are unrelated
  atoms to `field`.
- **Algebraic constants.** §11.2's central obligation needs (√3)² ≐ 3, which is
  a rule, not an algebraic fact about an opaque atom.

Both are provable once the right rewrite is applied, and **the trig half is now
handled rather than deferred** — which is a change from revision 5, made
because stage 0 showed the gap was wider than the two cases above suggest.
∫₀^{π/2} cos²x dx has no substitution in it and still escapes ℚ(atoms), since
`cos x`, `sin 2x` and `cos 2x` are unrelated atoms to `field`; the manual-rewrite
consequence was therefore landing on the most ordinary integrals in the corpus,
not on the exotic ones. **§8.9's `trig_norm` lands in stage 1** and makes the
check *decidable* whenever the residual is a trig polynomial in a single base
angle — subsuming the first case above along with the plain ones. It is a
canonicalisation rather than a search, which is why it does not drag `auto`
forward with it, and it is an untrusted tactic emitting §6.8 rewrites, so it
adds nothing to the trusted base.

What remains a scheduling problem is the **algebraic-constant** case: `auto` is
stage 3, `ftc` and `subst` are stage 1, so between those stages a close needing
`sqrt_sq_val` or a similar fact about an opaque atom is a manual step: the
learner names the fact and it is passed to `field` (§6.2). It is not a
rewrite, because the square it needs usually exists only after
normalisation (§11.2).

The payoff of the asymmetry is unchanged and is the reason the project exists:
the kernel needs **no integration algorithm at all**. No Risch, no table of
integrals, no search over antiderivatives. Several hundred lines of the most
error-prone code that would otherwise be in the trusted base simply do not
exist. Six reviewers looked for a path from the integrator, the factoriser, the
partial-fraction solver, the recognizer, the palette or §8.7's residual
reporting to `Proved` without a kernel step re-deriving it, and none of them
found one.

That is a statement about the *kernel*, not about what you are left alone
with. Above it sit two other ways to work: grinding the integral down step by
step with the forward rules below, each step checked (§8.1), or handing the
whole thing to the integrator (§8.2). All three routes end at the same `ftc`
obligation.

Around `ftc`: `int_linear`, `int_parts`, `int_split`, `int_improper` (as a
limit to `oo` or to a finite singularity, with a convergence obligation),
`int_compare` (convergence by an explicit dominating function), `leibniz`
(differentiating under the integral sign, with a uniform-domination obligation
— this is the expensive one, see §13), and:

**The divergence rules, new in revision 6 with §5.2's `diverges` judgement.**
`div_limit` — the defining limit of the partial integrals is infinite or fails
to exist, which is the definition discharged directly. `div_compare` — from
`0 ≤ g ≤ f` on the range and `diverges(∫g)`, conclude `diverges(∫f)`; the
dominating function is supplied, never searched for, exactly as `int_compare`
takes its dominator. `div_power` — the p-test, `∫₀¹ x^p` diverging for p ≤ −1
and `∫₁^∞ x^p` for p ≥ −1, which is what the pole cases actually reach for.
`div_pole` — an interior pole with a one-sided divergent piece makes the whole
divergent, via `int_split`. §6.7 carries the series duals, where the
contrapositives of `compare`, `ratio` and `root` already have the right shape
and the harmonic series is the case that wants them.

*(**How `leibniz` and `int_improper` compose is not stated**, and stage 0
reached it: ∂ₐ∫₀¹ xᵃ dx = −1/(a+1)² is a perfectly ordinary use, and the
integral is improper for −1 < a < 0 while staying convergent. One rule carries
a uniform-domination obligation, the other is a limit, and nothing says what
the obligation becomes when the integral underneath it is a limit. Readiness P7
is where `leibniz` is wanted (§18 Q5), so this is owed before P7 rather than
before stage 1. `STAGE0.md` gap 10.)*

```
    Γ ⊢ φ ∈ C¹([a,b])        Γ ⊢ f(φ(t)) ∈ C⁰([a,b])
  int_subst ──────────────────────────────────────────────────────────
    Γ ⊢ Int[x = φ(a) .. φ(b)] f  ≐  Int[t = a .. b] f(φ(t))·φ′(t)
```

**The continuity hypothesis is stated on the composed integrand, deliberately.**
The mathematically natural form is *f* continuous on φ([a,b]), with
monotonicity not needed — and that is the correct theorem. But nothing in this
design computes an image-valued domain: §5.3's discharge routes and §7's `reg`
both *consume* a domain, and the endpoint interval is not the image (φ(t) = t²
on [−1,1] with f = 1/x makes the endpoint interval the single point {1}, the
obligation trivial, and licenses a divergent integral). For continuous φ on a
compact interval, `f(φ(t)) ∈ C⁰([a,b])` is equivalent to f ∈ C⁰(φ([a,b])) — φ
is a closed map onto its image, hence a quotient map — it is expressible in
§5.2 exactly as written, and it is discharged by `reg` like every other C⁰
obligation. The generality is kept and the unstatable hypothesis is not.

*(The two alternatives, recorded and not taken: a constant-sign-of-φ′
certificate, which costs the no-monotonicity generality; or a §10 interval
enclosure R ⊇ φ([a,b]) with f ∈ C⁰(R), which is sound but is stage-2 machinery
against a stage-1 target. `sep_autonomous` inherits whichever is chosen.)*

**`int_subst` as built reads the rule both ways (revision 10, int_subst).**
The letters are the drawn rule's. [a, b] is the range on which the map is
differentiated, and every premise sits on it: it is the new range in forward
mode and the old one in reverse.
- **Forward, x := φ(t)**, which is §11.1's
  `step subst (x := t^2) over t in [0, pi/2]`. The learner supplies φ and
  the new range [a, b]. The kernel computes φ′ by `deriv` and never takes it
  as an argument, so the classic forgotten-dx error cannot be typed. It
  builds f(φ(t)) by the trusted capture-avoiding substitution, and replaces
  the integral with `Int[t = a .. b] f(φ(t))·φ′(t)`. This is the rule as
  drawn, read left to right.
- **Reverse, u := g(x)**, which is the learner's "let u = x²". The goal's
  integral is the right-hand side, with x for t and g for φ. The learner
  supplies g, the new limits and the new integrand f(u). The kernel computes
  g′ on [a, b] and checks **integrand ≐ f(g(x))·g′(x)** by `ring` or `field`,
  taking facts as `ftc`'s check does. It then replaces the integral with
  `Int[u = c .. d] f(u)`, where c and d are the learner's new limits. This is
  the same theorem read right to left, and that identity is the checked link.
  A failed check refuses the step with its residual. HolPy's first probe
  (§4.2), ∫₋₁¹ x² by u = x² with new limits 1 .. 1 and f = √u/2, is refused
  there, because f(g(x))·g′(x) is x·√(x²), and that is −x² for x < 0.

**What it owes, and where each premise lives.**
- **φ ∈ C¹ and f(φ(t)) ∈ C⁰ on [a, b], closed.** Both are admitted as
  `regularity not built` until §6.9 exists, so a proof through k
  substitutions and one `ftc` reads `Proved modulo 3 + 2k admissions`. In
  reverse mode they are g ∈ C¹ and f(g(x)) ∈ C⁰ on the old range. By the
  closed-map argument above, that is f continuous on g([a, b]), so g need not
  be monotone and nothing is refused for it.
- **`deriv`'s side conditions for φ′, also on the closed [a, b]**, not on an
  open interval as `ftc`'s are. The theorem asks φ ∈ C¹([a, b]), and φ′
  stands in the new integrand, which must be defined at the ends.
- **The endpoint equations.** A goal's limits are written values, not the
  images φ(a) and φ(b), so the step owes φ(a) ≐ the lower limit and
  φ(b) ≐ the upper. In reverse mode it owes g(a) ≐ c and g(b) ≐ d. They are
  two obligations, because a goal is a list (§5.2), and **both are decided
  in the step, never admitted.** §6.8's exact values are applied first, then
  the move's `ring` or `field`. A mismatch refuses the step with the
  residual, lower end first. There are two reasons for deciding them in the
  step. An equation is not a target of any §5.3 method, so a true
  non-literal one such as `(pi/2)^2 ≐ pi^2/4` could otherwise only be
  admitted. And without the exact values, x := ln t over [1, e] could never
  pass, since `ln 1` is an atom to `ring`.
- **The composed integrand's formers**, charged on [a, b] when the new goal
  enters, as every new goal's are (§5.1). That is where §11.1's nested
  `t^2 ≥ 0` comes from. The new variable must be fresh in the goal.
- **The orientation of each range**, below.

**Reading C¹ off `deriv` is sufficient, not necessary.** x := t·√t over [0, 1]
is C¹, with φ′ = (3/2)√t continuous on the closed range. But `d_sqrt` owes
t > 0 on [0, 1], which is false at 0, so the step is refused. That is a
completeness limit and not a soundness one. It goes away only with §6.9's
regularity rules, which can state C¹ without differentiating through the
root.

**A decreasing φ keeps the correspondence by end, not by order.** The new
lower limit is the preimage of the old lower limit, so a decreasing φ gives
reversed new limits, a > b.
- **With two literal ends**, the range is ordered by `norm_num` and nothing
  is owed. The limits are kept as given, reversed or not (x := 1 − t over
  [1, 0]), and §5.1 gives them their meaning.
- **With symbolic ends**, the kernel asks discharge for a ≤ b. If that is
  proved, it is owed and the limits are kept. Otherwise it asks for b ≤ a. If
  that is proved, the step emits the **flipped, oriented** integral
  `Int[t = b .. a] −(f(φ(t))·φ′(t))`, with the premises on [b, a]. If neither
  order is proved, the step is refused with `orientation-undecided`. The flip
  is §5.1's definition of a reversed integral composed with this rule. It is
  a trusted addition to the rule table and owes nothing beyond the
  discharged order. It is what lets §5.1's x = cos θ over [π/2, 0] through.

Reverse mode orients its new limits c and d in the same way. It decides the
old range's order as every step does, and its premises sit on the interval
that order gives.

*(Revision 10, consolidation, E56: this decision rule began here and is now
every step's, above, with `int_subst`'s own code
`int-subst-orientation-undecided` replaced by the shared one. Two things
follow. It is no longer stricter than `ftc`, which under E4 emitted an
undecided order and admitted it; every step now refuses one. And the flipped
form is a choice rather than a necessity, since the unflipped reversed
integral is now usable too; `int_subst` keeps it. Readiness P1.1 without
`pi_pos` in the constraint set is no longer refused at its `subst` step:
since E53, `0 ≤ pi/2` also closes by sign product with `cite pi_pos`
(§5.3).)*

**It acts on one integral, chosen as `rewrite` chooses a position.** An
optional occurrence selects the k-th integral, counting as `rewrite` counts
(§6.1). With no occurrence given, exactly one integral binding the named
variable must exist, and two or more refuse the step as ambiguous. This is
not `rewrite`'s every-occurrence default. Two integrals binding x generally
have different limits and bodies, and one set of endpoint equations fits only
one of them. Everything is owed at the position's domain: the goal's domain,
plus the range of each enclosing integral. Putting the new integral in place
of the old one is `rewrite`'s congruence. Under a `D[y]`, §6.1's open-domain
rule applies, as it does for `rewrite`. Everything the step emits is on a
closed range or is a regularity judgement, and neither is open in y. So if y
occurs in the selected integral or in the move's terms, the step is refused.
If it occurs in none of them, nothing emitted mentions y. *(Specified before
the code as `kernel/p1_expected.py` E36–E49, with the owner deciding the
reverse mode, the flip, the selector and §5.3's `sqrt_nonneg`, then built and
reviewed. P1.1 now starts from the sheet's own goal, §11.1.)*

**`int_flip` reverses an integral's limits, as an explicit move**
*(revision 10, consolidation, E51, the owner's decision)*.

```
  int_flip   Int[x = a .. b] f  ≐  Int[x = b .. a] −(f)          for every a, b
```

It is §5.1's definition of a reversed integral composed with pointwise
linearity, the identity `int_subst`'s flip already uses, so the rule table
gains a move and no theorem. It holds whatever the order of a and b, so the
step owes no orientation of its own and has no premise. It selects as
`int_subst` does, without a variable: the one integral in the goal, or the
k-th by `occurrence`, and it is refused `int-flip-no-integral` or
`int-flip-ambiguous` otherwise. Under a `D[y]` it takes `int_subst`'s
open-domain test. The new integral's formers are charged as a new term's
are, on its range, whose order is decided like any other (E56).

**The form was chosen so that `ftc` can run after it.** The owner stated the
move as `Int[x = a .. b] f ≐ −(Int[x = b .. a] f)`. `ftc` acts on a
top-level integral, and on `−(Int …)` it refuses `ftc-no-integral`, so the
owner's aim needed either the negation inside or a position argument for
`ftc`. The negation inside is the same identity, and the owner accepted it.
`Int[x = pi/2 .. 0] 2*x` flips to `Int[x = 0 .. pi/2] −(2*x)`, and `ftc`
closes it to −π²/4. Since E56 the flip is a convenience, because `ftc`
reaches the same value on the reversed goal directly. The limitation it had
under E4 is gone: flipping an oriented symbolic integral whose body owes a
former, such as ∫₀^{π/2} √x to ∫_{π/2}^0 −(√x), is accepted, where `pi/2 ≤ 0`
had refused it.

**The split premises do not over-admit, and the case that shows it is
∫₀¹ x^(−1/2) dx = 2.** Splitting the regularity across [a,b] and (a,b) was
meant to let in an integral whose *antiderivative* misbehaves at an endpoint
while the integrand is fine; the risk was letting in genuinely improper ones
with it. It does not. Here F = 2√x satisfies all three F-side premises — C⁰ on
[0,1], C¹ on (0,1), F′ = f on the interior — and the rule still refuses,
because `f ∈ C⁰([a,b])` fails with f unbounded at 0. `int_improper` remains
required. **The line the corrected rule draws is exactly: F may misbehave at an
endpoint; f may not** — which is why the f-side premise stayed on the closed
interval when the F-side ones moved to the open one. *(Stage 0's second pass,
`STAGE0.md` S30.)*

### 6.5 Differential equations

`ode_verify` — a candidate *x*(*t*) is checked against the equation by `deriv`
then **`field`**, plus initial conditions by `norm_num`. This establishes *a*
solution.

**`field`, not `ring`, and the distinction is the same one §11.2 turns on**
(stage 0, `STAGE0.md` gap 2). Take *m*v̇ = −*b*v with v = v₀exp(−*bt*/*m*):
with the exponential an opaque atom *E*, the residual is
*m*·v₀·(−*b*/*m*)·*E* + *b*·v₀·*E*, which vanishes only if *m*/*m* cancels —
and that is not a ring operation. The step needs `field` and emits `m # 0`,
exactly as §11.2's `close` needed `field` and emitted `sqrt 3 # 0`. Revision 2
made that correction there and revision 5 left this one standing. Any equation
whose coefficients divide reaches it, which is most of them: both unit 00 P1's
linear drag and P4's quadratic drag do. The obligation is emitted anyway —
§5.1's `/` former carries it — so what was wrong was the discharge procedure
named, not the obligation set.

`picard` — stated with its box, because the short form is a false theorem.
On R = [t₀−a, t₀+a] × [x₀−b, x₀+b] with *f* Lipschitz in *x* on R and
|f| ≤ M, there is a unique solution on |t − t₀| ≤ min(a, b/M), **and
uniqueness holds only among solutions whose graph stays in R**. Since §8.3 uses
`picard` only to add uniqueness to a candidate `ode_verify` has already
checked, the hypothesis that actually bites is graph containment, not the
existence interval — Lipschitzness on an unrelated box gives nothing. The
containment obligation is `Γ ⊢ e₁ ≤ e₂ @ D`, an existing judgement form,
discharged by a §10 enclosure on the closed-form candidate. The Lipschitz
obligation is discharged by `lipschitz_from_bounded_deriv` with a
learner-supplied bound, or admitted with a citation.

Three derived lemmas — general theorems, selected because the target corpus
needs them rather than derived from it:

- `quad_t` — *m*ẍ = *F*(*t*): integrate twice.
- `sep_autonomous` — from *m*v̇ = *f*(*v*) with *f* ≠ 0 and continuous on the
  range, conclude *t* = ∫_{v(0)}^{v(t)} *m* d*w*/*f*(*w*). **Derived**, from
  `int_subst` and `ftc` — not a new axiom. (Substitute w = v(s), use
  m·v′ = f(v), then ∫₀ᵗ 1 ds = t. The review tried to break the "not a new
  axiom" claim and could not.)
- `energy_integral` — from *m*ẍ = *F*(*x*), conclude
  d/d*t*(½*m*ẋ² − ∫*F*) = 0, and hence the quadrature.
- `period_integral` — between turning points, carrying *U*′ ≠ 0. That is the
  exactly right convergence condition and not a safety margin: near a turning
  point E − U ≈ −U′(x−x₁), so the integrand goes as (x−x₁)^(−1/2), which is
  integrable iff U′ ≠ 0. The kernel refuses the step without it. *(§13: unit 00
  calls this "the trap of that case", which is where the corpus meets it.)*

### 6.6 Dimensions

Fully decidable and worth having early for that reason — and, since exact rank
over ℚ needs only the exact rationals stage 1 already has, it now lands *in*
stage 1 rather than behind an interval library it does not need (§17).

A dimension is a vector in ℚ^k over (M, L, T, Θ, I, N, J). `dim_add` requires
equal dimensions; `dim_mul` adds them; `dim_div` subtracts them; `dim_pow`
scales them; `dim_sin`, `dim_exp`, `dim_ln` require the argument dimensionless
— which alone catches a large class of errors. (`dim_div` and `dim_pow` are new
here: §12.2's own advertised example uses both and revision 1 listed neither.)

**`buckingham` is split in two, because revision 1's version proved a physical
conclusion from a hypothesis it cannot check.**

- **`buckingham_structure`** takes the declared quantities, computes the rank
  *r* of the dimension matrix **exactly over ℚ**, concludes there are *n* − *r*
  independent groups, verifies each proposed group is dimensionless, and
  verifies independence by the rank of the exponent matrix. This half is
  completely sound and completely complete — it is linear algebra over ℚ.
- **`buckingham`** derives the physical conclusion from that structure *plus a
  named hypothesis in Γ* — `assume closure : T = Φ(m, kappa, a)`, the claim
  that the relation holds among **exactly** the declared quantities and no
  others. That hypothesis is discharged by `cite` or `admit`, so it lands in
  the obligation pane and in the admissions count.

The failure that forces the split is concrete. Run revision 1's rule on the
simple pendulum with T : T, m : M, L : L, g : L·T⁻²: rank 3, n = 4, one group
T√(g/L), verified dimensionless — the exact output shape of §12.2 — and it
certifies "the period is independent of amplitude". That is false: the exact
period is 4√(L/g)·K(sin(θ₀/2)), which grows without bound as θ₀ → π. The
amplitude θ₀ is dimensionless, contributes a zero row, and is invisible to
anyone reading dimensions off the problem. §12.2's spring example comes out
right only because a *linear* κ : M·T⁻² was declared — also a modelling choice.

**The teaching payoff is the strongest argument for doing it this way**: the
omitted-quantity trap is the actual content of dimensional analysis, and §16's
obligation pane is the right place for a learner to meet it. Secondary, and
also now stated: the π theorem yields Φ(π₁) = 0, not π₁ = C; the step between
is the textbook hand-wave and is not part of the theorem being axiomatised.

### 6.7 Series, limits, asymptotics

`geometric`, `geometric_diff`, `telescope` (with an explicit telescoping
witness), `compare`, `ratio`, `root`, `abs_conv`;
`alternating` **with monotone decrease** `a(n+1) ≤ a(n) @ (n ≥ 1)` — without it
the rule is a false theorem, and aₙ = 1/√n for even n, 1/n for odd n is the
counterexample, with alternating terms, aₙ → 0 and partial sums diverging like
√(2N) − ½ln N; the six limit laws, `squeeze`, `lhopital` (with its obligations
written out to §6.3's density), `taylor_lagrange` (remainder with an explicit
*ξ*-bound), `big_O` with explicit constants.

`radius_limsup` is **dropped**: Cauchy–Hadamard's hypothesis is about
limsup |aₙ|^(1/n) and limsup is not in §5.1. A ratio-form radius rule replaces
it; limsup is recorded as an open term-language question in §18 beside the
other endpoint-only constructions.

§6.7 was the one subsection revision 1 wrote without side conditions. The
explicit-constants treatment of `big_O` and `taylor_lagrange` is the part that
holds up unchanged: it dodges o()-arithmetic unsoundness by construction.

### 6.8 Named constants and escapes

A small table of exact values — `sin_zero`, `cos_pi_half`, `ln_one`,
`atan_one ≐ pi/4`, `atan_one_sqrt3`, `atan_odd`, `sin_pi_sixth`,
`cos_pi_fourth`, `ln_e`, `exp_zero`, `exp_one`, `atan_zero` and the rest —
plus `pyth`, the circular addition formulas, `log_mul` (with positivity),
`exp_add`, and `sqrt_sq` (√(u²) ≐ u @ u ≥ 0).

*(Revision 10: entries are stated in one notation, `c @ h`, where some were
sequents (`h ⊢ c`); a pointwise hypothesis on the free variable is exactly a
domain. Schema variables are u, a and the like, never a name a worked example
binds: `sqrt_sq` was stated over t, §11.1's bound variable, which hid the
instantiation §15.2 item 3 says is trusted. Each rule owes its obligation in
its own orientation, so §11.1's is `t ≥ 0`, not `0 ≤ t`.)*

**Three entries §8.9 needs, named here because "the addition formulas" did not
cover them** (stage 0's third pass, `STAGE0.md` gaps 12 and 14):

- `tan_def : tan u ≐ sin u / cos u @ cos u # 0` — `trig_norm` reduces to a
  polynomial in `sin u` and `cos u`, so it must be able to get there from a
  `tan` atom, and no listed entry did that. Note the obligation: this rewrite
  is a field operation and §8.9 is the reason the tactic changes the obligation
  set rather than only the syntax.
- `pyth_h : (cosh u)^2 - (sinh u)^2 ≐ 1` — **not an instance of `pyth`.** The
  sign differs, and a normaliser that reduced hyperbolic atoms with `pyth`
  would be unsound rather than incomplete.
- **the hyperbolic addition formulas**, stated separately from the circular
  ones for the same reason.

**Three more for `abs`, admitted to goals in revision 6** (§5.1):
`abs_nonneg : abs u ≐ u @ u ≥ 0`, `abs_neg : abs u ≐ -u @ u ≤ 0`, and
`abs_pos : abs u > 0 @ u # 0`. The first two are how a `cases` split on the
sign of *u* discharges an `abs` in a goal, which is the route
`∫₋₁¹ |x| dx` takes after `int_split` at 0; the third is what `d_abs`'s
`abs u # 0` obligation closes on, and is a positivity fact about an opaque
atom, so it belongs here by this section's own criterion.

Without these three, §8.9's coverage of `tan` and of hyperbolic atoms is
asserted rather than supported. With the three `abs` entries they bring the count below to **70**.

**Four of those are new, and how they were found is the point** (stage 0,
`STAGE0.md` gap 4). `ln_e`, `exp_zero`, `exp_one` and `atan_zero` were each
needed by one of the first five goals anybody tried to encode, and none was
listed. The reason is structural rather than careless: **no `ftc` step closes
without evaluating F at both endpoints**, so every authored goal terminates in
this table, and a table that ends in "and the rest" is carrying the most
traffic in the document on the least specification. Each entry is one line;
the enumeration is the work.

**The table needs an entry per function *and per direction*, which is the
systematic form of the same finding** (stage 0, `STAGE0.md` gap 8). `asin(1/2)
≐ pi/6` is needed by any goal closing through `asin`, and `sin_pi_sixth` —
sin(π/6) ≐ 1/2 — does not supply it: the two are different theorems, and `asin`
is an opaque atom, so `ring` and `field` cannot get from one to the other. As
it stands the table carries the inverse direction for `atan` and the forward
direction for `sin` and `cos`, which is not a design but the record of which
problems happened to get worked. §5.1 admits six inverse functions — `asin`,
`acos`, `atan`, `asinh`, `acosh`, `atanh` — and **every inverse-trig and
inverse-hyperbolic antiderivative closes through one of these values**, so the
basis for enumeration is *per function, per direction an antiderivative can
close through*, not per value that has come up.

**This is where the owed rule recount starts.** Three dimensions counted the
rule table independently and got ~80, ~100 and ~110, and §6.8 was one of the
three things they disagreed about — whether its table is 20 entries or 45.
Encoding goals enumerates it as a side effect, which makes stage 0 the cheapest
route to a number §14 cannot be priced without — and gap 8's basis is what
makes the enumeration finite and checkable rather than open-ended.

**The enumeration, run on that basis.** The endpoint set is the one the corpus
actually uses — 0, ±1, ½, √2/2, √3/2, 1/√3, √3, π/6, π/4, π/3, π/2, π, e
and the two infinities — and an entry exists where some antiderivative can
close on that value through that function.

```
  sin       0, π/6, π/4, π/3, π/2, π                                      6
  cos       0, π/6, π/4, π/3, π/2, π                                      6
  tan       0, π/6, π/4, π/3                                            4
  asin      0, ½, √2/2, √3/2, 1                                         5
  acos      0, ½, √2/2, √3/2, 1                                         5
  atan      0, 1/√3, 1, √3                                              4
  exp       0, 1                                                        2
  ln        1, e                                                        2
  sqrt      0, 1, and q² ↦ q via sqrt_sq_val                             3
  sinh/cosh/tanh          0                                             3
  asinh/acosh/atanh       0, 1, 0                                       3
  parity    sin_odd, cos_even, tan_odd, atan_odd, tanh_odd, asinh_odd,
            atanh_odd                                                   7
  limits    atan → π/2, exp(-x) → 0, tanh → 1, ln → ∞   (at ±∞)           4
  ─────────────────────────────────────────────────────────────
  values and parity                                                    54
  identities and positivity facts already named above
    (pyth, addition formulas, log_mul, exp_add, sqrt_sq, sqrt_sq_val,
     sqrt_pos, exp_pos, cosh_pos, cos_nonzero_on)                      10
  ─────────────────────────────────────────────────────────────
  tan_def, pyth_h, hyperbolic addition formulas (§8.9)                  3
  abs_nonneg, abs_neg, abs_pos (§5.1)                                   3
  ─────────────────────────────────────────────────────────────
  §6.8 total                                                          70
```

**Seventy, against the recount's "20 entries or 45".** That is the third
thing this section owed and it comes out *above both* estimates, which moves
§14's figure up rather than settling it in the middle: if §6.8 alone is 70,
the ~80 / ~100 / ~110 totals were counting something smaller than the table
they were counting. The number is basis-dependent and says so — change the
endpoint set and it changes — but the basis is now stated, which is what makes
it a count rather than a guess, and it is checkable by anyone who disputes an
endpoint.

**The last row is a boundary, not a value.** `atan → π/2` as x → ∞ is a limit
fact and belongs to §6.7; it is listed here because an `int_improper` close
needs it in exactly the place an ordinary close needs a value, and a reader
looking for "what closes my FTC step" should find it in one table. Which
section owns it is §18 material; which table the learner reaches for is not.

Five entries are new. Each answers an obligation the system's own machinery
emits and none of §5.3's methods can discharge — the recurring shape is a
**positivity fact about an opaque atom** (§6.2), which `ring` cannot know and
`field` cannot derive. They are selected, per the note at the head of §6,
because the corpus raises them; they are stated by the mathematics:

- `sqrt_sq_val : (sqrt a)^2 ≐ a @ a ≥ 0` — without it §11.2's flagship
  obligation is **false as annotated**, since `field` over ℚ(x, s) with *s*
  opaque gives residual (3/2 − s²/2)/(…), zero iff s² = 3. It enters as a
  **fact passed to `field`** (§6.2), never as a rewrite before it.
- `sqrt_pos : sqrt a > 0 @ a > 0` — `close … by ring` in §11.2 divides by the
  atom `sqrt 3`, which is not a ring operation; the step is `by field` with
  `sqrt 3 # 0` discharged here.
- `exp_pos : exp u > 0` — any integrating factor emits `exp u # 0`, and `exp u`
  is an opaque atom: not in Γ, not a range fact, not linear over ℚ, not a sum
  of even powers. Blocks the whole linear first-order route without it.
- `cosh_pos : cosh u > 0` — identically, wherever `ln cosh` appears and carries
  `d_ln`'s u > 0.
- `cos_nonzero_on` — `d_tan`'s side condition, which §8.5's Weierstrass row
  emits on every use.
- `pi_pos : pi > 0` — *revision 9.* π is an opaque atom to `ring` and a free
  variable to Fourier–Motzkin (§5.3), so nothing else knows its sign. By-range
  over [0, π/2] and every `sqrt_sq` at a multiple of π need it. It is cited
  (Rocq's `PI_RGT_0`), and §5.3 adds it to the constraint set whenever `pi`
  occurs, so it rarely has to be named.
- `e_gt_one : e_const > 1` — *revision 9*, for the same reason. By-range
  over [1, e] (stage 0's S3, ∫₁^e ln x / x) cannot be oriented without it, so
  `d_ln`'s `x > 0` is out of reach. Cited, and added by §5.3 whenever `e_const`
  occurs. It is `> 1` rather than `> 0` because 1 is the endpoint the corpus
  pairs it with.
- `sqrt_nonneg : sqrt a ≥ 0 @ a ≥ 0` — *revision 10, int_subst* (E49). `sqrt a`
  is an opaque atom to Fourier–Motzkin, so `1 + sqrt x # 0` had no method,
  and it is the divisor of ∫₀⁴ 1/(1 + √x), the first thing the kill-the-root
  row meets. §5.3's linear method reads it once for each `sqrt` atom in an
  obligation, as it reads `pi_pos`. Its hypothesis owes nothing, since it is
  the former the `sqrt` already paid on entry (§5.3).

**Six entries for a trigonometric substitution** *(revision 10,
consolidation, E54)*. They are what ∫₀¹ √(1−x²) by x = cos θ needs to finish
(§13), and each is read by exactly one route, which is the part worth
stating:
- `pyth : (sin u)^2 + (cos u)^2 ≐ 1` — the identity as the owner states it,
  and the parent of the next. `rewrite` can use it at a subterm that is that
  sum as a tree, turning it into 1, soundly for every real b, and refuses a b
  holding an `Int` or `D` node, which the rewrite would erase (§6.1, E57).
  `field` cannot, since a fact must be a^k ≐ r (§6.2).
- `pyth_cos : (cos u)^2 ≐ 1 − (sin u)^2` — `pyth` solved for (cos u)^2. It
  is a rewrite at (cos b)^2 and a `field` fact in §6.2's shape, and it is the
  form a √(a² − x²) substitution actually uses. Its statement minus `pyth`'s
  is a `ring` identity, so it adds no trust beyond `pyth`.
- `sin_nonneg_on : sin u ≥ 0 @ u ≥ 0, u ≤ pi` and
  `cos_nonneg_on : cos u ≥ 0 @ u ≥ 0, u ≤ pi/2` — the sign facts on the
  half and the quarter period, the second the owner's. **Both are read by
  `cite` only** (§5.3 method 6), whose children certify each instantiated
  hypothesis at the key's domain. They cannot be linear-method labels like
  `pi_pos`, because a Farkas certificate has no children, and u ≥ 0, u ≤ π
  are real conditions on the argument, not its definedness. x = cos θ uses
  the sine fact. x = sin θ would use the cosine one.
- `cos_le_one : cos u ≤ 1` and `cos_ge_neg_one : cos u ≥ −1` — the total
  bounds. The linear method reads each once per `cos` atom in an obligation,
  as it reads `sqrt_nonneg`, with nothing owed, since `cos` is total. They
  are what closes `1 − (cos θ)^2 ≥ 0` as −(cos θ − 1)(cos θ + 1) (§5.3
  method 5).

None is an exact value, since each has a schema variable. E27's
evaluated-answer check (§15.2) counts `pyth` at a tree-equal sum, since a value holding one is
unevaluated, and does not count `pyth_cos`, which trades one atom for
another. The count of 70 above predates these six, as it predates `pi_pos`.

`cite <Lemma>` invokes a named theorem from a curated library file with its
hypotheses checked. **The library file is part of the trusted base** (§15) and
every entry carries a provenance tag in §14's report, like every other rule;
revision 1 left its trust status unstated inside a section headed "stated
exactly". `admit "reason"` records a debt.

### 6.9 Regularity — the Cᵏ closure rules

**New in revision 2, and the largest single omission from revision 1's table.**
§5.2 declares `Γ ⊢ e ∈ Cᵏ(D)` as a kernel judgement; `ftc`, `int_subst` and
`sep_autonomous` all take Cᵏ facts as premises; and §6.1–§6.8 contained **no
rule whose conclusion was a Cᵏ judgement at all**. §7 makes `reg` an untrusted
tactic, so it had nothing to emit, and §5.3's methods are stated for
inequalities and nonvanishing and cannot conclude regularity. The five `by reg`
ticks in revision 1's worked examples were unjustifiable, and §11.1's "Proved.
0 admissions" was not reachable as written.

This is a completeness gap rather than a soundness hole — a `reg` with no rules
yields `Stuck` — but it breaks every worked example in the document.

The closure rules, roughly 25 entries and mostly one-liners:

- **Structural**: const, var, sum, product, difference, `^n` for n ≥ 0,
  composition, quotient-with-nonvanishing, real power with base > 0.
- **Per elementary function, with its own domain condition**: `sqrt` is C⁰ on
  u ≥ 0 but C¹ only on u > 0; `ln` on u > 0; `tan` needing `cos u # 0`;
  `asin`/`acos` C⁰ on |u| ≤ 1 and C¹ on |u| < 1; `atanh` on |u| < 1; `acosh`
  C⁰ on u ≥ 1 and C¹ on u > 1; `sin`, `cos`, `exp`, `sinh`, `cosh`, `tanh`,
  `atan`, `asinh` everywhere; **`abs` is C⁰ everywhere and C¹ where its
  argument is nonzero**, as §5.1 says since revision 6 admitted it to goals.
  (This line said "C⁰ only" and that §5.1 kept `abs` out of goals, and was
  stale until revision 10.) The C⁰ sets above are exactly the domains §5.1's
  partial formers owe.
- **A hypothesis form for declared function symbols**, so `v ∈ C¹` can enter
  from Γ as §12.1 needs.

Two things about C¹ worth stating because they are not recoverable from
elsewhere: it does **not** follow from §6.3's rules even in principle, since
those are pointwise and pointwise differentiability does not give a continuous
derivative; and C⁰ for `abs` is not reachable from derivative rules at all.

**The alternative of making `reg` a reflective procedure inside the trusted
base is rejected.** It would move ~25 machine-checkable lemmas out of §14's
report and add unverified code to §15's list — exactly the wrong direction for
a project whose verification is deferred (§15.4).

---

## 7. Tactics: the untrusted layer

Everything above the kernel produces *candidate* kernel steps and is checked:
`deriv`, `reg` (regularity by syntax walk over §6.9), `domain` (obligation
discharge), `subst`, `parts`, `classify`, `buckingham`, `trig_norm` (§8.9). A buggy tactic cannot
produce an unsound proof, only a rejected one. Tactics are where all future
convenience work goes, at zero cost to the soundness argument.

**That claim is true of `domain` because of §5.3's certificates, not by
assertion.** Revision 1 asserted it and was wrong: an obligation discharge is
*terminal* — when `domain` reports discharged, the kernel ticks and the proof
closes, with no downstream step re-deriving it — so a bug in Fourier–Motzkin or
in the sign heuristic converted directly into a false `Proved`. Having both
emit witnesses the kernel re-checks is what moves them out of the trusted base
and makes this paragraph a fact rather than a hope.

**The enforcement mechanism is named in §15.3.** "LCF discipline" in Milner's
sense is a *type*, enforced by a compiler; JavaScript has no equivalent by
default, and a discipline nobody enforces is an adjective.

---

## 8. The assistance layer

Everything in this section is available at all times, in every mode, without
ceremony or warning. §2 settled whether it should be; this is what it is.

### 8.1 One problem, three ways in v1

Readiness P1(1), ∫₀^{π²/4} sin √*x* d*x*.

**assisted — the loop, and the mode this tool is for.** The interesting part is
not the run that works. It is the one that does not.

```
  ⊢ Int[x = 0 .. pi^2/4] sin(sqrt x) ≐ ?A

  palette   subst · parts · split · ftc · table · rewrite‹sqrt_sq, …›
  matches   nothing in the antiderivative card

  > ?                                                            (rung 1)
    This integrand wants a substitution: there is a root around the
    argument of a transcendental, and nothing in the table matches.

  > step subst (x := pi^2/4 * sin t) over t in [0, pi/2]         ← your guess
    ✓ legal.
      ⊢ Int[t = 0 .. pi/2] sin(sqrt(pi^2/4 * sin t)) * (pi^2/4 * cos t)
          ≐  ?A
    ⚠ no progress: the root is still there, and the integrand now
      matches nothing.  2 atoms before, 3 after.

  > ↑                                                            retract
  > ??                                                           (rung 2)
    Technique: kill the root by making it the variable.  sqrt(u) → u = t².

  > step subst (x := t^2) over t in [0, pi/2]
    ✓  obl  t^2 ∈ C¹([0, pi/2])                     reg
       obl  sin(sqrt(t^2)) ∈ C⁰([0, pi/2])          reg → t² ≥ 0 by sign
       obl  0^2 ≐ 0,  (pi/2)^2 ≐ pi^2/4             ring, in the step
    ✓ progress: root removable, `sqrt_sq` now matches at position 1.
      probe: value preserved, 12 digits agree.                   ~
```

Four things in that exchange are the design:

The wrong guess **cost one keystroke**, and it was *legal* — the kernel had no
objection to it, and a tool that only reported legality would have said
nothing. The progress signal (§8.5) is what turned a legal dead end into
feedback. The ladder gave a nudge before it gave the answer. And the
speculative probe (§8.6) confirmed the good substitution numerically before any
effort went into the four steps after it.

*(Revision 10, int_subst: earlier revisions showed the guess as `x := sin t`
and marked it legal. It is not legal. Its upper end maps to
sin(π/2) = 1, not π²/4, and no t reaches π²/4, since sin ≤ 1. The kernel
refuses it at the step with `int-subst-endpoint-mismatch` and the residual
`1 − pi^2/4`. That is feedback too, but it comes from the kernel and not from
the progress signal. A legal dead end has to map both ends, so the guess shown
is scaled: its ends map by `sin_zero` and `sin_pi_half`. §8.6 keeps the
unscaled guess as its probe example. The good substitution's endpoint line is
two equations, both decided in the step (§6.4).)*

**by hand** — you supply every move; the tool does the algebra. This is the
same script with the palette and the ladder ignored.

```
  step subst (x := t^2) over t in [0, pi/2]      ← your substitution
  step rewrite sqrt_sq                            ← your identity
  step pull_const 2
  step parts  u := t,  v := -cos t                ← your split
  step table  cos
  step close ?A := 2                              by ring
```

You differentiated nothing, expanded nothing, and could not have dropped the
factor of 2 — it was computed. §8.4 says exactly what each move asks of you.

**check** — you worked it on paper and want a verdict.

```
  > check 2
    proof:  F = 2*sin t - 2*t*cos t verified by ftc after x := t^2
            18 rule applications, 0 admissions                   (0.6 s)
  ✓ Proved.   Int[x = 0 .. pi^2/4] sin(sqrt x) ≐ 2
```

In v1 `check` proves an *exact* answer or gets stuck; it cannot reject a
numeric one, because that needs the certified enclosure of §8.6 and §10, which
is the next stage.

**auto and solve are not in v1** (§2). When they arrive they end in the same
object — a proof the kernel checked — and the derivation `solve` prints is the
same derivation you would have written. That is the argument for having them
eventually and it is not an argument for having them first.

### 8.2 The integrator

> **Not in v1.** This section describes stage 3. §1's argument against shipping
> `solve` first applies to the integrator for the same reason and with only
> slightly less force: handing over the antiderivative for the *current*
> integrand is a smaller short-circuit than handing over the whole derivation,
> but for a problem like readiness P1(2) — where the integral *is* a partial
> fraction — it is the same act. What v1 ships instead is the vocabulary
> (§8.5's antiderivative card and recognizer) and the `table` move, which tell
> you that you are looking at a standard form without telling you the answer.
>
> **What v1 does build is the interface**, per §2's preparations: one entry
> point, `integrate : goal -> candidate option`, with the failure taxonomy
> below. A stopgap proposer behind that interface is then a flag rather than a
> project — and §16's server changes which one. Revision 3 named Algebrite, a
> CDN script tag measured at 12/16 on this course's integrands, because the
> tool had to run in a browser. With a server the obvious stopgap is **SymPy,
> shelled out to**, which §15.5 measures at **16/16** on the same sample with a
> median of 30 ms, and whose `1/(1+x**3)` output *is* §11.2's answer including
> the Rioboo real-arctan conversion. Under this architecture a wrong answer
> from it costs a rejected step. **Wired, off by default, one line to enable
> when the gate in §17 says the exploration loop has been given a fair run** —
> and note that SymPy was already going to be a build-time dependency as the
> authoring oracle, so this adds no new one.

The tool integrates. This costs nothing in soundness, for the reason §6.4
gives: whatever the integrator returns is checked by differentiating it. A
buggy integrator produces a **rejected step**, never a wrong answer.

So it is untrusted code, outside the trusted base of §15, and it can be as
heuristic as it likes:

| Stage | Method | Status |
|---|---|---|
| Table and linearity | the standard forms | trivial |
| Derivative patterns | *f*′·*g*(*f*) → *G*(*f*); *f*′/*f* → ln\|*f*\| (see §8.5) | trivial |
| Substitution heuristics | the shape table of §8.5, executed rather than suggested | heuristic |
| By parts | LIATE ordering, with cycle detection for ∫e^x sin x | heuristic |
| **Rational functions** | squarefree decomposition, Hermite reduction, Lazard–Rioboo–Trager with Rioboo's real-arctan conversion | **complete for denominators that factor over ℚ into linear and irreducible quadratic factors** |
| Elementary functions in general | the Risch algorithm | a large lift; probably never |

**The fifth row's completeness claim is now bounded, and the bound is the
output language rather than the algorithm.** Rothstein–Trager expresses the
logarithmic part as a sum over the roots of a resultant — algebraic numbers in
general — and §5.1 has rational literals, π, e and `sqrt` with no RootOf
constructor. For 1/(x⁵ − x − 1) the resultant 2869z⁵ + 160z³ − 80z² + 15z − 1
is irreducible with Galois group S₅, so its roots have no radical expression at
all: **this is not fixable by adding radicals, and it holds at any budget.**
Linear and irreducible-quadratic denominators are every partial-fraction
problem in this course — readiness P1(2) and P5, unit 00's quadratic drag — and
the tool will do those every time, exactly, and prove it.

Two further corrections to the row. Plain Rothstein–Trager emits **complex**
logarithms; producing §11.2's displayed answer
−(1/6)ln(x²−x+1) + (1/√3)atan((2x−1)/√3) requires Lazard–Rioboo–Trager *and*
Rioboo's complex-log-to-real-arctan conversion — which is where the √3 and the
`atan` come from at all, and which is the integrator's most branch-cut-sensitive
code. (SymPy 1.14 returns exactly that form, so the step is known, implemented
and nameable.) And that tier **reuses stage 1's factoriser and
partial-fraction solver** (§8.4) rather than re-implementing them.

When the integrator fails it says *which kind* of failure, because the
difference matters — and there are three kinds, not two:

```
  ✗ no elementary antiderivative is known for this form.
    exp(-x^2) matches my table of forms with no elementary antiderivative
    (Liouville). That table is a citation, not a proof here.
    available instead:  quad_verified  — a proved numeric enclosure
                        erf            — as a named special function
```
```
  ✗ not found.
    My heuristics did not find an antiderivative. One may well exist.
    available instead:  by-hand mode, the move palette, or quad_verified
```
```
  ✗ found F, could not verify it.
    D[x] F − f is not zero in Q(atoms); the residual needs an identity I
    did not locate.  residual: (1 + cos^2 θ - sin^2 θ)/2 - cos^2 θ
    available instead:  rewrite pyth, then retry;  or auto
```

The first message changed in revision 2 and the change matters. Revision 1
reported non-existence as a theorem. Deciding non-elementarity is Risch, which
this table rates "probably never"; what the tool will have is a hard-coded
list, and a pattern-matched list misfires — ∫(1 + 2x²)e^{x²} dx = x e^{x²} *is*
elementary, and any rule keyed on "contains e^{x²}" reports a falsehood. This
is the one place the tool could state a mathematical untruth without a `Proved`
label attached, which §2's "it never lies" does not otherwise distinguish. The
table entries carry `cite` provenance and the message says so.

The third message is new and is the one §6.4 predicts. Without it, a correct
answer that needs an identity reads as an integrator failure.

### 8.3 The ODE solver

> **Not in v1** (stage 4). `ode_verify`, `sep_autonomous` and the rest of §6.5
> *are* reachable in v1 — they need no numerics — so unit 00's quadrature cases
> can be worked in the loop with the learner supplying the candidate. What is
> deferred is the pattern-driven **proposer** below, for §8.2's reason.

Same architecture, same reasoning: a pattern-driven solver (separable, linear
first-order, exact, constant-coefficient linear, Euler, reduction of order,
the three quadrature cases of unit 00) proposes a candidate, and `ode_verify`
checks it by differentiating and ring-normalising. Untrusted proposer, checked
result.

Uniqueness is the part that does not come free: `ode_verify` establishes that
your *x*(*t*) solves the equation, not that it is the only thing that does. For
*the* solution you still need `picard`, its Lipschitz obligation and its graph
containment (§6.5). That is a mathematical fact about ODEs, not a restriction
the tool imposes — and §17's bank now carries a uniqueness claim asserted past
the blow-up time (ẋ = x², x(0) = 1, on [0,2]) to make sure the containment
obligation is doing its job.

### 8.4 What each move asks of you, when you drive

Every row is optional — the integrator will do the whole column — and this is
what it looks like when you would rather do it yourself.

| Move | You supply | The tool supplies |
|---|---|---|
| substitution, forward | *x* := φ(*t*) and the new range | computes φ′, rewrites, decides both endpoint equations, emits φ ∈ C¹ and `f(φ(t)) ∈ C⁰([a,b])` |
| substitution, reverse | *u* := *g*(*x*), the new limits and the new integrand *f*(*u*) | computes *g*′, checks integrand ≐ *f*(*g*(*x*))·*g*′(*x*), decides both endpoint equations, emits *g* ∈ C¹ and `f(g(x)) ∈ C⁰` on the old range |
| by parts | *u* and *v* | computes *u*′, checks *v*′, assembles both halves |
| partial fractions | the ansatz, or nothing | solves for the coefficients exactly; verifies by recombining |
| completing the square | nothing | does it; `ring` verifies |
| factoring | the field (ℚ or ℝ) | proposes the factorisation; `ring` verifies |
| trig identity | which identity, at which position | rewrites, discharges the domain condition |
| Taylor to order *n* | *n* | every coefficient, by iterated `deriv` |
| limits of integration | nothing | propagates them through every substitution, including reversed ones (§5.1) |

The pattern in rows 3–5 is why none of this threatens §15. Factoring 1 + *x*⁴
over ℝ, or solving an ansatz for *A*, *B*, *C*, is **search**, and its result is
checked by one `ring` or `field` step. Search whose output is cheap to verify is
free. That sentence is the whole design, and §8.2 is it applied to the largest
search of all.

### 8.5 The palette, the recognizer, and the progress signal

**This section is the product.** §1 says the gap is knowing which move to make;
everything here is the vocabulary for that, indexed so a machine can offer it.
Revision 1 filed this under stage 1b as a convenience. It is stage 1, and it is
what the rest of the tool exists to serve.

Four layers, cheapest first.

**The palette** shows which rules syntactically match the current goal —
Rocq's `Search`, always visible, always free. It answers *what is even legal
here*, which for a learner without the trained eye is not a trivial question.

**The standard antiderivative card** is the twenty forms from the inside cover
of any calculus text, live: the ones that match the current integrand are
highlighted. This is rung-0 vocabulary rather than an answer machine — it tells
you that what you are looking at *is* a standard form, which is exactly the
recognition being learned.

**The recognizer** keys on the shape of the integrand and names the technique,
with what each move will demand in return:

```
  ∫ R(sin θ, cos θ) dθ           →  Weierstrass, t = tan(θ/2)   [emits cos θ # 0]
  √(a² − x²)                     →  x = a sin θ                 [close needs pyth]
  √(x² + a²)                     →  x = a sinh u                [inverse: asinh]
  √(x² − a²)                     →  x = a cosh u                [x ≥ a; inverse: acosh]
  √(u) inside f(·)               →  u = t², kill the root       [emits u ≥ 0]
  f′(x)·g(f(x))                  →  u = f(x)                    [reverse int_subst]
  f′(x)/f(x)                     →  ln|f|                       [emits f # 0]
  tan u,  tanh u                 →  −ln|cos u|,  ln cosh u      [f′/f after tan_def]
  P(x)·e^{ax}, P(x)·sin ax       →  parts, reducing deg P each time
  e^{ax}·sin bx, e^{ax}·cos bx   →  parts twice, solve for the integral (the cycle)
  (linear)/(irreducible quadratic) → c·f′/f plus an arctan
  rational function              →  factor, then partial fractions
```

**Row seven is ln|f| with f # 0 (revision 8).** Revisions 1–7 stated it as
ln f with f > 0, because the only rule that could check it, `d_ln`, requires
u > 0, and nothing in §6 differentiated `abs`. Revision 6 added `d_abs`, which
removed the reason, and the recognizer spike found the row still stated the
old way. `D[x] ln(abs f)` now checks through `d_ln`, `d_abs` and `abs_pos`,
and the `cases` split on f's sign is no longer needed.

**Revision 8 changed five rows, and all five come from the recognizer spike**
(`spike/recognizer/`, §17):
- `√(x² − a²)` and `tan u, tanh u` fill two misses in unit 00.
- `(linear)/(irreducible quadratic)` is the step readiness P1 and P5 both
  take after partial fractions, and "partial fractions" named it wrongly.
- `e^{ax}·sin bx` is the cycle case the progress signal below says the parts
  row "knows about". The `P(x)·e^{ax}` pattern never matched it, because there
  is no polynomial factor.
- **`f′(x)·g(f(x))` is the chain rule**, the commonest substitution there is,
  and §8.5 had no row for it: `x·e^{x²}` matched nothing, and `sin x·cos² x`
  was offered Weierstrass. It is the one row that is a search rather than a
  pattern: is some factor a constant multiple of the derivative of a subterm of
  another factor? `field`'s constant-ratio test (D[x] of the ratio ≐ 0) is
  what answers it. *(Revision 10, int_subst: the move the row names is
  `int_subst`'s reverse mode, u := f(x). The learner writes g(u), and the
  kernel checks the integrand against g(f(x))·f′(x) (§6.4). Until then the
  rule table had only the forward move. Its emulation of u = x² as x := √u is
  refused, correctly, because √ is not C¹ at 0, so the commonest substitution
  there is had no substitution move at all, and `ftc` closed those integrals
  directly.)*

**The rows match the normalised goal, not the written one** (revision 8).
Three of the spike's six held-out misses were rows reading the raw term:
- `sin t·(−sin t) − cos t·cos t` is −1, and was offered Weierstrass.
- `1/(u·ln(1/u))` is f′/f with f = ln(1/u), but the row took the whole
  denominator as f.
- `√(2ε + 2GM/r − h²/r²)` is a quadratic under the root once r² is cleared.

So the recognizer runs on the goal after `ring`/`field` normalisation and
§8.9's `trig_norm`, and f′/f tries each factor of a denominator. This is
untrusted tier-2 work, so normalising here emits nothing. §8.9's rule that
`trig_norm` is a fallback, not a preprocessor, is about the kernel's
discharge, where it would add obligations, and it still stands there.

**Two further techniques are recorded rather than given rows**, because each
appeared once and a row fitted to one example is what the spike showed does
not generalise. They are differentiating a parameter of ∫ 1/D to reach
∫ 1/D² (readiness P2), and the Beta substitution for √(1 − xⁿ) with symbolic
n (unit 00 P7).

The recognizer is the integration-techniques chapter, indexed by syntax. In
`assisted` mode it proposes; when `solve` eventually exists (§2) it is the same
table, executed instead of suggested.

#### The progress signal

**New in revision 2, and the component §1's framing most depends on.** The
kernel tells you whether a move was *legal*. Trial and error needs to know
whether it was *useful*, and those are different questions — the wrong
substitution in §8.1 was perfectly legal and left the learner worse off with no
comment from the system.

After every accepted move, the tool re-runs the layers above on the new goal
and reports what changed:

| Signal | Meaning |
|---|---|
| **finishable** | the integrand is rational, or matches the antiderivative card — a named move closes it from here |
| **rule now matches** | a rewrite applies at a position where it did not before (`sqrt_sq` at position 1) |
| **technique named** | the recognizer has a row for the new shape, and did not before |
| **no progress** | nothing above fired, and the goal is not obviously simpler |
| **worse** | strictly more distinct atoms, or deeper nesting, with nothing new matching |

Cheap to compute — it is the palette, the card and the recognizer run once more
over a term — and nearly free once those exist.

**Two honest limits, because a progress signal that is believed uncritically is
worse than none.** It is a *heuristic and never a judgement about the proof*:
nothing here can enter the kernel, and a move the signal calls `worse` may be
the right one. The canonical counterexample is already in this document:
**parts with a cycle** (∫e^x sin x, §8.2) deliberately goes around twice and
gets worse each time before the two halves are solved against each other. The
recognizer's `e^{ax}·sin bx` row knows about that case and suppresses the
warning. *(Revisions 3–7 credited the `P(x)·e^{ax}` row with this; its pattern
never matched, and revision 8 gave the cycle its own row.)* Nothing guarantees
the list of such cases is complete. Second, "more
atoms" is a crude proxy, and the signal says which measure fired rather than
pronouncing a verdict.

#### The ladder, implemented

§2's hint rungs are these four layers exposed one at a time: rung 1 is the
recognizer's *category* without its row, rung 2 is the row, rung 3 is the row
with its parameters instantiated against the current goal, rung 4 applies it.
No separate machinery, which is why the ladder is affordable in v1 while
`solve` is not.

### 8.6 Two probes: navigation now, evidence later

Numeric evaluation serves two different jobs in this design, they have opposite
soundness requirements, and revision 1 conflated them. They are separated here
because the cheap one belongs in v1 and the rigorous one does not.

#### The speculative probe — v1, navigation, never evidence

Before committing five steps to a substitution, check numerically that the
transformed integral still has the same value.

```
  > step subst (x := t^2) over t in [0, pi/2]
    ~ probe: 2.0000000000 vs 2.0000000000 — value preserved, 12 digits agree
```
```
  > step subst (x := sin t) over t in [0, pi/2]
    ~ probe: 2.0000000000 vs 0.6023373579 — VALUE CHANGED.
      Check the endpoints and the dx factor.
```

This is the single largest reduction in the cost of a wrong guess in the whole
document, which is why it is in v1 despite needing no kernel support at all:
a mistaken substitution is caught in milliseconds instead of four steps later
when `ftc` refuses to close.

*(Revision 10, int_subst: the second probe printed 1.3012779, which is not the
value of that move. With the range shown, the transformed integral is
∫₀^{π/2} sin(√(sin t))·cos t dt = ∫₀¹ sin √x dx = 2 sin 1 − 2 cos 1 ≈ 0.6023,
as mpmath and SymPy both give. The kernel now refuses this move
itself, because its upper end does not map (§8.1). A substitution the kernel
accepts cannot change the value, since φ′ is computed and both endpoint
equations are decided in the step (§6.4). So for `int_subst` the probe's catch
repeats a refusal and adds the size of the error. A changed value the kernel
does not refuse can now come only through an admission: a regularity premise,
or an obligation tagged `none` that is false, such as a pole the counter-point
search misses (§5.4).)*

**It is explicitly not evidence, and the UI marks it `~` rather than `✓`.**
The v1 probe is ordinary floating-point adaptive quadrature. It can be wrong in
both directions — a near-singular integrand can disagree when the substitution
was right, and two genuinely different values can agree to twelve digits. It
never enters the kernel, never discharges an obligation, and never appears in
the obligation pane. §10's rule stands without exception: **`math.h`/double
results are never admissible as in-tool evidence.** A navigation aid is not
evidence, and the two are kept visibly apart precisely so the distinction
survives contact with a tired user at midnight.

#### The certified probe — stage 2, evidence, can reject

Rigorous quadrature needs no antiderivative. Interval or Taylor-model
quadrature — with derivative bounds obtained by composing §6.3's symbolic
`deriv` with §10's interval evaluator, and an explicit tail bound for an
improper integral — produces a **verified enclosure** of a definite integral
directly from the integrand. Subdivision grades toward endpoints where the
derivative bounds fail; `sin √x` at 0 is the example already on this page.

```
  > probe pi/4
    your answer            ≈ 0.78540
    the integral is in       [0.8356487, 0.8356489]      ✗ these are disjoint
```

That is **a verified enclosure disjoint from your answer**, in about a tenth of
a second, before any search for a closed form. It is what makes `check` mode
able to reject rather than merely fail to prove, and it is the reason stage 2
is the next stage rather than a later one.

Revision 1 called this "a *proof* that your answer is wrong". It is not, and
the difference is not pedantry: the proposition "your answer is wrong" is a
negation, and §5.2 has no negation (§13). The enclosure is rigorous and the
rejection is decisive; the kernel simply has no form in which to record it.

It is **advisory** by default, which keeps the quadrature engine out of the
trusted base; a separate `quad_verified` rule promotes it to a proof step for
the problems whose answer genuinely is a number, or where no elementary
antiderivative exists. **When `quad_verified` is used, quadrature is in the
trusted base for that proof**, and §15 says so in its list rather than only in
its prose.

### 8.7 Feedback: three kinds of stuck, and the residual

Under §1's framing this is not error reporting, it is the other half of the
loop. A move that fails must say *what to do next*, and there are three
different answers.

**1. Nothing matches.** No rule in the palette applies to this goal's shape and
the recognizer has no row for it. The next action is a different move, and the
ladder is the way to find one.

```
  ✗ stuck: no rule matches  Int[t = ...] sin(sqrt(sin t)) * cos t
    The recognizer has no row for a root inside a transcendental
    inside another transcendental.  ?  for a nudge.
```

**2. A rule matches but an obligation will not discharge.** The move is right
and something is missing from the domain. The next action is a fact, not a
different move — and for this learner that is the familiar situation.

```
  ✗ stuck: rewrite sqrt_sq applies at position 1, but
    obl  0 ≤ t  @ [-pi/2, pi/2]    NOT discharged
    by hypothesis: no.   by range: gives -pi/2 ≤ t ≤ pi/2.   by sign: no.
    Either split the range at 0 with `cases`, or this rewrite is wrong here.
```

That second sentence is the design working: over a range containing negatives
√(t²) really is not *t*, and the tool has just said so rather than making the
rewrite the way a CAS would.

**3. The step is legal and the algebra does not close.** Here the useful output
is not two normal forms to compare by eye. Both sides are already sparse
polynomials in the atoms, so subtract them:

```
  step ftc  F := sin t - t*cos t
  ✗ D[t] F ≐ 2*t*sin t   fails.

    D[t] F  −  integrand  =  −1·(t·sin t)

    Your F′ is short by exactly one copy of  t·sin t.
    Check the constant in F:  F := 2*(sin t − t*cos t) would close this.
```

Where the residual is not a clean monomial, a numeric sample over the range
shows where the two diverge.

**One case must be recognised before suggesting an arithmetic slip.** On a
correct trig-substitution answer the residual is not zero and not a mistake —
it is a known identity's left-hand side, and reporting "check the constant in
F" would diagnose a right answer as an error. The residual is matched against
§6.8's identity table first, and where it matches the message names the
identity. The same applies to surds: a learner who writes π√3/9 — SymPy's
normal form and most textbooks' — is compared against π/(3√3), and with
`sqrt 3` opaque the difference is (3π − s²π)/(9s) ≠ 0. Every surd answer on
this syllabus is affected, and `sqrt_sq_val`, passed to `field` as a fact
(§6.2), is what closes it.

For long chains this is the highest-value feature in the application after the
recognizer, and it is a few dozen lines on top of machinery §6.2 already needs.

### 8.8 Generated practice, if you want it

The kernel differentiates, so it can **generate** integration problems with
known answers: draw *F* from a grammar, differentiate it, pose ∫ D[*x*]*F*.

Two honest qualifications revision 1 skipped. Posing ∫ D[x]F over [a,b] is
well-posed only if F ∈ C¹([a,b]) and D[x]F ∈ C⁰([a,b]) — the two obligations
`ftc` emits — and a grammar producing `ln`, `1/·`, `sqrt` or `tan` produces
poles and branch points inside randomly chosen ranges. **The generator runs the
kernel's own `reg` and range checks and discards failures**, so "unlimited"
means unlimited within the grammar's dischargeable range. And "difficulty set
by the grammar" is unsupported: the posed integrand is D[x]F in whatever normal
form the generator prints, and the chain rule is usually readable straight off
it, so the generated corpus is systematically unrepresentative of the course's
integrals. **It is not a substitute for authored goals** (§17).

Checking is instant and rigorous, and §8.7 names each error rather than just
marking it — and under §1's framing a generator that can pose *one technique at
a time*, graded by the recognizer's own rows, is a more interesting object than
revision 1 took it for. The machinery is a by-product of the kernel either way, so it costs
almost nothing to expose.

### 8.9 The trig normaliser

**New in this revision, and it exists because §6.4's incompleteness turned out
to be wider than §6.4 said** (stage 0, `STAGE0.md` gap 9). `∫₀^{π/2} cos²x dx`
closes on F = x/2 + sin(2x)/4, and to `field` the atoms `cos x`, `sin 2x` and
`cos 2x` are unrelated symbols — residual ½ + C₂/2 − C₁², not zero. No
substitution is involved, so the manual-rewrite consequence §6.4 draws for
trig *substitutions* was reaching the most ordinary integrals in the corpus.

**What it is.** A canonicaliser for trigonometric polynomials in a single base
angle. Given a goal whose trig and hyperbolic atoms have arguments that are
rational multiples of a common base *u*, it rewrites everything to a polynomial
in `sin u` and `cos u` via §6.8's addition formulas, then reduces with `pyth`
to the canonical form **at most degree one in `sin u`**. Then it hands off to
`field`. The hyperbolic atoms go the same way and **need their own table
entries to do it**: `cosh² u − sinh² u ≐ 1` is a different identity from `pyth`,
not an instance of it, and §6.8's "addition formulas" have to name the
hyperbolic ones explicitly or this sentence is unsupported (stage 0's third
pass, `STAGE0.md` gap 14).

**What makes it a normalisation and not a search — which is the whole reason it
can land before `auto`.** The target form is canonical: two trig polynomials in
the same base angle are equal iff their normal forms are identical, so there is
nothing to search over and no backtracking. `auto` (stage 3) searches for
*which rule to apply*; this applies a fixed reduction to a fixed target. They
are different kinds of component and the scheduling argument in §6.4 that keeps
`auto` at stage 3 does not reach this.

**It is untrusted, like every other tactic (§7).** It emits `rewrite` steps
citing §6.8 entries that are already kernel rules; the kernel checks each one.
A bug costs a rejected step, never a false `Proved`, and **nothing enters the
trusted base** — the same discipline as §8.2's factoriser and §5.3's method 5.

**It runs only after `field` has failed, and that is a correctness requirement
rather than an optimisation** (stage 0's third pass, `STAGE0.md` gap 13).
∫₀^{π/4} tan²x dx closes on F = tan x − x with **no normalisation at all**:
`d_tan` yields `1 + (tan x)^2`, so the residual is a ring identity in the single
atom `tan x`. Run unconditionally, `trig_norm` would rewrite `tan x` to
`sin x / cos x`, turn a free `ring` close into a `field` close, and **emit a
`cos x # 0` obligation that the original proof never needed**. A normaliser
that can only help is a preprocessing step; this one can cost something, so it
is a fallback. Try `field`; on failure, normalise and try again.

**It changes the obligation set, not only the syntax.** The `tan`→`sin/cos`
rewrite is a field operation and carries `cos u # 0` with it (§5.1). That is
sound — obligations are checked like any other — but it means the tactic's
output is not purely a rewritten goal, and the obligation pane will show
entries the learner did not cause. §8.7 should name their origin when it does.

**Where it runs, and where it deliberately does not.** It runs inside the
discharge of `D[x] F ≐ f`, not on the learner's working goal. That boundary is
load-bearing: §1 says the gap is *which technique to reach for*, not
sign-and-factor bookkeeping, and expanding `cos 2x` into `2(cos x)² − 1` is
bookkeeping. Normalising it inside the residual check removes an obstacle the
learner gains nothing from clearing; normalising it in the visible goal would
be doing the exercise for them, and §8.5's recognizer would lose the cue that a
double-angle identity was what the shape called for. The learner still chooses
the technique; they stop paying for the expansion.

**What it buys, stated exactly.** `D[x] F ≐ f` becomes **decidable whenever the
residual is a trig polynomial in a single base angle over ℚ(atoms)** — which
covers both the ordinary trig integrals above *and* §6.4's first documented
escape, the post-substitution `pyth` case, since reduction to canonical form
subsumes it. Incommensurate angles (`sin x` and `sin(pi*x)` together) stay
outside, as do §6.4's algebraic constants — `(√3)² ≐ 3` is `sqrt_sq_val`, a
different kind of fact about a different kind of atom.

**Cost.** One assistance-layer component, in stage 1 (§17).
Nothing to reuse: the reduction has to emit *these* kernel steps against
*this* rule table.

---

## 9. Answer schemas: making "= ?" mean something

Most problems ask for a value that is not given, so the goal must contain a
metavariable:

```
  goal  Int[x = 0 .. 1] 1/(1 + x^3)  ≐  ?A
```

Unrestricted, this is **vacuous** — `?A := Int[x=0..1] 1/(1+x^3)` closes it by
`refl`, and the goal asserts nothing. This is a *specification* problem, not a
pedagogical one: without some constraint the theorem has no content, and that
would be true even if nobody were learning anything. That diagnosis is right
and survives review; the fix below is what changed.

### What `?A` and `close` are

`?A` is a goal-level metavariable (§5.1): a goal state may carry one, a kernel
theorem never does, and `?A` may not mention a variable bound in the goal —
that scope check lives inside §15 item 1.

`close ?A := e` is a **structural rule** (§6.1). It instantiates the
metavariable with *e*, checks *e* against the answer schema, and discharges the
resulting goal. Instantiation is sound for the ordinary reason: proving
`G[?A := e]` proves an instance, and the instance is the theorem reported.

**The schema checker is not in the trusted base.** A permissive schema yields a
weaker true theorem, not a false `Proved` — so it is a *statement-strength*
component, not a soundness one. The instantiation itself is kernel work; the
schema check is a filter on what the goal is worth.

### The `closed` schema, as a whitelist

```
  answer schema  closed
```

Revision 1 defined `closed` as "?A contains no Int, D, Sum or lim" — a node
**blacklist** — and then read it as asserting *this integral has an elementary
closed form, and it is this one*. It does not. A declared function symbol
(§5.1) is opaque and contains no excluded node, and §8.2 offers `erf` "as a
named special function" as this design's own fallback, so
`?A := sqrt(pi)/2 * erf(1)` passes while asserting considerably less than
elementarity. Readiness P7 is the case that hits it first.

So `closed` is stated positively, as a whitelist of the elementary term formers
§5.1 already enumerates — rational literals, π, e, the ring and field
operations, integer and real powers, and the named elementary functions — with
**declared symbols excluded**. A problem that legitimately wants a special
function writes:

```
  answer schema  closed + erf
```

so the weakening is visible in the goal rather than silent. The check runs
**before** `cite`d definitions are unfolded, on the raw instantiation; the
whitelist form makes that the obvious reading.

An earlier draft had per-problem whitelists like `Q[pi, ln 2, sqrt 3, atan]`,
justified on the grounds that they leak no more than the sheet's own first hint
rung. True, but unnecessary — the closed-form schema leaks nothing at all, so
the whitelists are gone except where a problem genuinely asks for a *particular
form* ("give the answer as a single logarithm"), which is a real specification
and belongs in the goal. (Revision 1 said that and then used the discarded
whitelists in both worked examples; §11 is corrected.)

**`closed` also means fully evaluated (E27, owner's decision 2026-09-24).**
The whitelist on its own accepted an unevaluated F(b) − F(a): after `ftc`,
S2 closed as `(exp 1 − exp 0)/2` and S3 as `(ln e_const)^2/2 − (ln 1)^2/2`,
with no §6.8 entry ever used. That made `close` vacuous and §6.8's "every
authored goal terminates in this table" unenforced. A closed value must now
be **fully evaluated**. This is a checkable property, not a canonical form,
because equality of closed constants is undecidable in general, and both of
P1.2's forms stay accepted. It has two clauses:
- **(a) No subterm can still be evaluated by a §6.8 entry in force.** The
  match is the one `rewrite` uses, with ring-normalised arguments, so
  `exp(0^2)` counts. Each schema entry has a stated reading:
  - `sqrt_sq`: a closed perfect square;
  - `atan_odd`: every coefficient negative;
  - `sqrt_sq_val`: a power with |n| ≥ 2.
- **(b) No unreduced literal arithmetic.** The tests are local and
  order-independent: a literal term not in lowest terms, a zero or combinable
  summand (counted by monomials), a unit, zero or like factor, and a trivial
  or nested power.

A value that fails is refused `close-not-evaluated`. The refusal names the
move still available, for example "`exp 1` can still be evaluated
(`exp_one`)". The check is **untrusted**: it sits beside the whitelist in
`schema.py` and runs **last** in `close`, so every trusted refusal wins, and
the code only ever means "right value, unevaluated form". The kernel never
simplifies anything itself. Applying the entry is the learner's move (§2).

It is relative to the entries in force. `cos 0`, `exp(ln 2)` and `sin(pi)`
pass until their §6.8 entries are built, and `ln 2 + ln 3` passes because
no entry reduces it. These are listed as limitations in
`kernel/p1_expected.py`'s `EVALUATED_RULE`, with every accepted and refused
case. Refusing `atan(-1/2)` in favour of `-atan(1/2)` is a deliberate
canonical sign, not evaluation.

**Goals are authored with the problem, not written as you go.** That is not
about integrity — it is that a goal you write yourself while solving can drift
to fit what you found, and then proving it tells you nothing. Authoring them is
the dominant cost of the whole project (§17).

---

## 10. The numeric kernel

**A checked derivation that ends in a float ends in a printout, not a theorem.**
Everything §15 claims is about steps the kernel verified, so the moment a value
arrives by floating-point evaluation the last line of the proof is the one line
nothing stands behind, and `approx` becomes the hole in the claim rather than
its conclusion. Whatever produces a number must produce it with an enclosure or
not be admitted as evidence at all. *(The corpus corroborates the precision
target rather than creating the requirement: the readiness sheet asks for five
significant figures throughout and warns that "if yours differs in the third
significant figure, something is wrong rather than rounded", which fixes how
narrow an enclosure has to be, not whether there is one.)* So:

- **Exact rationals** (`fractions.Fraction` — §16.2) as the endpoint
  representation.
- **Interval endpoints are rounded outward to a bounded working precision**,
  under an explicit precision parameter. Outward rounding preserves the
  enclosure property, so §15's claim is untouched.
- **Certified enclosures** for the transcendental atoms `exp`, `ln`, `sin`,
  `cos`, `atan`, `sqrt`, behind the interface `enclose(atom, interval,
  precisionBits) → [lo, hi]`.
- **Interval arithmetic** composes those enclosures outward, so the result is
  an interval that provably contains the true value.

**The bounded precision is not a refinement, it is a correction.** Revision 1
specified exact rationals "composed outward" with no rounding policy — the
words *precision* and *rounding* did not occur in the document — and the review
implemented that literally, with 12-term Taylor for `sin`:

| composition depth | numerator digits | denominator digits | time |
|---|---|---|---|
| 1 | 33 | 34 | 1 ms |
| 2 | 790 | 791 | 25 ms |
| 3 | 18,199 | 18,200 | **20,668 ms** |

Depth 4 did not terminate in two minutes. Every add and multiply multiplies
denominators, so endpoint bit-length grows superlinearly in the operation
count. The composition that blows up is `sin(√x)` — §8.1's flagship `probe`
example — so as written, §10 could not evaluate this document's own headline
example, let alone in the tenth of a second §8.6 promises.

### Where the atoms come from

**Recommendation: MPFR, through `gmpy2`** (which wraps GMP, MPFR and MPC and
exposes directed rounding), and this is the one place in the document where
reuse is recommended *below* the trust line. It is a dependency, and §16.2's
stdlib-only rule is for v1 — this arrives with stage 2, and is exactly the kind
of dependency that should have to argue for itself and can.

Measured during review, against the WASM build of the same library: MPFR's
`ROUND_DOWN`/`ROUND_UP` are genuinely directed (at 24 bits, `sin(0.5)` gives lo
0.479425519, hi 0.47942555), so **evaluating twice is a certified enclosure** —
by MPFR's specification rather than by a remainder bound proved on a napkin.
Every atom §10 needs is present, plus `erf` (§8.2's own special-function
fallback) and `gamma`. Endpoints come back as dyadic rationals, so §10's
"intervals with rational endpoints" survives verbatim. The WASM build measured
20,000 `ln`+`sin` evaluations at 200 bits in **318 ms** (~16 µs each); the
native bindings will be faster, so a thousand-panel quadrature with four
evaluations per panel is comfortably inside §8.6's tenth of a second.

*(Revision 3 specified `gmp-wasm` — a 385,644-byte CDN bundle — because the
kernel was to run in a browser. §16's move to a local process removes that
constraint: the same library, natively, with no bundle and no WASM boot. The
measurement above is retained because it is the evidence for the
directed-rounding claim, which does not depend on the binding.)*

**What it costs, stated rather than smuggled.** §15's reviewability claim
changes shape: the trusted base now includes MPFR, and nobody reads MPFR in an
afternoon. The honest comparison is not *reviewed* versus *unreviewed* but
"bespoke code one person read once" versus "the reference implementation behind
GCC and Sage, with twenty-five years of adversarial testing concentrated on
precisely the hard cases" — and this is the one trusted component where bespoke
code fails **silently** (§17's bank cannot see an enclosure that is too narrow)
and where the library's entire specification *is* the property needed. Two
smaller costs: it buys point evaluation only, so the interval extension and
composition remain bespoke; and it is LGPL, which §18 Q6 must
answer before this is published anywhere.

The `enclose(atom, interval, precisionBits) → [lo, hi]` interface is the hedge,
and it costs nothing: the decision is reversible, and §17's numeric falsifier
arm tests the interface rather than the implementation.

### What the bespoke half still owes

For each atom, whether from MPFR or not, §10 owes the reduction identity used
and its **range of validity after reduction**. `atan` outside |x| ≤ 1 is the
genuine soundness hazard — the alternating-series remainder bound is simply
invalid there, and a naive implementation emits a bogus certificate rather than
a slow one. Cancellation in `ln` near 1 and `exp` of large negative arguments
are *cost* problems under exact arithmetic, not correctness problems; they
should not be conflated with the first.

`approx e ≈ q ± tol` then succeeds iff the computed enclosure is contained in
[*q* − tol, *q* + tol]. Two consequences worth naming:

- A **narrow enough** enclosure proves the digits. `0.83565` to five
  significant figures is a theorem, not a printout.
- This same engine can be pointed at **the course's own numbers**, and §17 says
  where that is and is not a saving.

**`math.h`/double results and non-interval mpmath are never admissible as
in-tool evidence.** They are fine as an offline oracle (§17) and nowhere else.

---

## 11. Worked example: readiness P1

The sheet's first problem, in full, because it is the smallest thing that
exercises the whole design.

> Evaluate exactly, then give each to five significant figures.
> (1) ∫₀^{π²/4} sin √x d*x*  (2) ∫₀¹ d*x*/(1 + *x*³)

### 11.1 Part (1)

```
problem readiness.P1.1
  answer schema  closed
  goal  Int[x = 0 .. pi^2/4] sin(sqrt x)  ≐  ?A
       obl  4 # 0                                      by norm_num     ✓
       obl  0 ≤ pi^2/4                                 by sign         ✓
       obl  x ≥ 0  @ [0, pi^2/4]                       by range        ✓

proof
  step subst (x := t^2) over t in [0, pi/2]
       obl  2 # 0                                      by norm_num     ✓
       obl  0 ≤ pi/2                                   by linear, pi_pos ✓
       obl  0^2 ≐ 0                                    by ring, in step ✓
       obl  (pi/2)^2 ≐ pi^2/4                          by ring, in step ✓
       obl  t^2 ∈ C¹([0, pi/2])                        by reg          ✓
       obl  sin(sqrt(t^2)) ∈ C⁰([0, pi/2])             by reg          ✓
       obl  t^2 ≥ 0  @ [0, pi/2]                       by sign         ✓
  ⊢ Int[t = 0 .. pi/2] sin(sqrt(t^2)) * (2*t)  ≐  ?A

  step rewrite sqrt_sq
       obl  t ≥ 0  @ [0, pi/2]                         by range        ✓
  ⊢ Int[t = 0 .. pi/2] sin t * (2*t)  ≐  ?A

  step ftc  F := 2*sin t - 2*t*cos t
       obl  F ∈ C⁰([0,pi/2]) ∧ F ∈ C¹((0,pi/2))        by reg          ✓
       obl  D[t] F ≐ sin t * (2*t)  @ (0,pi/2)         by deriv; ring  ✓
       obl  sin t * (2*t) ∈ C⁰([0,pi/2])               by reg          ✓
  ⊢ (2*sin(pi/2) - 2*(pi/2)*cos(pi/2)) - (2*sin 0 - 2*0*cos 0)  ≐  ?A

  step rewrite [sin_pi_half, cos_pi_half, sin_zero]
  step close  ?A := 2                                  by ring         ✓
qed

  Proved.  0 admissions.
```

*(Revision 10. The proof-of-life runs this from the substituted goal on, with
discharge stubbed, and reports `Proved modulo 6 admissions`: the three `reg`
premises, `t^2 ≥ 0`, `t ≥ 0` and `0 ≤ pi/2`. The derivative premise is decided
in the step, and `pi/2`'s literal divisor `2 # 0` by `norm_num`. Three lines are
new and one moved. `x ≥ 0` and `t^2 ≥ 0` are `sqrt`'s own domain, now a
former (§5.1), and `t^2 ≥ 0` was listed before only as `reg`'s sub-obligation. The orientations
`0 ≤ pi^2/4` and `0 ≤ pi/2` are now owed (§6.4), and `pi_pos` moves to the
second, since by-range needs the order before it can supply `t ≥ 0`. `sqrt_sq`'s
obligation is written as the entry states it, `t ≥ 0`, because obligations are
keyed in each rule's own orientation.)*

*(Revision 10, int_subst: the kernel now runs this from the sheet's own goal,
with the `subst` step included, and reports `Proved modulo 5 admissions`. Two
of them are the substitution's `reg` premises and three are `ftc`'s, so every
one is regularity, which §6.9 closes. Everything else is discharged. The
endpoint line was one conjunction and is two obligations, because §5.2's goals
are lists. Both are decided in the step by `ring`, with §6.8's exact values
first where φ is transcendental, and neither can be admitted (§6.4). `pi/2`'s
`2 # 0`, which the note above mentions, is listed now, and so is the goal's
`4 # 0`. The substitution's lines are in the order the kernel emits them. The
new integrand is shown tidied: the kernel carries `deriv`'s `2*t^1*1`, which
`ring` reads as `2*t`. The run is staged beside the main proof set, and it
joins that set in the next consolidation step.)*

*(Revision 10, consolidation, E52: it has joined. The sheet's goal is now
P1.1's official route, run by every check that runs the main proof set, and
it reports `Proved modulo 5 admissions`, all regularity. Before the build,
every planted bug and mutation the suite runs was re-traced by hand against
it. The proof that starts from the substituted goal stays, as the proof of
that goal. The `0 ≤ pi/2` line is now the orientation key of §6.4's
decision, discharged the same way.)*

Three things to notice, and one correction from revision 1. *(Revision 9
brought the `ftc` premises up to §6.4's split form, named `pi_pos` beside
by-range, dropped `cos_zero`, which `ring` makes unnecessary since
`2*0*cos 0` is 0, and removed a rule count nobody had checked.)*

**The `sqrt_sq` step is the whole argument for this design.** √(*t*²) = *t* is
false — it is |*t*| — and a CAS will make that rewrite without comment. Here it
is a rule with the side condition 0 ≤ *t*, discharged from the integration
range. Over [−π/2, π/2] the step would be refused — whoever proposed it.
That is a *lost sign* caught by construction, which is the failure mode the
readiness sheet names as the gap. (And §5.1's orientation convention is what
stops the same range being written backwards to make the constraint set
inconsistent and prove anything at all.)

**Integration by parts never appears — in this mode.** The script above is
`check` mode: *F* = 2 sin *t* − 2*t* cos *t* arrived from somewhere, and the
kernel verified it by differentiating. Where it arrived from is not the
kernel's business — §8.1 shows the same problem explored in
`assisted` mode, worked by hand, and checked, and each of them produces this
same `ftc` obligation and the same proof.

**The factor of 2 is checked, not trusted.** Had *F* := sin *t* − *t* cos *t*
been offered — by you, or by a buggy integrator — `deriv; ring` rejects the
step and §8.7 reports the residual: short by one copy of *t*·sin *t*. This is
why §8.2 can be as heuristic as it likes.

**The correction:** revision 1 put the substitution's continuity obligation on
`sin(sqrt x) ∈ C⁰([0, pi^2/4])`, where the image, the endpoint interval and the
goal's integration range all coincide — so the worked example did not show the
real obligation. It is on the composed integrand (§6.4), and the nested `t² ≥ 0`
is what `reg` needs from §6.9's `sqrt` entry.

### 11.2 Part (2), compressed

```
problem readiness.P1.2
  answer schema  closed
  goal  Int[x = 0 .. 1] 1/(1 + x^3)  ≐  ?A
       obl  1 + x^3 # 0          @ [0,1]     by product (F's ln domains; ring) ✓

proof
  step ftc  F := (1/3)*ln(1+x) - (1/6)*ln(x^2 - x + 1)
                 + (1/sqrt 3)*atan((2*x - 1)/sqrt 3)
       obl  1 + x > 0            @ [0,1]     by range                       ✓
       obl  x^2 - x + 1 > 0      @ [0,1]     by sign ((x-1/2)² + 3/4)       ✓
       obl  sqrt 3 # 0                       by sqrt_pos                    ✓
       obl  F ∈ C⁰([0,1]) ∧ F ∈ C¹((0,1))    by reg                         ✓
       obl  D[x] F ≐ 1/(1 + x^3) @ (0,1)     by deriv;
                                                field [sqrt_sq_val 3]       ✓
            ⤷ obl  1 + x > 0            @ (0,1)  (d_ln)   by range          ✓
            ⤷ obl  x^2 - x + 1 > 0      @ (0,1)  (d_ln)   by sign           ✓
            ⤷ obl  1 + x # 0            @ (0,1)  (field)  by range          ✓
            ⤷ obl  x^2 - x + 1 # 0      @ (0,1)  (field)  by sign           ✓
            ⤷ obl  1 + ((2*x - 1)/sqrt 3)^2 # 0
                                        @ (0,1)  (field)  by sign (as written) ✓
            ⤷ obl  1 + x^3 # 0          @ (0,1)  (field)  by product        ✓
       obl  1/(1+x^3) ∈ C⁰([0,1])            by reg                         ✓
  step rewrite [ln_one, atan_one_sqrt3, atan_odd]
  step close  ?A := (1/3)*ln 2 + pi/(3*sqrt 3)            by field          ✓
       obl  3*sqrt 3 # 0                     by product (sqrt_pos)          ✓

  step approx ?A ≈ 0.83565 ± 5e-6
       enclosure [0.8356487, 0.8356489]                                     ✓
qed
```

*(Revision 10. Literal obligations are decided by `norm_num` at once and are
not listed: `3 # 0` and `6 # 0` from F's coefficients, `3 ≥ 0` from `sqrt 3`
and from `sqrt_sq_val 3`, `2 > 0` from the answer's `ln 2`, and the four literal
`ln` domains that `ftc`'s endpoint substitution produces. `approx`'s literals
are not terms, since the term grammar has no decimals (`kernel/GRAMMAR.md`
D1), so stage 2's `approx` brings its own numeric syntax.)*

The learner did the partial fractions and the numerator split by hand — that is
the exercise. The kernel's contribution is the one line that matters: the
`deriv; …; field` obligation is a page of algebra, done exactly, and if the
learner's *A*, *B*, *C* are wrong it fails with the residual named.

**Three obligations changed in revision 2, and each was wrong rather than
loose.** The `deriv; field` step was **false as annotated**: `sqrt 3` is an
opaque atom (§6.2), so `field` sees a free atom *s* unrelated to 3, and the
residual in ℚ(x, s) is (3/2 − s²/2)/(s²x² − s²x + s² + 4x⁴ − 8x³ + 9x² − 5x + 1),
which is identically zero iff s² = 3. `sqrt_sq_val` supplies exactly
that — *(stage 0c confirmed this residual in code, and corrected how the fact
gets in)*. The `close` step was `by ring`, which divides by `sqrt 3` — not a ring
operation; it is `by field`, and the `sqrt 3 # 0` it emits arrives from
`sqrt_pos` (that obligation is emitted earlier anyway, since §5.1's `/` former
carries it, so writing *F* at all requires it). And `1 + x^3 # 0` was labelled
`by domain (linear)`, which is provably wrong — with x³ an uninterpreted atom
the domain 0 ≤ x ≤ 1 constrains it not at all, and an odd cubic falls outside
both sign certificates. It closes by §5.3's **sign product**, method 5,
as a product of the two facts already established above it, with `ring`
certifying the factorisation 1 + x³ = (1 + x)(x² − x + 1). *(That method was
unnamed when this example was written and was named because of it, and because
of the four derivative entries §6.3's sweep found needing the same move.)* No factoriser and no enclosure engine is
involved: the factorisation comes from the learner's own *F*.

Note `x² − x + 1 > 0` discharged by the sum-of-squares certificate of §5.3 —
a domain condition the paper solution passes over in silence, and the one the
obligation pane is for.

**Revision 7: the fact goes into `field`, not in front of it.** Revisions 2–6
wrote this step as `deriv; rewrite sqrt_sq_val; field`. Stage 0c ran it, and
the rewrite has nothing to act on. `d_atan` produces
`D[x]u / (1 + u^2)` with `u = (2x − 1)/sqrt 3`, and the output of `deriv`
contains no `(sqrt 3)^2` anywhere. The square exists only inside `u^2`, and
*s*² appears only once `field` has expanded it. No rewrite on terms can reach
it, so the fact is passed to `field` itself (§6.2, *facts*), which reduces the
normalised numerator modulo s² = 3. That is a parameter on a trusted rule, and
it is sound for the reason stated there.

Running it also produced **one obligation this example had never listed**:
`1 + ((2x − 1)/sqrt 3)^2 # 0`, which is `d_atan`'s denominator. It is true for
the obvious reason, but only if §5.3's sign certificate reads it *as written*.
After ring-normalisation it is a quadratic in x whose coefficients involve the
atom `1/sqrt 3`, and the discriminant test no longer applies. §5.3 now tries
the written form first. The spike runs this whole obligation, `deriv`
included, in about a millisecond.

**Revision 10: the list is now what the kernel emits.** The proof-of-life ran
this script with discharge stubbed and reports `Proved modulo 14 admissions`:
every `obl` line above except the derivative premise, which is decided in the
step. Three things in revision 9's list were wrong. `1 + x > 0 @ [0,1]` was labelled a
linear domain fact, when it is `ln`'s own domain on the closed range (§5.1)
and a different obligation from `d_ln`'s copy on (0, 1). `x^2 - x + 1 > 0` had
no domain at all. And `field`'s divisors `1 + x`, `x^2 - x + 1` and `1 + x^3`
on (0, 1) were missing, with only the `atan` denominator listed. The goal's own
`1 + x^3 # 0` on [0, 1] now closes by sign product on F's two `ln` domains,
which were previously implicit. The answer's other accepted form,
⅓ ln 2 + π√3/9, closes only as `close … by field [sqrt_sq_val 3]`, and owes no
`3*sqrt 3 # 0`, so its count is 13.

---

## 12. Worked example: unit 00, where physics enters

### 12.1 P1(a) — classify and take the first step

```
problem unit00.P1.a
  var  m b g : R   with  m > 0, b > 0, g > 0
  fun  v : R -> R
  assume eom : ∀t. m * D[t] v ≐ -(m*g) - b*v

  goal  classify(eom) ≐ F_of_v
    ∧   ∀t. t ≐ Int[w = v 0 .. v t] m/(-(m*g) - b*w)
            @  w # -(m*g)/b

proof
  step classify by free_vars        -- RHS mentions v; not t, not x    ✓
                                    -- a tactic report, not a judgement (§5.2)
  step apply sep_autonomous with f := (λw. -(m*g) - b*w)
       obl  -(m*g) - b*w # 0        @ w # -(m*g)/b   by field; hyp     ✓
       obl  f ∈ C⁰                                   by reg            ✓
       obl  v ∈ C¹                                   by hyp            ✓
qed
```

`classify` is decided by inspecting the free variables of the right-hand side,
which is decidable and is the standard test. (The unit's own Rung 2 phrases it
"cover up the left-hand side and read the right" — the same test, arrived at
independently, which is a reason to trust the implementation rather than a
reason for it.) For parts (d) and (e) it returns `None`, and
the goal asserting `None` is provable while any goal claiming one of the three
cases is not.

`sep_autonomous` is **derived** from `int_subst` and `ftc`, not an axiom. The
domain condition `w # −mg/b` is the point of the problem — the sheet says
"note where that integrand blows up" — and the kernel will not let the step
through without it.

*(Revision 1 discharged the first obligation `by field_sign`, a method named
exactly once in the document and defined nowhere. It is genuinely outside
§5.3's methods as stated — `b*w` is bilinear in two symbols, the goal is a
disequality, and the discharge needs `b > 0` to divide through — which is why
§5.3 now says a goal may be `field`-normalised first and that method 1 matches
disequalities. With `b > 0` in Γ this is −b(w + mg/b), and `hyp` finishes it.
The reach for a fifth method is also why §5.3 now offers `have`.)*

### 12.2 P2 — dimensional analysis, fully decided, and one thing that is not

The sheet's own P2(a): *the period P of a mass m on a spring of stiffness*
κ *(dimension* MT⁻²*), released from amplitude a.*

```
problem unit00.P2.a
  quantities  P : T,  m : M,  kappa : M·T^-2,  a : L
  assume closure : P = Phi(m, kappa, a)      -- the modelling assumption

  goal  rank ≐ 3  ∧  ngroups ≐ 1
    ∧   basis ≐ [ P*sqrt(kappa/m) ]
    ∧   conclusion  P ≐ C * sqrt(m/kappa),  C an undetermined pure number

proof
  step buckingham_structure                                             ✓
       rank 3 over Q; 4 − 3 = 1 group; verified dimensionless.
       a occurs in no group.
  step buckingham  from closure
       obl  closure                                  admit "modelling"  ⚠
qed

  Proved modulo 1 admission.
    closure — the relation holds among exactly these four quantities.
```

The rank half is decided outright, end to end, with no creative step required —
linear algebra over ℚ, and verified: the dimension matrix over (M, L, T) for
(P, m, κ, a) has rank 3, the null space is spanned by (1, −½, ½, 0), so
P√(κ/m) is a correct basis and δ_a = 0 is forced.

**The admission is the point, not a blemish.** "a occurs in no group → the
period is independent of amplitude" is a *physical* conclusion, and it rests on
a hypothesis the machine cannot check: that the relation holds among exactly
the declared quantities. Run the same rule on the simple pendulum with the
amplitude θ₀ omitted — dimensionless, a zero row, invisible to anyone reading
dimensions off the problem — and it certifies a falsehood (§6.6). Revision 1
reported "Proved · 0 admissions" for exactly that shape.

So the obligation pane shows the modelling assumption by name, every time. The
omitted-quantity trap is the actual content of dimensional analysis, and this
is where a learner meets it. The sheet still asks "what does the answer say
about the amplitude?", and the learner still has to say it.

---

## 13. What it covers, honestly

Doing the design against real units produced a finding that revised the scope
set at the start. Doing the **review** against the units' actual problems —
rather than their titles — revised it again, downward. Three of revision 1's
rows had been rated from unit titles.

**"Units 00–21" is not a clean target for a scalar language.** Rather more than
half of that range needs a sort the design does not have. The honest table:

| Units | Fit | Why |
|---|---|---|
| **00** ODE cases, dimensions | **Full** | The design was built against it. P7 (V = k\|x\|^n) is out: §5.1 keeps `abs` out of goals |
| **08** central forces | **Full** | Orbit equation is scalar quadrature |
| **09** Kepler's equation | **Full** | Series, iteration, `approx` |
| **11–12** variations, Lagrangian | **Full** | *Applying* Euler–Lagrange is scalar calculus |
| **14** Hamiltonian | **Good** | Legendre transforms; brackets need pairs |
| 01 determinism | Partial | `picard` applies; the existence *proof* is metatheory |
| **06** driven oscillator | **Partial** | Linear ODEs and resonance are in. P2 is complex end to end (Euler, (1+i)^8, Re/Im of ker L); P12 wants complex ω and zeros of p(iω); P10 convolves against an arbitrary continuous *f*, which §5.1 forbids outright |
| 10 Legendre, 13 Noether, 15 H–J, 21 asymptotics | **Tier 2** | Need recurrences / symmetry structure / limits library |
| 04–05 work, flux, Gauss | Extension | Vector calculus — but see below |
| 18 wave equation, 19 Fourier | Extension | PDEs in components; then function spaces |
| **03** frames | **New sort** | SO(3), the hat map, the transport theorem. P8 is "R â Rᵀ = (Ra⃗)^"; P9 is Coriolis; P5–P6 are Frenet frames. That is matrices, eigenvalues and quadratic forms. P1 and P2 are also *negative* results ("is nevertheless **not** continuous"), and piecewise-defined with the value patched at the origin |
| 07 normal modes, 16 rigid bodies | **New sort** | Matrices, eigenvalues, quadratic forms |
| 20 Fourier transform, complex | **New sort** | Complex plane, contours, residues |
| 02 phase portraits, 17 chaos | **Out of reach** | Qualitative and numerical, not equational |

Two softenings, both of which survive. First, `D[x] e` where *e* mentions other
variables **already is the partial derivative** — multivariate scalar calculus
costs nothing extra, so 04, 05 and 18 are reachable *in components* (∇·**F**
written out) with a modest extension rather than a new sort. Second, the truly
out-of-reach units (02, 17) are the ones where the course is teaching
qualitative judgement, which is not a fluency problem and was never the target.

**On complex numbers:** do not make ℂ a stage-0 gate. No stage-1 or stage-2
deliverable contains a complex number, so the question can be decided when unit
06 is approached. It is recorded in §18 as an item separate from the
functions-as-objects question, because they are different questions — one is a
sort, the other is an order.

**The readiness sheet is P1–P5, not "in full".** Revision 1 said in full and
was wrong by five problems out of twelve. The sheet has five groups: P1–P5 are
the calculus-fluency group and are in scope; P6 is an interchange of limit and
integral that *fails*, which is a negative result; P7 is ∫₀^∞ sin x/x, which the
sheet itself solves by differentiating a parameter; **P8–P12 are not scalar
calculus at all** — dual basis and the matrix of a bilinear form; the signature
of xy+yz+zx and "no 2-dimensional subspace makes q positive definite"; an
orthogonal Q diagonalising a symmetric K and Jⁿ of a Jordan block; Banach's
fixed-point theorem; the group of hyperbolic rotations with orbits and
stabilisers. Those are the "new sort" row, four lines above.

**The revised target that the design actually supports:** not a unit range, but
**the readiness sheet's P1–P5, unit 00 complete, and the calculus-fluency
subproblems wherever else they occur** — which within the units above means the
scalar parts of 06, 08 and 09. That is a smaller and much more defensible
project than revision 1's table advertised, it is what the stated need is, and
it is measurable.

**The √(a² − x²) row now runs end to end, and it shows what a trigonometric
substitution costs** *(revision 10, consolidation, E55)*. ∫₀¹ √(1−x²) dx =
π/4 by x = cos θ is §5.1's canonical reversed case, and §8.5's second
recognizer row with cos for sin. It is
`kernel/problems/consolidation/QC1.json`, and it proves `Proved modulo 5
admissions`, all regularity:

```
problem consolidation.QC1
  goal  Int[x = 0 .. 1] sqrt(1 - x^2)  ≐  ?A
       obl  1 - x^2 ≥ 0  @ [0, 1]                 by sign product      ✓

proof
  step int_subst (x := cos θ) over θ from pi/2 to 0
       obl  0 ≤ pi/2                              by linear, pi_pos    ✓
       obl  cos(pi/2) ≐ 0,  cos 0 ≐ 1             exact values, in step ✓
       obl  cos θ ∈ C¹,  sqrt(1 - (cos θ)^2) ∈ C⁰  on [0, pi/2]   by reg
       obl  1 - (cos θ)^2 ≥ 0  @ [0, pi/2]        by sign product, cos bounds ✓
  ⊢ Int[θ = 0 .. pi/2] −(sqrt(1 - (cos θ)^2) * (−sin θ))  ≐  ?A

  step rewrite pyth_cos at (cos θ)^2
  step rewrite sqrt_sq  (u := sin θ)
       obl  sin θ ≥ 0  @ [0, pi/2]                by cite sin_nonneg_on ✓
  ⊢ Int[θ = 0 .. pi/2] −(sin θ * (−sin θ))  ≐  ?A

  fact h := pyth_cos (u := θ)
  step ftc  F := (θ - sin θ * cos θ)/2
       obl  D[θ] F ≐ −(sin θ * (−sin θ))  @ (0, pi/2)   by deriv; field [h] ✓
       obl  F ∈ C⁰, F ∈ C¹, the integrand ∈ C⁰    by reg
  step rewrite [sin_pi_half, cos_pi_half, sin_zero]
  step close  ?A := pi/4                          by ring              ✓
```

Integrands are shown tidied, as in §11.1, and the literal divisors' `# 0`
lines are left out. The five `reg` judgements are the admissions. The
substitution flips, because x = cos θ is decreasing and `0 ≤ pi/2` is
proved (§6.4). Three things are the point. **Both sign products are non-strict** (§5.3 method 5), and
before the consolidation both were admitted `none`. **`pyth_cos` is used
twice, by two routes**: as a rewrite, so that `sqrt_sq` can match
√(1 − (1 − sin²θ)) through `ring_nf`, and as a `field` fact, because F′ holds
cos²θ and the check is §6.4's trig-identity case, which escapes ℚ(atoms)
until the fact reduces cos²θ to 1 − sin²θ. **Nothing large was needed**: no extension of `field`, and no `trig_norm`.
Two wrong moves are in the suite. Dropping the fact refuses `ftc` with the
residual, and applying `sqrt_sq` before `pyth_cos` is refused as a
left-hand-side mismatch.

### The limits that remain, all of them technical

Nothing below is a policy. These are the places where the mathematics or the
scalar term language genuinely runs out.

- **Equality of transcendental expressions is undecidable** (§3). Some true
  equalities are unreachable by any finite rule table, and no amount of
  automation changes that. This is the system's permanent incompleteness.
- **The kernel proves only positive statements.** There is no negation (§5.2).
  "This is not continuous", "this diverges", "this limit does not exist" and
  "your answer is wrong" are outside the system. `check` on a wrong answer
  yields `Stuck`, which is indistinguishable from "your answer is right and I
  could not find the proof"; §8.6's enclosure is what makes a rejection
  decisive in practice, and it is not a judgement.
- **Some antiderivatives do not exist in elementary form.** ∫e^{−x²},
  ∫sin *x*/*x*, ∫e^x/*x* — Liouville's theorem, not a failure of §8.2. The
  fallbacks are a named special function or `quad_verified`. Readiness P7 is
  exactly this case, and it is why the sheet solves it by differentiating a
  parameter instead. **The tool cannot prove non-existence**; it cites a table.
  This is a different claim from divergence, which revision 6 *can* prove: *no
  elementary antiderivative exists* is a statement about a language, and stays
  a citation.
- **The integrator is complete only for linear and irreducible-quadratic
  denominators, and the binding constraint is the output language** (§8.2), not
  the algorithm and not the budget.
- **There is no piecewise, Heaviside or min former.** Switched and impulsive
  drives (06 P7, P9, every Green's-function problem) cannot be stated, and
  neither can a function patched at a point (03 P1–P2).
- **`abs` has no rules** and appears only in side conditions and domains
  (§5.1). Unit 00 P7 is the casualty.
- **Functions as objects are out of the term language.** Uniform convergence
  arguments, inner-product spaces, P7's justification of differentiating under
  the integral sign. `leibniz` exists but its uniform-domination obligation
  will usually be `cite`d or admitted. This is the first-order design of §5.1
  showing its edge, and §18 asks whether to pay for a second sort.
- **Modelling is not in scope** — not withheld, simply absent. The tool sees
  the equations you give it and has no access to the physical situation they
  came from. Nothing about a proof checker helps you decide that the drag goes
  as *v*². §12.2 is this limit made visible rather than an exception to it.

---

## 14. The rule table, and machine-checking it later if the tool earns it

**The decision, stated first.** Revision 1 made a machine-checked rule table stage 4 of five
and treated it as the thing that turns "trust my kernel" into something better.
Revision 2 **deferred it until the tool has been built, used, and found
useful.** Revision 5 keeps the deferral and **unbinds it from Rocq**: this is a
*possibility the design stays open to*, not a plan with a prover attached. The
first implementation is not formally verified, and says so in its own UI.

**Two things could be verified, and the document has run them together.**
Separating them is most of the value of this section:

> **(A) The rules are true theorems.** That `ftc`'s statement is the
> fundamental theorem with its real hypotheses, that `int_subst` carries the
> right continuity condition, that `d_ln` needs `u > 0`. Statements about
> *mathematics*, checked against a library. **This is the cheap 80% and it is
> what §14 is about.**
>
> **(B) The kernel is a correct program.** That the code composing rules,
> matching, substituting and normalising does what it claims. A statement about
> *software*, which needs the kernel written in a prover and extracted — a
> different and much larger project, recorded in §18 and not planned.

§15's claim has only ever rested on (A): its condition (a) is "every rule in
the table being a true theorem", and condition (b) — the procedures being
correctly implemented — is exactly the part (A) does not touch. Doing (A) turns
condition (a) from an assumption into a checked fact and leaves (b) where it
is.

### Why

The ledger is a one-time fixed cost, and a real one: a generator
plus 80–110 lemmas, plus installing and choosing a library
stack that is not on this machine. Revision 1 priced it as an afterthought
("~60 lemmas") and the review repriced it as a small second project.

That cost is not the problem. The problem is *when* it falls. §17's largest
risk is not that the tool is unsound; it is that **the tool is built and not
used** — the four-month interest curve, and the layering question that no
reviewer can answer from a document. Verifying the rule table before that
question is answered spends the most expensive component in the plan on the
one whose value is entirely contingent on an outcome nobody has measured. If
the honest answer after stage 1's gate turns out to be "finish the
integrator, ship `solve`, and drop §1's claim", a machine-checked rule table for the thing that was not built is a
pure loss.

And deferring costs little, because **the guarantee was never load-bearing on
the first implementation's claim in the first place.** Revision 1's §15 already
said, correctly, that there is no Rocq proof of the kernel itself and that
the engine is reviewed-not-proved; §14 raised the *rules* only. Deferring it
moves one bullet from "done" to "planned"; it does not change the kernel's
status, and §15.1's claim is stated conditionally either way.

### What v1 owes anyway, to keep the option cheap

Three things, about a day of work between them, and skipping them is what would
make §14 expensive later rather than merely later:

1. **The rule table is data, in one module, behind one interface.** Not code
   with the conditions inlined at each use site — a table the kernel
   *interprets*. That is what makes it portable to a prover later without the
   rest of the kernel coming along, and it costs nothing now.
2. **A rule's condition is one datum, interpreted rather than transcribed.**
   Nothing anywhere re-states a side condition in prose or in a second
   language. This is also what §17's falsifier bank is generated from — one
   case per side condition, mechanically — so it earns its place long before
   §14 exists.
3. **The provenance column exists in the UI from the first build, showing
   zero.** `14 rule applications over 9 rules: 0 machine-checked.` A zero that
   is visible is an honest statement and a standing invitation; a column added
   later is a retrofit nobody does.

### The design, for when it lands

Doing (A) means stating, in whichever prover is chosen, that each entry of §6's
table is a true theorem — and then facing the problem the review identified as
this section's whole premise: **how does anyone know the lemma proved is the
rule the kernel runs?** Two artefacts, no shared execution of the condition
term, and a one-character divergence that is silent and fatal. Say the table
carries `u # 0` for `d_ln` while the prover proves the provable `u > 0` — §6.3
has both forms verbatim — and the kernel accepts `D[x] ln u ≐ u′/u` on a range
where u < 0 while the UI prints green.

**There are two ways to close that, and the choice of prover is mostly a choice
between them.**

- **Define the rules as data in the prover, prove the data sound, and extract
  it.** `Definition ftc_rule : rule := ...` together with
  `Theorem ftc_rule_sound : rule_sound ftc_rule`, where `rule_sound` quantifies
  over a denotation function. Then the extracted table *is* the table, and
  there is no correspondence left to argue about. The cost is that the term
  language and its semantics must exist in the prover — perhaps 15–20% of the
  kernel, and the most stable 15–20% — and that the kernel must be written in
  the extraction target, which **Python is not** (§16.2 pays this knowingly).
- **Keep the table in the kernel, and check the correspondence mechanically.**
  A generator, a round-trip parse of the prover's statements back against the
  table, and a build that fails on divergence. Weaker — it is a check rather
  than an identity — but it works from any implementation language, which means
  it works from here.

**Revision 5 does not choose.** The second is available from Python today and
is what §14 would do if cashed tomorrow; the first is better and is the reason
the rule table is data behind an interface (above), so that moving it into a
prover later does not drag the rest of the kernel with it. This is the one
place where §16.2's language choice has a lasting consequence, and it is
recorded rather than argued away.

Each rule then carries a provenance tag:

- `proved` — the Rocq lemma is proved and **its assumptions are a subset of a
  declared classical-reals whitelist**, diffed at build time, with the build
  failing on anything outside it;
- `cited` — discharged by a named stdlib/Coquelicot lemma, **with one line per
  library hypothesis naming the obligation the kernel emits for it**;
- `axiom` — stated in Rocq but `Admitted`, with a textbook citation
  (Buckingham's π theorem lives here);
- `unverified` — in the table and not yet backed by a lemma. **The UI shows
  these in red**, and in v1 every rule is one.

Three corrections to revision 1's version survive the change of mechanism, all
found by running it:

**`Print Assumptions` clean is unattainable, so the whitelist replaces it.**
Verified: under `Require Import Reals`, `Print Assumptions Rle_refl` and
`Rle_trans` each report `ClassicalDedekindReals.sig_forall_dec`, and
`Rplus_comm` and `derivable_pt_lim_mult` add
`FunctionalExtensionality.functional_extensionality_dep`. Every rule in §6 is a
statement about ℝ, so no lemma can print clean and the `proved` tag would
always be empty. A declared whitelist, diffed, is a *stronger* check anyway —
it catches the real risk, an `Admitted` rule leaking into the `proved` bucket —
and costs about ten lines. Print the whitelist once in the UI colophon.

**`cited` is weaker than `proved` and must be coloured differently.**
Coquelicot states hypotheses in its own vocabulary (`ex_derive`, `is_RInt` over
possibly-reversed intervals, `Rbar` endpoints, `continuity_2d_pt` for
`leibniz`'s domination). Deciding that those are implied by what the kernel
checks is itself a proof obligation, currently discharged by somebody believing
it. Folding `cited` into a green count overstates what was checked. Note that
extraction does **not** help here: a `cited` rule's correspondence to its
library lemma is a mathematical claim, not a translation.

**The statements must go through the partial forms.** Rocq's Reals are total —
verified: `Rinv_0 : / 0 = 0`, and `Rdiv r1 r2 = r1 * / r2` — and Coquelicot's
`Derive`, `RInt` and `Lim` are total functions returning junk outside their
domains. For the rules §6 lists the total and partial readings coincide,
because those rules carry their definedness conditions on the source side.
*(Revision 10: until then this was false of `ring` and `field`, which cancelled
atoms such as `ln(-1)` and so proved `0*ln(-1) ≐ 0` with nothing owed. It holds
now because §5.1's partial builtins are formers and the normalisers refuse
`Int` and `D`.)* The
Rocq statement must carry them too, with `D[x] e ≐ f` going through
`is_derive` and never `Derive`, `Int[...]` through `is_RInt` and never `RInt`,
`lim[x -> a^s]` through `is_lim`. The last is sharpest, since Coquelicot's
`Lim` is a right-sided sequential limit and a rule about a two-sided limit
could be underwritten by a one-sided one. The regression test must be one where
the junk value *coincides* with the claim: `D[x] |x| ≐ 1 @ x ≥ 0` is true under
the total reading and false under `is_derive`; `Int[x = -1 .. 1] 1/x^2 ≐ -2 @ ⊤`
is the matching `RInt` case. (`D[x] |x| ≐ 1 @ ⊤` tests nothing, being
refutable under both readings.)

**Which prover: open, and deliberately so.** Revision 4 had it mostly settled
by the implementation language; revision 5's Python kernel unbinds it again,
which is a genuine gain — the decision can now be made on the *library*, which
is what should have decided it all along. Revision 1 said the tooling exists
here today. That is true of `rocq-mode.el`
and the Rocq MCP server and **false of the libraries**: the `rocq9.1` switch
has Rocq 9.0.0, mathcomp 2.5.0, MetaRocq, Equations and VerifiedExtraction, and
**no Coquelicot, no Flocq, no coq-interval, no mathcomp-analysis** — nor does
`coq8.19`. So `opam install rocq-coquelicot rocq-interval` remains a
prerequisite, and the choice between Coquelicot and mathcomp-analysis is still
open and still wants a two-lemma spike (`int_subst` and one integral-table
entry, judged on side-condition discharge rather than line count).

**Lean 4 + Mathlib is fully in contention**, and on libraries alone it may be
ahead: `intervalIntegral` with FTC-1/FTC-2, `integral_comp_smul_deriv` matching
§6.4's `int_subst` hypotheses, interval parts, and
`fun_prop`/`measurability`/`continuity`/`positivity` aimed squarely at the side
conditions §4.1 calls brutal. Against it: a heavier toolchain, no MCP
integration in this workspace, and API churn against a file meant to be proved
once. Rocq's advantages are incumbency, `rocq-mode.el` and the MCP server
already here, and — if the data-and-extract route is ever taken — that MetaRocq
and VerifiedExtraction are already installed on the `rocq9.1` switch, which
would move the translation *out* of the trust base rather than into it.

**Rocq remains the most likely answer and is not the committed one.** §18 Q7
stays open, to be settled by a two-lemma spike when and if the question becomes
live.

### What would flip this decision

Either of these, and the deferral ends:

- **The layering gate passes and a unit's worth of real work has been done in
  the tool** (§17). At that point the tool is a thing that gets used, and the
  ledger is worth building.
- **A falsifier-bank acceptance traces to a rule *statement* rather than an
  implementation bug.** That is direct evidence that the v1 argument of §15.4
  is not enough, and it should be acted on immediately rather than at the next
  milestone.

---

## 15. The soundness claim, stated exactly

### 15.1 The claim

> **Claim.** If the checker reports `Proved` for a script establishing goal *G*
> in context Γ, then *G* is a true statement about the reals under Γ, on the
> domain recorded in *G*.
>
> **Conditional on:** (a) every rule in the table being a true theorem;
> (b) `ring`, `field`, `norm_num` and the interval library being correctly
> implemented; (c) the parser rendering the intended statement.

And the caveats, stated plainly because a claim of soundness with hidden
conditions is worse than no claim.

### 15.2 The trusted base

**This is a list of judgements accepted without further evidence, not a list of
components.** Revision 1 listed six components, and at least four accepted
judgements had no component on the list. The difference is not bookkeeping: an
obligation discharge is *terminal*, so anything that can tick one is trusted
whether or not it looks like a kernel.

1. **The term representation and syntactic equality**, including substitution
   and the metavariable scope check (§9).
2. **The rule table** — 55–70 analysis rules plus a 25–45 entry identity and
   exact-value table (§6), including §6.9's regularity rules, and — while
   `ftc` accepts `deriv`'s output without a re-deriving kernel step, as the
   proof-of-life does — `deriv`'s output forms and side conditions (§6.3).
3. **The rule matcher and instantiator.** §11.1's `rewrite sqrt_sq` binds the
   schema's `u` to a bound `t`; "capture-avoidance is a solved problem" is a
   claim about the term language, not about the implementation.
   *(Revision 10, consolidation review, E57: it is also what bound `pyth`'s
   u to `D[x](abs x)`, a term that does not denote everywhere, and the
   entry's right side then erased it. `rewrite` now refuses any instance
   value or target holding an `Int` or `D` node, §6.1.)*
4. **`ring`, `field` and `norm_num`** — the three reflective procedures, with
   `field`'s divisor obligations and its reduction modulo facts (§6.2) the
   soundness-bearing behaviour.
5. **The obligation tracker, the certificate checkers and the exact-value
   rewrite.** The checkers are hypothesis, Farkas (methods 2 and 3), sign,
   sign product and cite. The exact-value rewrite (E31) uses item 3's matcher
   and item 7's entries. *(Discharge, E28–E29: by-range is now a Farkas
   certificate over the range's own items, checked like method 3. The
   satisfiability pre-check runs in the untrusted search, because its
   verdict can only withhold a discharge. Every search, including
   Fourier–Motzkin, is untrusted, and only its witness is checked.)*
6. **The certified-enclosure library** (§10), and MPFR if adopted.
7. **The `cite` library file** (§6.8), whose entries carry provenance tags.
8. **The parser and pretty-printer.**
9. **The quadrature engine, but only in proofs that use `quad_verified`**
   (§8.6). Revision 1 said this in prose beside a list that read as exhaustive.

**Two things came back out of the list, deliberately.** Fourier–Motzkin over ℚ
and the sign-certificate heuristic were the two largest pieces of unlisted
trusted code in revision 1 — error-prone on strict-versus-non-strict
combination, and on carrying through constraints that do not mention the
eliminated variable. Having each emit a witness the kernel re-checks
(§5.3) moves both out. That is the one place in this revision where the trusted
base **shrinks**, and it is why §7's LCF claim is now true of `domain`.

**What keeps it small is that every item must be auditable, not a size.**
Each item is a judgement someone has to be able to check by reading: a rule
statement against its theorem, a normaliser against its specification, a
matcher against its instantiation. The threat to that is not length. It is
trusted code whose output nothing re-checks, so the argument for each item is
made from what it does. *(Revision 10 dropped the line estimate that stood
here. It was a budget, not an argument.)*

**Untrusted code the kernel calls (revision 10).** The kernel calls three things
that are not on the list: the admission tagger, which names the §5.3 method an
admitted obligation expects (§5.4); the `closed` whitelist, untrusted by §9's
own account; and residual rendering (§8.7). None of them can yield a false
theorem, because the kernel's verdict does not depend on their being right. A
tag decides no obligation's status, a wrong whitelist can at worst accept an
answer of the wrong shape, and a residual is display. That is the condition
under which trusted code may call untrusted code, and each new callee has to
be argued the same way. *(Since revision 10 three more have been argued the
same way.*
- *E27's evaluated-answer check and E33's decided-false check can only
  refuse a step.*
- *The discharge search, including Fourier–Motzkin and the satisfiability
  pre-check, only proposes a certificate that trusted code then checks. A
  search bug costs an admission, never a discharge.)*

Everything else — tactics, UI, problem files and **the whole of §8** — is
untrusted and cannot produce a wrong `Proved`.

That last point deserves its own paragraph, because it is the load-bearing
claim of the revision that removed every pedagogical restriction from this
document. **§8 grew to include a full integrator, an ODE solver, `auto` and
`solve`, and this list did not change by one line.** The integrator, the
polynomial factoriser, the partial-fraction solver, the recognizer table and
the move palette all *search*, and every one of their outputs is checked by a
kernel step before it is believed. Six reviewers attacked that claim from
different directions and none of them broke it; the two leaks that existed were
`quad_verified` and the discharge procedures, and both are named above.

A bug anywhere in §8 costs you a rejected step, never a false `Proved`. That
is what made it possible to say yes to all of it.

### 15.3 The enforcement mechanism

"LCF discipline" is an adjective until something enforces it. In Milner's LCF
the guarantee is a *type*: `thm` is abstract, ML's module system makes its
constructors unreachable, and the compiler enforces it. **Python has no
equivalent and no approximation of one** — no abstract types, no private
fields, nothing unforgeable. This is the clearest cost of §16.2's choice of
language and it is met by architecture rather than by the language.

**The kernel hands out handles, not judgements.** Proof objects stay inside the
kernel module; what crosses to the assistance tier is an opaque identifier.
Tier 2 asks *"what is the conclusion of theorem 47?"* and is told; it never
holds the theorem, so it cannot construct, mutate or fabricate one. There is no
result object to build by mistake.

That last clause is the point. The realistic failure here is not an attacker,
it is **one tactic that assembles a result object instead of calling the
kernel** — a bug that looks like ordinary code and produces a `Proved` that no
rule justified. Handles make it unexpressible rather than merely wrong.

Two disciplines follow it out to the other boundary:

- **No proof state crosses the API.** §16.3's protocol carries step names, term
  arguments and node identifiers in, and rendered display state out. The client
  is shown *that* something was proved and *what*; it never holds the thing
  itself.
- **Nothing reconstructs a judgement from storage.** Persistence stores
  *scripts* and attempt trees, which are re-checked on load, never theorems.

The weaker fallback, if handles prove awkward in practice, is a `Thm` class
whose constructor demands a sentinel private to the kernel module. It is
forgeable in five lines by anyone who wants to, and impossible to trip over by
accident, which covers the realistic failure and not the adversarial one. Say
which is in force; do not let it be ambiguous.

**Both are in force, and that is stated (revision 10).** The proof-of-life uses
handles for facts: a fact slot takes only the object `fact` minted, by
identity, and copies, pickles and fabricated ids are refused. Proof states use
the sentinel: a `ProofState` demands a kernel-private token. That is enough for
proof states because a finished state is only ever produced by `step()`, and
the realistic threat, a tactic building a result object, is exactly what the
sentinel refuses. §16.3's API will replace in-process states with ids at the
boundary, which is where the handle model ends up anyway.

§17's bank carries the corresponding cases: a tactic that attempts to
manufacture a proved result, one that writes directly to the obligation
tracker, and one that round-trips a proof state through JSON and back. All must
fail. **In a language with abstract types these would be compile errors; here
they are tests, and that difference is exactly what §16.2 is paying.**

### 15.4 What carries soundness in v1, and what the deferral costs

**It is not machine-verified, and under §14 it will not be for some time.**
There is no Rocq proof of the kernel, and in the first
implementation there is no Rocq proof of the *rules* either. What stands in the
meantime is three things, and they are not equally strong:

1. **Certificate-checked discharge.** The two hardest pieces of reasoning in
   the trusted base — linear arithmetic and sign certificates — do not have to
   be believed, because the kernel re-checks their witnesses with `ring` and
   `norm_num` (§5.3). This is the strongest of the three, and it is
   *structural*: it does not depend on anyone having read anything.
2. **The adversarial falsifier bank** (§17), generated mechanically — one case
   per rule side condition from the rule table — and run in both directions, with
   correct answers that must be accepted as well as wrong ones that must be
   rejected. This is the main empirical evidence, and its coverage is
   measurable rather than asserted.
3. **A kernel built to be read.** This is real but weak, and revision 1
   overclaimed it. HOL Light's kernel, far smaller than this one, had
   genuine unsoundnesses found after years of expert reading; it is trusted
   today because of Harrison's self-verification, the CakeML/Candle verified
   kernel and decades of adversarial use — none of which is available here.
   Reviewability is a supporting property, not the argument.

**What the deferral actually costs, named precisely.** Items 1–3 are good at
catching *implementation* errors: a mis-normalised polynomial, a dropped
obligation, a tactic that fabricates a theorem. They are poor at catching a
**wrong rule statement** — a side condition that is missing, or present but too
weak. A rule stated wrong is stated wrong in the table, so it is stated
wrong in the bank's generated falsifiers too, and the kernel will cheerfully
and correctly apply a false theorem. §14 is precisely the thing that catches
that class, and it is the class being deferred.

This is not hypothetical. **Reading revision 1 found five rule statements that
were false or under-conditioned** — `picard` without its box or graph
containment, `alternating` without monotone decrease, `radius_limsup` with an
unstatable hypothesis, `d_pow_int` without its negative-exponent condition, and
§8.5's `f′/f → ln|f|` against a `d_ln` that requires u > 0. That cuts both
ways, and both ways are worth saying: careful reading *did* find them, which is
evidence for item 3; and there were five, in a table of sixty, which is
evidence for how much §14 would be worth. *(Revision 10: building the kernel
found two more of the same kind, both passed by every reading before it: `ftc`
without `a ≤ b` (§6.4), and the normalisers treating partial functions as total
(§5.1).)* *(Revision 10, consolidation review, E57: and one of a different
kind, which reached a false `Proved.` in the committed kernel. Every rule
involved was true. `pyth` holds for every real u. What failed was an
assumption under all of them, that a schema variable is bound to a term that
denotes. The matcher bound u to `D[x](abs x)`, and an entry whose right side
drops u erased it. That is §15.2 item 3 and a missing principle, not a
missing hypothesis, which is why the fix is one rule checked against every
move (§6.1) rather than a side condition on `pyth`. A falsifier bank
generated one case per side condition could not have produced it from
`pyth`, which has none. The skeptic reading the build found it.)*

So the honest v1 statement is: **"sound by construction where certificates
exist, sound by test against a mechanically generated adversarial bank
elsewhere, with the rule statements reviewed but not machine-checked."** That
is weaker than revision 1's headline and stronger than a CAS's, and it is what
the UI's `0 machine-checked` reports. When §14 lands, the first clause of
§15.1's condition (a) stops being an assumption and becomes a checked fact; the
rest is unchanged.

### 15.5 Build versus reuse

The principle that decides every row is §15.2's: a bug anywhere in §8 costs a
rejected step, never a false `Proved`. That answers build-versus-reuse
mechanically and in **opposite directions on the two sides of the line.**
Below the line reuse is usually wrong — you cannot review a library, so reuse
converts "sound by review" into "trust by reputation" — with one exception,
where bespoke code fails *silently* and the library's entire specification is
the property you need. Above the line reuse is free.

| Layer | Verdict | Why |
|---|---|---|
| Terms, equality, substitution | **build** | the object everything else is about |
| The rule table | **build the table; cite Coquelicot for its proofs later** | The rules are standard calculus with hypotheses restored. `Rules.v` should mostly be `cited`: Coquelicot has `is_RInt_derive`/`RInt_Derive` (`ftc`), `RInt_Chasles` (`int_split`), `is_RInt_comp` (`int_subst`, with exactly §6.4's hypotheses), the `Derive_*` family, `RInt_gen`, and `is_derive_RInt_param_bound_comp` (`leibniz`). Stdlib's `Rtrigo_calc` supplies §6.8's trig constants |
| `ring` / `field` / `norm_num` | **build** | Reflective, and `field`'s cancellation obligation is *the* soundness-bearing behaviour. No library emits nonvanishing obligations, because no library wants them |
| Enclosures of the six atoms | **reuse MPFR** (§10) | The one trusted component where bespoke code fails silently |
| Interval extension and composition | **build** | MPFR answers point evaluation only; enclosing `sin` over an interval containing a critical point is bespoke either way |
| Obligation tracker + §5.3 | **build** | An SMT solver would put 500k lines of C++ under the one component whose bug is a false `Proved`, to decide 0 ≤ x ⟹ 0 ≤ x³ |
| Parser | **build** | A small ASCII script grammar, not LaTeX. `unified-latex` and friends parse LaTeX, whose AST is macro-level, so adopting one means a LaTeX-AST → term-AST translation that is itself new trusted code. MathQuill/MathLive are input widgets, and putting one in front of a trusted component adds a second place where what you see differs from what you proved |
| `trig_norm` (§8.9) | **build** | Untrusted. It must emit `rewrite` steps against *this* rule table and *this* term language; a CAS simplifier returns an answer, not a sequence of §6.8 applications the kernel can check, which is the same reason §15.5 keeps SymPy out of the kernel |
| Pretty-printer | **reuse KaTeX** | Already a dependency and already the parser mitigation. Note the pin: §16 says 0.16.9, current is 0.18.x |
| §8 integrator, shipped | **build, scoped down** | §3's measurements: every shippable JS CAS returns *wrong* antiderivatives on this course's own integrals |
| §8 integrator, authoring oracle | **reuse SymPy 1.14, offline** | 16/16 on the course sample, median 30 ms, and its `1/(1+x**3)` output *is* §11.2's answer. Attacks the dominant cost, not the line count. Never shipped |
| ODE solver, factoriser, partial fractions | **build** | Small, pattern-driven, each output checked by one `ring`/`field` step |
| Palette, recognizers, `auto`/`solve` | **build** | The course's integration-techniques chapter indexed by syntax. The content is the value |
| Verified quadrature | **build on reused MPFR** | Arb's `acb_calc_integrate` is canonical and unavailable in the browser: `@sagemath/flint` was last published in 2021, predates the Arb–FLINT merge, has no `acb_calc_integrate`, is 36.7 MB and GPL-3.0-or-later |
| Numeric falsifier oracle | **reuse CoqInterval / mpmath, offline** | Build-time only; supplies the evidence §15.1's condition (b) otherwise lacks |
| Exact rationals | **reuse `fractions.Fraction`** | Stdlib, arbitrary precision, and the arithmetic below `ring` is not where this project adds anything. `gmpy2` is the escape hatch if profiling demands it (§16.2) |
| HTTP server | **reuse `http.server`** | Five endpoints over JSON for one local user. Stdlib keeps §16.2's no-dependency rule intact; a framework buys nothing |
| Client UI | **build, no framework** | §16.3 is three panes, a tree and Proof-General stepping over a JSON API — a framework buys nothing and costs the six-month rule. KaTeX renders what the server sends |

*(Revision 3's build-versus-reuse rows were argued for a browser. The verdicts
are unchanged by §16.2 — the reasoning was always about the trust line, not the
runtime — but three rows are new above, and the shipped-CAS row is now about
SymPy rather than Algebrite: see §8.2.)*

**The one row that must never move, stated as a rule rather than a
preference.** Writing the kernel in Python puts SymPy one import away from
every algebraic decision, and reaching for it inside the kernel would end the
project's claim rather than weaken it. `sympy.simplify` is a heuristic
normaliser, and §3 is nine paragraphs and two measured experiments on why a
heuristic normaliser cannot be trusted with an equality. **`ring`, `field` and
`norm_num` are bespoke, reflective and sound by construction; SymPy lives in
tier 2 and at build time and nowhere else.** The temptation will present itself
on a tired afternoon as a one-line shortcut in a function nobody will look at
again. It is the single highest-consequence line that could be written in this
codebase.

**Pyodide was not an escape** when the tool had to run in a browser: it ships SymPy 1.14 and mpmath
1.4.1 but **not** `python-flint`, so the browser route gives mpmath, which is
not rigorous and must not be trusted here — and it costs ~6 MB gzipped with a
2.7 s boot in Node and 13–17 s under WebKit.

### 15.6 The parser, and `admit`

**The parser is in the trusted base**, which is a real and irreducible
weakness: a misparse checks a different theorem. The mitigation is that the app
**always pretty-prints the parsed goal back in KaTeX above the editor**, so the
statement being proved is on screen in the notation of the sheet. That reduces
the risk to "the learner did not read what they were proving", which is the
same risk Rocq has.

**That mitigation only works if printing is a faithful inverse of parsing**, so
it is tested: a round-trip property test, `parse(print(t)) ≡ t` over every rule
schema, every worked example and a set of precedence-ambiguous inputs. A
printer that drops a precedence bracket or prints `-x^2` for `(-x)^2` restores
exactly the risk, and it is the failure the reader cannot see, because the
wrong rendering is what they are checking against. A dozen lines against
machinery stage 1 already builds.

**`admit` never yields `Proved`.** It yields `Proved modulo N admissions` with
the list. Incompleteness is visible debt — and §12.2 is the case where the
admission is the most valuable line in the output.

---

## 16. The application

### 16.1 Three tiers

```
  ┌──────────────────────────────────────────────┐
  │  UI            browser: DOM, KaTeX, no framework
  │                three panes, stepping, the ladder keys
  └───────────────── JSON over localhost ────────┘
  ┌──────────────────────────────────────────────┐
  │  ASSISTANCE    recognizer, palette, progress signal,
  │   untrusted    the attempt tree, later the integrator,
  │                `auto` and `solve`
  └──────────── handles, never judgements ───────┘
  ┌──────────────────────────────────────────────┐
  │  KERNEL        terms, rules, ring/field, ftc,
  │    trusted     obligations, discharge
  └──────────────────────────────────────────────┘
```

Revisions 1–3 had two layers and called everything above the kernel
"untrusted". That was true and too coarse: the assistance layer *manipulates
terms* and the UI *renders pictures*, and conflating them hid the fact that
they want different languages, different tests and different failure
behaviour. Three tiers, two boundaries, and each boundary carries a discipline
stated in §15.3.

**The kernel and the assistance layer are Python, in one local process. The UI
is browser technology, talking to it over JSON on localhost.** `./calc` starts
the process and opens a page. Single user, no accounts, no network, offline.

**`./calc` takes a corpus path and does not assume one** (§18 Q6, settled in
revision 6: the tool is its own artefact and the course points at it, so the
course problems are content it loads). This is §1's replaceability test made
operational rather than aspirational — *replace the course and only the problem
files change* is a claim the entry point either honours or quietly breaks, and
a default corpus baked into the binary is how it would break. A bare `./calc`
may still open the corpus it shipped with; what it may not do is make that the
only one reachable.

### 16.2 Why Python, and what it costs

**Because the project's binding constraint is finding out whether §1's loop
works, and Python is the shortest path to that.** §17's gate — does the average
hint rung fall over a corpus — is the central falsifier, it sits behind the
whole of stage 1, and any effort spent on implementation language before it is
effort spent on a question that is not in doubt. The recognizer table is
content, the progress signal is a heuristic, the attempt tree is bookkeeping;
none of them is hard, all of them are *fiddly*, and fiddly-and-not-hard is what
Python is for.

Three costs, stated rather than discovered:

**A verified kernel becomes a rewrite, not a swap.** No prover extracts to
Python. If §14 is ever cashed, the kernel is reimplemented in the prover's
extraction target and this one is retired. That is the same bet §14 already
makes — do not spend for an outcome that may not come — taken one level deeper,
and it is only defensible because §14 is a *conditional* (§14, "what would flip
this decision"). If verification were planned rather than possible, this would
be the wrong language.

**Python offers no enforcement of the LCF discipline.** No abstract types, no
private fields, nothing unforgeable. §15.3 therefore rests on an API discipline
rather than a type, and that discipline has to be taken seriously precisely
because nothing will catch a violation for you.

**Speed is a real risk in exactly one place.** `ring`/`field` normalisation on a
large rational function is the operation that can become pathological (§10
measured a related blow-up), and it is the one place the kernel does real work
in a loop. Mitigations in order: exact rationals from `fractions.Fraction`,
which is arbitrary-precision and stdlib; sparse polynomials as dictionaries
rather than dense structures; the outward-rounded bounded precision §10 already
requires; and a per-step timeout in the server, which §16.4 makes a first-class control. If it is still too slow, `gmpy2` moves the rational arithmetic to GMP
without touching the algorithm. Measure before optimising, and note that the
sizes here are undergraduate integrands, not computer algebra benchmarks.

**Measured, stage 0c (2026-09-23): not a risk at the corpus's sizes.** With
stdlib `Fraction` and dict-of-monomials polynomials, and nothing optimised:
§11.1's check takes 0.1 ms, §11.2's flagship (`deriv` plus `field` with a fact)
1.2 ms, unit 00 P4's quadratic drag 0.7 ms, a 16-factor partial-fraction check
8.6 ms, and a 32-deep continued fraction 4.4 ms. Only synthetic stress breaks
§8.6's 100 ms: a telescoping sum over 64 distinct factors (0.7 s, growing
roughly with the cube of the factor count) and (x + y + z + 1)^16 by `ring`
(144 ms for 969 terms, roughly quadratic in the term count). Those are the two
shapes to watch. Nothing in §11–§12 comes near either, so `gmpy2` and a
compiled normaliser both stay unneeded. The per-step timeout of §16.4 remains
the backstop. *(Load 2.4 on 8 cores during the run: one core was free for the
single-threaded bench, but it was not idle. None of these conclusions moves at
a factor of 2.)*

**Standard library only, for v1.** This is how the house rule survives — *a
thing untouched for six months must still open* — and it is the precedent
`./mr` set in this workspace (stdlib Python, no venv, because a virtualenv
hardcodes absolute paths and breaks when moved). `fractions.Fraction` is
stdlib. `http.server` is stdlib. The client is one HTML file with vendored
KaTeX. **Nothing in v1 needs a dependency**, and the first one that does should
have to argue for itself. SymPy arrives with the integrator at stage 3 and is
already a build-time dependency as the authoring oracle (§15.5), so it adds no
new kind of risk when it does.

### 16.3 The two boundaries

**Kernel ↔ assistance: handles, never judgements.** The kernel holds its own
proof objects and hands out opaque identifiers. The assistance layer asks *"is
there a theorem with id 47, and what is its conclusion?"*; it never holds the
theorem. In a language with abstract types the discipline is the type; in
Python it is this, and it is the only version available.

It is also stronger than it sounds, because the failure it prevents is not
malice but accident: a tactic that builds a result object instead of calling
the kernel is the realistic bug, and it cannot happen if there is no result
object to build. A `Thm` class with a construction sentinel is the weaker
alternative — forgeable in five lines of Python by anyone who wants to, but
impossible to trip over — and is the fallback if handles prove awkward.
*(Revision 10: the proof-of-life uses both, handles for facts and the sentinel
for proof states, for the reasons in §15.3.)*

**Assistance ↔ UI: rendered state, never proof state.**

```
  POST /step     { session, node, move, args }
      →  { node', goal, obligations, progress, probe, log }
  POST /retract  { session, node }        →  { node', goal, obligations }
  GET  /hint     { session, node, rung }  →  { category | row | params }
  GET  /palette  { session, node }        →  [ rule names matching ]
  POST /parse    { text }                 →  { term, katex }   -- the echo
```

**A rejected move returns a refusal in place of `node'`:**
`{ refusal: { code, message, residual } }`. It carries a stable code from the
kernel's list, a message for the learner, and §8.7's residual when the move was
a failed check. *(Revision 10: the table had no shape for a refusal, and every
must-refuse case in §17's bank needs one. The in-process `step()` returns
`Refusal(code, message, residual)`.)*

The client is a view with no authority: it cannot misrepresent the server's
state because it never holds it. **One round trip per move, carrying
everything** — §1's loop lives or dies on a move feeling instant, and the
progress signal (§8.5) and the speculative probe (§8.6) are per-move, so they
ride on the `/step` response rather than costing calls of their own. Localhost
round trips are sub-millisecond, but only if there is one of them.

**The same API drives the headless harness.** §17's stage 1 wants the kernel
proving §11.1 and §11.2 before the client exists; with this shape that is not a
separate harness, it is a script against the API, and it stays as the
regression suite afterwards. *(Revision 10: `kernel/proof_of_life.py` is that
script. It runs in-process against `step()` until this API exists.)*

### 16.4 The client

**Three panes and a move strip — and the middle pane is a tree.** Trial and
error produces branches, not a transcript, and a UI that only records the path
that worked throws away the part §1 says you are here to learn.

```
┌─────────────────┬──────────────────────────┬─────────────────────┐
│ PROBLEM         │ ATTEMPTS                 │ STATE               │
│                 │                          │                     │
│ readiness P1    │ ▾ root                   │ Γ  t : R            │
│ the statement,  │  ├ ✗ subst x := sin t    │    0 ≤ t ≤ pi/2     │
│ as the sheet    │  │    ~ value changed    │ ─────────────────   │
│ has it, KaTeX   │  └ ▾ subst x := t^2      │ ⊢ ∫ sin√(t²)·2t     │
│                 │     ├ ▸rewrite sqrt_sq   │     ≐ ?A            │
│ ── formal goal  │     │  step parts u:=t…  │ ──── PROGRESS ────  │
│ ∫₀^{π²/4} …≐?A  │     │  step close ?A:=2  │ ✓ sqrt_sq matches   │
│ schema: closed  │     └ ○ unexplored       │   at position 1     │
│                 │                          │ ──── OBLIGATIONS ── │
│ ── KaTeX echo   │  green above ▸, grey     │ ✓ 0 ≤ t      range  │
│    of the parse │  below, ✗ = retracted    │ ✓ t↦t² ∈ C¹    reg  │
│                 │  and kept                │ ⚠ open: none        │
├─────────────────┴──────────────────────────┴─────────────────────┤
│ MOVES  subst · parts · split · ftc · table · rewrite‹sqrt_sq, …› │
│ hints ? ?? ??? !        ~ probe          mode: assisted  ▾       │
└──────────────────────────────────────────────────────────────────┘
  Proved · 0 admissions · assisted · max rung 2 · 12 rules · 0 machine-checked
```

- **Retraction is the primary interaction, not an undo.** `↓` advances one
  step, `↑` retracts, `↵` re-checks to the cursor — Proof-General's, because
  that is the loop the learner already owns. A retracted branch is **kept and
  labelled**, not deleted: `✗ subst x := sin t — value changed` is a fact worth
  having on screen while you choose the next one, and it is the record §17's
  gate reads.
- **The attempt tree lives in the assistance tier and is the state model, not
  a view.** Any goal can be forked; branches carry their own obligation sets; a
  branch can be abandoned, annotated or promoted. It has to be in the state
  model from day one or it is a rewrite later — and it is also the shape a
  `solve` derivation arrives in when §2's preparations are cashed, which is why
  it earns its place twice. Note it holds *handles*, per §16.3, so a bug in
  tree management cannot manufacture a theorem.
- **The progress pane is the feedback half of the loop** (§8.5). After every
  accepted move it says what the new goal matches, what rule now applies, or
  that nothing fired. Marked as heuristic; it never enters the kernel.
- **The obligation pane is first-class**, not a log. It is the visible form of
  the soundness argument and, for this learner, the part of calculus that reads
  like home: *this* is the condition the paper solution passed over. Regularity
  obligations are real entries in it (§6.9), and §12.2's modelling admission
  appears here by name.
- **The move strip carries the moves and the ladder.** `?` `??` `???` `!` are
  §2's four rungs. `~ probe` is the speculative check of §8.6. **`auto` and
  `solve` are absent in v1** — not greyed out, absent, because a greyed-out
  button is an invitation to want it.
- **The status line reports the rung you reached and `0 machine-checked`.**
  The first is the number §17's gate is about; the second is honest about §14
  and stays visible until a verified rule table exists, at which point it
  becomes `9 proved · 3 cited · 0 axiom` with `cited` coloured apart from
  `proved`.
- **Cancellation is a first-class control**, because exploring cheaply means
  being able to abandon a step that is taking too long, and because §16.2 names
  normalisation speed as the one real performance risk. The server enforces a
  per-step timeout and reports it as a *timeout*, not a failure — a step that
  ran out of budget has not been refused.
- **Persistence** is a file per problem under the working directory, plus
  explicit export/import — **the whole tree, including the dead ends**. Scripts
  and trees, never theorems; everything is re-checked on load.
- **Problem files** are plain `.json`, one per problem — statement, formal
  goal, answer schema, declarations. They are authored, not generated.

---

## 17. What it costs, and what would kill it

### Order of work

Revision 2 re-ordered revision 1's stages twice: first for evidence, then —
after §1 was rewritten — for what the tool is actually **for**. The second
re-ordering is the larger one. Revision 1 built the kernel first and treated
the palette and the recognizer as stage-1b garnish. Under §1 those *are* the
product, and the kernel is what stops the product from lying.

**Stage 0 — try to encode goals against §5.1 and §6 as they stand, and list
what breaks. No code, before anything else.** Write goals and their reference
proofs; every place the language cannot express one, or the rule table cannot
close one, is the output. **The output is a gap list, not a number.**

*Revisions 2 through 5 called this "measure the authoring rate" and made the
authoring rate the single most decision-relevant quantity in the plan.
The first pass (2026-09-22, `STAGE0.md`) retired that framing.* The course
supplies a worked solution for every problem, so the mathematics is given and
what remains is **encoding** — which can be drafted mechanically and checked
against SymPy in the build-time oracle role §15.5 already allows. A rate
measured that way measures whoever does the typing, and prices nothing.

**What the gap list is worth, and why it does not depend on the drafting being
trustworthy.** Fifteen goals produced seven gaps, three of them folded into
§6.3, §6.4 and §6.5 above and two of those design defects rather than missing
table rows — including a `ftc` that could not close ∫₀¹ √(1−x²), an entirely
ordinary integral sitting under one of §8.5's own recognizer rows. None of that
required the surrounding proof scripts to be correct: a missing `ln_e` is
missing whichever way the step around it is written, and an unstatable sec²*u*
is unstatable regardless. Gaps are facts about the grammar and the table, and
they are checkable by anyone against §5 and §6.

**Spread the goals across shapes**, not across one unit: a bare definite
integral, one needing a substitution, one carrying a nontrivial domain
obligation, one with an answer schema, one ODE, one improper, one with an
endpoint degeneracy. Shape is what exercises different parts of the table, and
provenance is not — the corpus nearest to hand is unit 00's lettered parts, and
that is a convenience rather than a premise. A sample weighted toward unit 00's
dimensional analysis and ODE classification exercises §6.6, which is stage 2,
while stage 1's target is unit 00's *quadrature* cases.

**Stop when the gaps stop, and do not author past a known-wrong rule.** Goals
authored against a rule already known to need correcting are wasted, so each
pass ends when its findings are folded rather than when a count is reached.

**Stage 0 ran to completion on 2026-09-22 and is closed** (`STAGE0.md`).
Three passes, **forty-one goals, fourteen gaps**, four of them design defects.
The rate fell and then stopped falling: four gaps from the first five goals,
three from the next ten, three from the next fifteen, three from the last
eleven — and the last pass was the narrowest of the three, one component and
one shape of integral, so the rate per unit of ground covered stopped
improving. That is the signal to stop, not the count.

**What stage 0 cannot do, and neither can anything before stage 1 — which is
now the argument for going there.** Nothing checks the *encodings*. SymPy settles the mathematics and says nothing about
whether an obligation list is complete, which is exactly where §11.2's three
errors lived. §1 is explicit that the learner has no calculus fluency, so
reviewing a drafted encoding by eye is a weak check made by the wrong reviewer.
**The right reviewer is the kernel**, where a reference proof can be run rather
than read. So checking the encodings waits for stage 1's headless kernel, and
stage 0 gives a cheap early answer to *do the rules work*, which is the
question that was actually blocking.

**Stage 0b — drive Iscalc/HolPy before writing the API. Closed, 2026-09-21 and
2026-09-22; findings in §4.2.** §16's three tiers make it the nearest neighbour
architecturally as well as intellectually, down to the implementation language,
which is what turned it from background reading into the obvious thing to try
first.

**What it returned.** Their step protocol resends the whole file per move — a
counter-example for §16.3 rather than a model. Their side-condition automation
is weaker than their paper: two of three traps went through the kernel as false
results, including FTC across a pole, which is the error their own paper holds
against Maple. **Hence the verdict: reimplement the core rather than reuse it**,
with four things taken as inputs to weigh and none as code under §15's line.
Their interaction was judged clunky and is not a source of inspiration for
§16.4 — but §4.2 records why that is a verdict on HolPy and not on §16's
request-per-move boundary, which stands on its own argument. Their 183-problem
corpus is filed as a pointer whose trigger is wanting a benchmark.

It also answered, with use rather than with a paper, the question that should
not be dodged: *is this project worth starting, given that thing exists?* Yes,
and for a sharper reason than the paper gave. The expectation was that their
trust story would be weaker — >1,000 HOL Light statements ported, ~40% proved,
the FTC itself unformalised — and that they would lack `check` mode, dimensions,
certified numerics and anything like §8.5's recognizer-and-progress loop. All
true. What a day of use added is that **the soundness property §15 exists to
provide is absent from their kernel's own rules**, not merely unproved, which
is the difference between a weaker version of this and a different thing.

**Stage 0c — the `ring` spike.** Sparse polynomials over ℚ[atoms] as
dictionaries of exponent tuples, `field` normalisation *emitting its
nonvanishing obligations*, run against §11.2's flagship residual. This is the
one component whose bug is a false `Proved` rather than a rejected step, the
one where no library can be borrowed because none emits obligations, and — per
§15.5 — the one where a one-line reach for SymPy would end the project's claim.
It is also where §16.2's performance risk lives.

**Stage 0c closed on 2026-09-23** (`spike/ring/`, with its own README).
`ring` and `field` come to ~370 lines of code. There are 28 tests, including
property tests that check every verdict against exact rational evaluation,
and they catch each of four planted false-`Proved` bugs. It answered both of its
questions:

- **Does the design work?** Mostly. It also corrected the flagship: §11.2's
  `rewrite sqrt_sq_val` cannot fire, so `field` takes facts (§6.2, §11.2).
  Five smaller corrections went to §5.3, §6.2 and §6.3.
- **Is it fast enough?** Yes, by at least an order of magnitude on every
  corpus-shaped case (§16.2, §18 Q18).

**The recognizer table follows the headless kernel, not the other way round**
(revision 8). The table had been listed as the next thing after 0c because it
is content and can be written without code. The recognizer spike showed that
writing the rows is the cheap part, and that what makes them work is matching
on normal forms, which needs the kernel. A table written first could be scored
only by eye. One written second is scored mechanically on the held-out corpus.

**Stage 1 runs headless first, then grows a client.** Terms, `ring`, `field`,
`deriv`, `ftc`, domains and obligations, driven over the §16.3 API against
§11.1 and §11.2 before the panes exist. That is where the central bet either
holds in code or does not — and with §16's shape it is not a separate harness,
it is a script against the API that stays as the regression suite.

**What is deliberately *not* in stage 1**, and each of these was in revision 1's:
`auto` and `solve` (§2 — the decision is pedagogical); the bespoke integrator
(§8.2); certified numerics (§10 — replaced in v1 by the floating-point
speculative probe of §8.6); the full §6.9 regularity table (only the C⁰/C¹ subset `ftc` needs); dimensions
and `buckingham`; and the series and limit rules.

**Fourier–Motzkin with its Farkas witnesses is back in stage 1** (owner's
decision, 2026-09-24). Revisions up to 10 deferred it to stage 4, on the
claim that hypothesis closure, by-range, sign certificates and simple
interval propagation "cover the obligations the target problems actually
raise". The proof-of-life refuted that claim. The `linear` method is what
closes `0 ≤ pi/2` from `pi_pos`, `1 ≤ e_const` from `e_gt_one`, and
`t ≥ 0` on [0, π/2] from the range and π's sign together. An FM
implementation already exists, untrusted, in the tagger. So stage 1 builds
§5.3 method 3 as written:
- the untrusted FM searches and emits the Farkas combination;
- a small trusted checker verifies it, after the constraint set's
  satisfiability pre-check.

That check is smaller and easier to audit than the interval propagation it
replaces, which is no longer planned.

### Size

**Revision 10 removed the line estimates this section carried**: a
per-component table, its stage-1 total and the later stages' figures. They were
budgets rather than arguments, and nothing in the plan depends on them. What
stays is what each stage contains, and the order.

**Stage 1 — the exploration environment.** Target: readiness **P1, P3, P5**
worked in the loop, plus unit 00's quadrature cases, which need no numerics.

- **Kernel:** terms, equality, substitution and the matcher; `ring` / `field`
  / `norm_num`, with `field`'s obligations; `deriv` and §6.3's table; `ftc`,
  the forward moves, the obligation tracker and discharge; the C⁰/C¹ subset of
  regularity `ftc` needs (§6.9); `abs` in goals (§5.1); `diverges` and its
  rules (§5.2); the parser, the KaTeX printer and the round-trip property test.
- **Assistance:** the palette, antiderivative card, recognizer and progress
  signal (§8.5); residual reporting and the three kinds of stuck (§8.7); the
  speculative probe with floating-point quadrature (§8.6); the factoriser and
  partial-fraction solver, `ring`-verified; `trig_norm` (§8.9); the attempt
  tree, session state and §16.3's API.
- **UI:** three panes, tree rendering, stepping and retraction, the ladder,
  and the `./calc` entry point with vendored KaTeX and no dependencies.

Stage 1 also carries the symbolic falsifier bank and the recognizer corpus
(below), and authoring readiness P1–P5 and unit 00's quadrature cases. Both are
content rather than code.

**The first useful landing has landed** (revision 10): the headless kernel
proving §11.1 and §11.2. `WHAT.md`'s proof-of-life built `ring`/`field`,
`deriv`, `ftc`, terms, the matcher, the parser, `close`, the P1 rules from §6.8
and handles against readiness P1, with discharge stubbed, in `kernel/`. The
rest of the kernel list — real discharge, `int_subst`, regularity, `abs`,
`diverges` — and everything under assistance and UI are still to do.
*(Revision 10, int_subst: real discharge and `int_subst` have since landed, and
P1.1 proves from the sheet's own goal. Regularity, `abs` and `diverges` remain.)*
*(Revision 10, consolidation: so have `int_flip`, one orientation rule for
every step and the non-strict sign product, and ∫₀¹ √(1−x²) by x = cos θ
proves, §13. The list that remains is unchanged.)*

**Against revision 4's OCaml plan**, Python is simpler to write for exactly this
shape of code — dictionaries of exponent tuples, pattern dispatch over a term
type, a small HTTP layer — and the parser, the server and the build story are
each meaningfully simpler. What that simplicity costs is stated in §16.2 and
should not be forgotten: no type checker over the term language, no enforcement
of §15.3, and a verified kernel that would be a rewrite rather than a module
swap.

**The remaining uncertainty was `ring`/`field`, not the toolchain.** No library
emits nonvanishing obligations, so nothing outside the spike exists to copy,
and it is the one component whose bug is a false `Proved` rather than a
rejected step. It is also, per §15.5, the one place where a one-line reach for
SymPy would quietly end the project. *(Revision 10: it is built, promoted from
the spike, and property-tested against exact rational evaluation.)*

**What comes after, if stage 1 earns it.**

| Stage | Contents |
|---|---|
| **2. Certified numbers** | `enclose()` over MPFR, precision policy, interval extension and composition, `approx`, the certified probe and `quad_verified`, series and limit rules, dimensions and `buckingham`. Target: **unit 00 complete**, and readiness P1 including its five significant figures |
| **3. The integrator, then `auto` and `solve`** | table, derivative patterns, substitution heuristics, parts with cycle detection, the rational tier reusing stage 1's factoriser; then the search layers §2 prepared for |
| **4. Kernel completion** | the full §6.9 table, the ODE solver (§8.3) |
| **V. Machine-checked rules** | *deferred and unbound from any prover* (§14) — the rule table stated and proved in a prover, provenance tags, the assumption whitelist. 80–110 lemmas, most of them `cited`. **(A) only**; a verified kernel is §18 Q19 and is not planned |

Stage V is conditional spend, not planned spend, and the library install and
two-lemma spike come with it rather than before it.

**What matters is the order, not a total.** **The thing §1 says is the product
arrives in stage 1, and the two most expensive components in the document —
the integrator and the certified numeric kernel — arrive after the question
"does this actually help?" has an answer.**

### The dominant cost is not the code

It is authoring the formal goal for each problem — **and the unit is the
lettered part, not the problem.**

*Stage 0's re-framing changes part of this, and this section states the old
position first and the correction after it.* The counting below is unaffected
and stands. What is affected is where the work lies: drafting an encoding
turned out to be mechanical once the course has supplied the mathematics, so
the real work is **review**, not authoring — and review needs a kernel to
review against, because §1's learner cannot check an encoding by eye.

§12.1 authors `unit00.P1.a`: one part, one
goal, one answer schema, one proof script. Unit 00's P1 has parts (a)–(e), five
different ODEs needing five classifications and five quadratures, and they
cannot share a goal. Unit 00 is 11 problems but **42 lettered parts**; units
00–07 are ~347 parts against 98 problems, a factor of ~3.5 that revision 1
missed by counting problems.

Two things pull the other way. Parts within one problem share their
`var`/`fun`/`assume` declarations and physical setup, so the marginal part is
much cheaper than the first. And **count only the targets this document
commits to**: stage 1 is readiness P1/P3/P5 plus unit 00's quadrature cases, stage 2 is
unit 00 complete. That is a small fraction of what revision 1 counted,
which covered work nobody has agreed to do. (Its supporting figures were also off: units
00–07 are 8 of 41 units and 98 of 512 problems, a **fifth** of the course, not
a third.)

The good answer to the cost is unchanged and is strong:

> The course already contains a complete worked solution for every problem —
> verified, 512 solutions to 512 problems, 1:1 in all 42 sheets, unit 00's
> averaging ~420 words of carried algebra with a "Check." paragraph. Author the
> formal goal *and a reference proof* from that solution, and check it. Where
> the reference proof fails, either the encoding is wrong or the course's
> solution is. Authoring is **transcription, not re-derivation.**

**"Transcription" overstates it, and stage 0 is where that showed.** What the
solution hands you is the *mathematics* — you do not have to find F, do the
partial fractions, or discover where the integrand blows up, and that is the
true and load-bearing half. What is left is the **encoding**: which rule the
step is, which obligations it emits, whether a domain condition closes by range
or as a product of two earlier facts. That is judgement, and §11.2 is this
document's own evidence for how much — three of its obligations were **wrong
rather than loose**, one of them provably so, and no one transcribed their way
into those errors. The claim to keep is that the *mathematics* is given. The
claim to drop is that what remains is clerical.

Two legs of that stand. **The third is deleted.** Revision 1 said the
formalisation pass "doubles as a mechanical verification pass over the course,
which is work `WHAT.md` lists as outstanding anyway". It is not: `WHAT.md`
records "2026-09-20: **all 41 units written and verified**", and for units
00–03 that an independent agent re-derived every worked example, checked every
number numerically and fixed 83 defects. That is the record of a pass that
already ran.

**One cost revision 1 did not have, because the component did not exist:** the
recognizer table is *content*, not code, and its rows have to be right. That is
the integration-techniques chapter transcribed and indexed by syntax, and it is
the part of stage 1 where the work pays most.

### The falsifier bank, and the recognizer corpus

**The bank** is the main empirical evidence for the soundness claim while §14
is deferred (§15.4), so it is generated rather than hand-written: **one
falsifier per rule side condition, mechanically, from the rule table.** Coverage
then tracks the table instead of the author's imagination.

Thirty **symbolic** wrong solutions, all of which must be rejected — a dropped
factor of 2, a sign error, √(*t*²) → *t* over a range containing negatives, an
antiderivative with a pole inside the range, *x*/*x* → 1 at 0, a crossed branch
cut of `atan`, a divergent integral closed by FTC. Plus, each closing a gap the
review found:

- **The other direction.** Thirty must-reject cases and no measurement of
  acceptance is a bank that a kernel rejecting everything would pass. Add
  correct antiderivatives that must be **accepted**, in several equivalent
  forms of the same answer (π√3/9 and π/(3√3) must both close), and record the
  fraction `field` closes unaided. The 183-problem corpus of §4.2 is available
  for this and comes with known verdicts.
- **The rule-statement cases found by reading**: a reversed-limit `sqrt_sq`, a
  reversed-limit `ln|u|`, a non-monotone `int_subst`, an ODE uniqueness claim
  past the blow-up time (ẋ = x², x(0) = 1, on [0,2]), a pendulum with θ₀
  omitted, rewriting `D[x] sqrt(x^2)` with `sqrt_sq` under `D[x]` (§6.1,
  revision 9), and both spellings of the negative-exponent pole
  (∫_{−1}^{1} −x^(−2) and ∫_{−1}^{1} −1/x²). *A bank that tests one spelling of
  a term is testing the author's habits.*
- **The four brand cases** of §15.3 — a fabricated judgement, a prototype-forged
  one, a structured-clone round-tripped one, a direct write to the tracker.
- **The parser/printer round-trip property** (§15.6), the only thing standing
  behind the parser's irreducible place in the trusted base.
- **A numeric arm, deferred with stage 2**, since the components it tests do not
  exist in v1: a truncation rounded inward, a Taylor remainder one term short, a
  dropped tail bound, near-tolerance `approx` calls. An enclosure **narrower**
  than the truth rejects nothing and silently certifies a wrong fifth
  significant figure, which is the opposite failure mode from everything above.

**The bank must carry the forward moves, because the authored corpus will not**
(stage 0, `STAGE0.md` gap 5). `ftc` collapses the substitution: a goal whose
learner-facing solution is "substitute u = x²" closes in the reference proof by
handing F = exp(x²)/2 straight to `ftc`, with no `int_subst` step anywhere.
That is §6.4's keystone working exactly as designed and it makes authoring
cheaper — and it means a corpus of authored reference proofs **systematically
never exercises `int_subst`**, the rule with the most delicate hypotheses in
this document and the one HolPy got wrong in two of three probes. Authored
goals test the kernel's *checking*; they do not test the *moves*. The bank is
where the moves get tested, and generating one falsifier per side condition
already reaches them — this is the note that it must, and that nobody should
read corpus coverage as move coverage.

**The recognizer corpus is a separate and equally important acceptance test**,
and it is new in this revision because the component is. A recognizer that
names the wrong technique is not a soundness bug — the kernel still refuses the
bad step — but it is a failure of *the product*. The test is mechanical and the
course supplies it: **for each integral in the target corpus, does the
recognizer name the technique the course's own worked solution uses?** Record
the fraction. That number is the honest measure of whether §8.5 is doing its
job, and it should be published beside the soundness bank rather than folded
into it.

**Measured, 2026-09-23 (`spike/recognizer/`).** Twenty-two integrals from
readiness P1/P2/P5 and unit 00 were each labelled with the technique the
course's hint or solution names, with the line quoted. §8.5's table as it
then stood scored **15/22**. Five rows fitted to the misses scored 22/22. On
**nine integrals held out from units 01–10**, both scored **3/9**. The fitted
rows fixed their own examples and nothing else, which is what a long tail
looks like, and it changes what the test must be:

- **Score on a held-out set, and never tune on it.** A table scored only on
  the corpus it was written against measures its author's reading. Hold back
  units the rows were not written from, and publish that score as the number.
- **The cost is matchers, not rows.** Each row is a few lines. The held-out
  misses came from matching the written form and from the missing chain-rule
  row (§8.5). Both need `ring`/`field` normal forms and the constant-ratio
  test, which is why the table follows stage 1's kernel (below) rather than
  preceding it.

### The gate: does the loop actually teach?

Revision 1's behavioural falsifier asked whether `solve` gets pressed on
everything. With `solve` deferred (§2) that question is deferred with it — and
a better one takes its place, because §1 now makes a claim that is falsifiable
in a few weeks of use.

The claim is that this is **a fluency trainer, not a fluency substitute**. The
instrument is already in the work log: every proof records how far up the hint
ladder it went.

> **After stage 1**, work readiness P1–P5 and unit 00's quadrature cases in
> order, and plot the maximum rung reached per problem against time.
> **Pre-register the threshold now, before the work:** *if the average rung
> over the last third of the corpus is not below the average over the first
> third, the tool is a crutch rather than a trainer and §1's central claim has
> failed.*

That is a real falsifier: it can come out against the project, it costs nothing
to instrument, and the answer arrives at the end of stage 1 rather than after
stage 3.

What to do if it fails is not "stop" but "**stop building this one**": a tool
that reliably gets you the answer without building fluency is still useful, and
the honest response is to finish the integrator, ship `solve`, call it a
verified CAS front end, and drop §1's claim rather than keep asserting it.

A second, softer reading is worth recording at the same time: **which rung gets
used most.** If it is rung 0 — the palette alone — the recognizer is carrying
the project and the ladder was over-engineered. If it is rung 3 throughout, the
recognizer's rows are too coarse to be actionable and want splitting.

**Both readings assume the recognizer fires.** Where no row matches, rungs 1–3
show nothing, and the reading measures coverage instead of learning. The
recognizer spike had no row firing on four of nine held-out integrals. So **the
recognizer's held-out score on the gate's own corpus is measured before the
gate is read**, and problems where no row fired are reported separately
rather than averaged in.
### The risk that is not technical

**Building the checker is more interesting than unit 00, and will stay that way
for about four months.** This is a fact about proof-assistant projects, not
about anyone's character. It is an estimate of how long the motivation
lasts, not of how long the work takes, and it is the real argument for the ordering above: get the
loop running against readiness P1 inside that window, because that is the
evidence that arrives while you still want it.

It is also the argument for §14's deferral, stated once more in its sharpest
form: **the worst outcome in this plan is not an unsound kernel, it is a
pile of Rocq proofs about a tool that nobody opened.**

---

## 18. Open questions

Revision 1 asked six. Revision 2 kept them, sharpened two and added six the
review raised. Revision 3 retired one — the default mode, which §1 settles —
and added four that the exploration framing opens. Revisions 4 and 5 add four from
the change of language and deployment, and reopen Q7.

1. **When does the integrator get switched on?** §8.2 wires the interface in
   v1 and leaves the proposer off. The flag should be flipped deliberately,
   after §17's gate has had a fair run, rather than on the first frustrating
   evening — and the deliberate part is the whole of the question, since
   flipping it is one line.
2. **How far to take the integrator?** The rational tier is complete for linear
   and irreducible-quadratic denominators and covers every partial-fraction
   problem in this course; past that the bound is the **output language**
   (§8.2), so extending it means a grammar extension first, hence the parser,
   hence the trusted base. Risch is a large lift for a small return on this
   syllabus. The stopping point wants choosing deliberately rather than
   discovered by drift, and §17's bank supplies the number to choose on.
3. **Does the obligation pane get looked at?** Note this asks about the
   **display**, which costs UI space — not about the **recording**, which costs
   nothing and which §17's gate depends on. Revision 1 conflated them while
   also saying the record "never blocks anything".
4. **First-order was the right call for 00–15. Does it survive 19?** Fourier
   and Sturm–Liouville want functions as objects, inner products and operators.
   Either a second sort, or those units are out. Decide before any extension
   work, not during.
5. **Is `leibniz` worth its obligation?** Differentiating under the integral
   sign appears in readiness P7 and in units 11, 20, 21. Its uniform-domination
   condition is the one place the scalar language genuinely strains. Possibly
   better as a `cite`d library lemma with the domination supplied as a witness
   function.
6. ~~**Where does it live when it graduates?**~~ **Settled, revision 6:
   `tools/`, with the course pointing at it.** The question offered two
   options — `tools/` if it becomes a thing that is installed, or inside
   `mechanics-to-relativity/` if it becomes part of the course — and the answer
   is neither exactly: **this is a tool in its own right, and someone
   undertaking the course should have it at their disposal.** So it is its own
   artefact in its own repository, and the course *references* it.

   **The direction of that reference is the whole content of the decision, and
   it is one-way: course → tool.** Living inside `mechanics-to-relativity/`
   would put §1's boundary under permanent pressure, because everything in a
   course directory is answerable to the course; a tool the course merely
   points at is not. This is the same shape as the workspace's `_docs/` rule —
   the pointing goes one way and nothing on the far side may point back.

   **One consequence, and it is a deliverable rather than a note.** If the tool
   is its own artefact, the course problems are **content it loads**, not part
   of it — a separable problem-file package. §1's replaceability test already
   demanded that (*replace the course and only the problem `.json` files, §13's
   coverage claims and §8.5's row priorities change*); this gives the demand a
   shape, and §16's `./calc` has to take a corpus path rather than assume one.

   **What the decision does not do is publish it.** Its own repository means
   publishing is a later and separate choice, which is the part
   `courses/PUBLISHING.md` cares about — and the licence question stands
   unchanged whenever that choice is made: **MPFR is LGPL** (§10), and it
   arrives with stage 2, not stage 1.
7. **Which prover for the rule table?** Coquelicot, mathcomp-analysis, or Lean
   4 + Mathlib. Revision 1 chose Rocq on incumbency and tooling-in-hand rather
   than by argument, and none of the relevant libraries is installed here
   (§14). Settled by a two-lemma spike, and only worth doing if stages 1–3
   survive their gate.
8. **Complex numbers as a sort.** Unit 06's P2, P10 and P12 need them, unit 20
   is built on them. Separate from Q4: that one is about *order*, this one is
   about *sort*. Not a stage-0 gate — no stage-1 or stage-2 deliverable
   contains a complex number.
9. ~~**limsup, and the other things that live only at an endpoint.**~~
   **Deferred with a trigger, revision 6 — case by case, not a general
   treatment.** `oo` earned its own syntactic class because it appears in
   *three* constructs: `Int` limits, `Sum` limits and `lim` targets. A general
   mechanism paid for itself there. `limsup` would appear in **one** place, the
   radius of convergence, and §6.7 already replaced `radius_limsup` with a
   ratio-form rule that covers the corpus and survived review. **One use does
   not justify a sort**, and building the general treatment now is the
   premature commitment this document declines elsewhere.

   **The trigger to revisit:** a *second* endpoint-only construction arriving,
   or a target problem whose **statement** — not its proof — requires `limsup`,
   `liminf`, `inf` or `sup` as a value. Neither is in stage 1 or stage 2. If
   the trigger fires, generalise then, with two instances to design against
   instead of one.
10. ~~**What is `abs` for?**~~ It currently appears only in side conditions
    (§5.1), which costs unit 00 P7 and forces §8.5's `f′/f` row through
    `cases`. The alternative is `d_abs (u # 0)` plus a C⁰-only regularity
    entry and a `cases` discipline. Cheap either way; not free.
    *Stage 0 (`STAGE0.md` gap 7) gives it a one-line price:* **∫₋₁¹ |x| dx
    cannot be written down** — not unprovable, unstatable, which is a harsher
    failure than the rest of §13's limits and the one a learner meets first,
    since they meet it at the keyboard rather than at a refusal. Worth
    deciding before the parser is built (§17 stage 1), because the answer
    changes the grammar rather than the table.
    **Settled, revision 6: `abs` is admitted to goals** (§5.1), with `d_abs`
    in §6.3 and `abs_nonneg`, `abs_neg`, `abs_pos` in §6.8. It costs no
    decidability claim — §6.4 never had one — and unit 00 P7 comes back into
    scope.
11. ~~**Negatives.**~~ **Settled, revision 6: the `diverges` judgement is in**
    (§5.2), for `Int` and `Sum`, with `div_limit`, `div_compare`, `div_power`
    and `div_pole` in §6.4 and the series duals in §6.7. **Not general
    negation** — no `¬`, no negation-introduction, no excluded middle relating
    it to `conv` — and never a term, so `ring` and `field` are untouched. The
    four target problems come into scope, and the larger gain is that the
    FTC-across-a-pole error becomes **refutable** rather than merely
    unprovable, which is the trap §4.2 found HolPy failing.
12. **When does §14 actually get done?** The deferral has two named triggers
    (§14). This question is whether a third should exist — a calendar one — or
    whether "when the tool has earned it" is a stable answer. The risk of no
    calendar trigger is that `0 machine-checked` becomes permanent furniture;
    the risk of one is doing the work for the deadline rather than the tool.
13. **Is the progress signal's `worse` verdict safe to show?** §8.5 names one
    known false negative — parts with a cycle, which must get worse twice
    before it closes — and suppresses the warning for that row. Nothing
    guarantees the list of such cases is complete, and a signal that
    discourages a correct move is worse than no signal. Options: show only the
    positive verdicts, show `worse` without emphasis, or collect the false
    negatives from the corpus before deciding.
14. **Does the attempt tree get used, or does everyone work linearly?** It
    costs UI space and complicates the state model, and it is justified twice
    over (§16) — but so was the obligation pane's display, and Q3 asks the same
    thing about that. Instrument it: count forks per problem.
15. **Is the recognizer's granularity right?** §17's gate records which rung
    gets used most. Rung 3 throughout means the rows are too coarse to act on
    and want splitting; rung 0 throughout means the palette alone was carrying
    the project and the ladder was over-engineered. Both are cheap to fix and
    neither is decidable in advance.
    **Partly answered, revision 8:** the first problem is not granularity but
    reach. The spike's rows were fine-grained enough wherever they fired, and
    rung 3 was specific enough to act on. What failed was firing at all
    (3/9 held out), for reasons more rows do not fix (§8.5, §17). Granularity
    stays open until coverage is good enough to measure it.
16. **Local-only, or hosted?** §16 decides local for v1 — `./calc` on
    localhost, single user, no accounts, no network — on the grounds that
    hosting adds auth, multi-user persistence and a service to maintain, for a
    tool with one user. It is easy to add later and impossible to remove, so
    the decision is deliberately recorded as reversible rather than settled.
17. **Does the request-per-move boundary hold up under §1's loop?** Localhost
    round trips are sub-millisecond and §16.3 batches the progress signal and
    the probe into the step response, so the arithmetic says yes. The
    arithmetic said yes about a lot of things. §17 stage 0b is there partly to
    find out by feel rather than by calculation.
18. ~~**Is `ring`/`field` fast enough in Python, and if not, where does it
    go?**~~ **Settled, revision 7: yes, with room to spare.** Stage 0c
    measured every corpus-shaped case at least 10× inside §8.6's 100 ms,
    §11.2 in about a millisecond (§16.2). The budget breaks only on 64+
    distinct denominator factors, or on a trivariate expansion of degree 16.
    If that is ever wrong, the order of escape is unchanged: `gmpy2` for the
    arithmetic, then a compiled normaliser behind the same interface.
    **Trigger to reopen:** a real problem, rather than a synthetic one,
    over budget.
19. **(B), ever?** A kernel written in a prover and extracted — verified
    `check_step`, verified `ring` — is a genuinely different project and this
    document does not plan it. Worth recording that the parser sits
    permanently outside it (§15.6), so even (B) leaves a trusted component
    behind, which is an argument for (A) being the sensible stopping point.
20. **What does `check` mode mean before stage 2?** Without the certified
    enclosure it can prove an exact answer and cannot reject a numeric one, so
    a wrong answer is indistinguishable from an unfound proof (§13). Is a v1
    `check` that can only ever say "yes" or "I don't know" worth shipping, or
    does it wait for §8.6's certified probe?
21. ~~**What does `rewrite` match modulo?**~~ **Settled, revision 10: the
    default below, as trialled, with every occurrence rewritten when no
    position is given (§6.1, `kernel/p1_expected.py` E1–E2).** Both P1 scripts
    were written out this way before any code, and the kernel runs them.
    *(Revision 9.)* `ftc` substitutes
    the endpoints literally, producing `ln(1+0)`, `atan((2*1-1)/sqrt 3)` and
    `sqrt(pi^2/4)`. None of these is syntactically the left-hand side of
    `ln_one`, `atan_one_sqrt3` or `sqrt_sq`, so §11.2's own rewrite step fires
    nowhere under a purely syntactic matcher. The matcher is trusted (§15.2),
    so this belongs in the design and not in the code. The default the
    proof-of-life trials:
    - the rule is instantiated explicitly (`rewrite sqrt_sq (u := pi/2)`);
    - it is accepted when the instantiated left-hand side and the target
      subterm agree after **ring**-normalising atom arguments, the congruence
      §6.2 already uses for atom identity (never field-normalising, which
      would need obligations);
    - every §6.8 entry used is pinned by its exact statement.

    Settle it by writing both P1 scripts out step by step before any code.
22. **How does an admission tagged `none` get closed, or refused?**
    *(Revision 10.)* The tagger names the §5.3 method an admitted obligation
    expects, and `none` when no method can close it. Some `none` obligations
    are simply false: `tan(pi/2) − tan(pi/2) ≐ ?A` owes `cos(pi/2) # 0`, and
    no method can decide `cos(pi/2)`, so the kernel admits it rather than
    refusing. Real discharge will close the true ones it can reach. What it
    does with an obligation no method decides — keep admitting it, try §6.8's
    exact values first (`cos_pi_half` would refute this one), or refuse
    anything tagged `none` — decides whether `Proved modulo N` can ever hide
    a false admission.

    **Settled, 2026-09-24: an obligation discharge can decide false refuses
    the step.** Discharge first rewrites an obligation with §6.8's exact
    values, then decides it where it can. Here `cos_pi_half` turns
    `cos(pi/2) # 0` into `0 # 0`, which `norm_num` finds false, so the step
    is refused, just as E7 refuses `0*ln(-1)` for `-1 > 0`. The reason: a
    goal that can only be "proved" through a false admission is a wrong goal,
    and the learner should be told so at the step where it goes wrong. An
    obligation that discharge can decide neither way stays admitted and
    tagged `none`, so it is still visible. Refusing every `none` would also
    refuse obligations that are true but out of the methods' reach.

    **The reading settled with discharge (E33, owner's answers of
    2026-09-24):** an obligation is decided false in three ways, all under one
    code, `obligation-decided-false`:
    - **F1:** it is a false literal after exact values;
    - **F2:** it is closed and its negation is discharged, like the reversed
      range's `pi/2 ≤ 0`;
    - **F3:** a rational counter-point from a fixed, bounded candidate set
      lies in its domain and makes it false. F3 keeps full reach: a goal with
      no stated domain whose terms are undefined somewhere, such as
      `ln x * 0 ≐ ?A`, is refused. Stating `@ x > 0` is the learner's move.
      *(Revision 10, int_subst review, E50: the candidates include the
      rational roots of the obligation's one-variable polynomial pieces, so
      a rational pole inside a range is refused. Irrational roots are still
      missed, §5.3 and §5.4.)*

    The decided-false check can only refuse, so it is untrusted, beside E27.
    Misses of the bounded search stay admitted and tagged `none`.
23. **How will `Int` and `D` state their definedness?** *(Revision 10.)*
    `ring`, `field` and `norm_num` refuse them today, because an opaque atom
    is assumed to denote and nothing yet shows that these do (§5.1). Once
    §6.9's regularity and §5.2's `diverges` exist, the natural former is
    "`Int[x = a .. b] f` owes f integrable on the range" and "`D[x] e` owes e
    differentiable at x". The choice was between stating those as formers,
    like `/`, and stating them only as `ftc`'s and `int_subst`'s premises,
    with the normalisers still refusing.

    **Settled, 2026-09-24: they are formers (option A).** `Int[x = a .. b] f`
    owes "f integrable on [a, b]" where it enters, and `D[x] e` owes "e
    differentiable at x". From then on `ring` and `field` read each one as an
    ordinary atom. Three cases decided it, each run against the kernel as it
    stood, where all three are refused:
    - **Integration by parts that returns the same integral.** I = ∫₀^π eˣ
      sin x gives I ≐ (e^π + 1) − I, and solving for I is `ring` algebra
      on the atom I. Under A, the owed integrability is closed by regularity
      and the algebra goes through. Under premises-only, it needs a
      dedicated trusted rule.
    - **The same algebra on a divergent integral.** I = ∫₁^∞ 1/x with
      I − I ≐ 0: under A it stops at the owed "1/x integrable on [1, ∞)",
      which is false (`diverges`, §5.2). The refusal is then for the right
      reason rather than a blanket one.
    - **An ODE with an unknown function.** Checking `D[x] y(x) − 2*y(x) ≐ 0`
      needs `D[x] y(x)` as an atom, owing y differentiable.

    A is the same discipline E26 applies to `ln`: a term owes its own
    definedness where it enters, and algebra then treats it as a number. It
    lands with §6.9's regularity and `diverges`, stage 1's third piece. Until
    then E26 (b)'s refusal stands as the safe placeholder. *(Revision 10,
    consolidation review, E57: and until then no rule may erase an `Int` or
    `D` node, except where its own premises owe the node's definedness,
    §6.1. The refusal in the normalisers was not enough on its own: a
    `rewrite` that never normalised erased one.)*

---

## What the review established, and how much to trust it

Revision 2 was produced by an adversarial review of revision 1, across eleven
dimensions — soundness, rule table, worked examples, build-versus-reuse in two
halves, coverage against the course, internal consistency, plan and cost,
missing material — plus a completeness pass. 108 candidate findings, each put
to two adversarial verifiers with the document and the course open; 48
survived, most corrected in the process. Rocq checks ran against the `rocq9.1`
opam switch on this machine; JavaScript and Python measurements against Node
26.4.0 and SymPy 1.14.0. The review document has since been folded into this
one and deleted; what follows is the part that does not appear as a correction
somewhere above, because it is about confidence rather than content.

### Attacked and not broken — do not re-litigate these

Each was a deliberate attempt to break a load-bearing claim, and each failed.
They are recorded because the cost of re-deriving them is real and the
temptation to revisit them will recur.

- **§6.4's keystone.** `ftc` as differentiate-and-check genuinely removes the
  integration algorithm from the trusted base. Only the *decidability* wording
  was wrong (§6.4); the asymmetry is not. **Superseded in part on 2026-09-22:**
  the review also called the rule statement "correct and even slightly
  redundant — F ∈ C¹ on [a,b] with F′ = f already forces f ∈ C⁰", and the
  redundancy half is now withdrawn. Stage 0 found that the closed-interval form
  cannot close ∫₀¹ √(1−x²) at all; §6.4 now splits the premises across [a,b]
  and (a,b), and `f ∈ C⁰([a,b])` is load-bearing under that form. The
  keystone argument is untouched — this was the rule's regularity hypotheses,
  not its asymmetry. *It is worth noting where this sat: the endpoint gap was
  one of the three findings the section below flags as **stated as settled and
  not adversarially verified**, and it was the one that turned out to be
  understated.*
- **§15's untrusted-§8 argument.** Six reviewers looked for a path from the
  integrator, the factoriser, the partial-fraction solver, the recognizer, the
  palette or §8.7's residual reporting to `Proved` without a kernel step.
  Nobody found one. The two leaks that existed were elsewhere —
  `quad_verified` and the obligation-discharge procedures — and both are fixed
  above.
- **§6.2's opaque-atom argument.** `ring` is sound *precisely because* it knows
  nothing about `sin`. This should not be replaced by any library. Note that it
  is also what makes §11.2's √3 problem real: the property that buys soundness
  is the one that refuses the flagship obligation.
- **§6.4's `int_subst` hypotheses.** φ ∈ C¹ with *f* continuous on φ([a,b]) and
  no monotonicity is the correct hypothesis set. **Do not weaken it** — the gap
  was only ever in how the domain is derived, which §6.4 now answers with the
  composed integrand.
- **`sep_autonomous` is derived, not an axiom.** Substitute w = v(s), use
  m·v′ = f(v), then ∫₀ᵗ 1 ds = t. The claim was attacked directly and held.
  `energy_integral` is a true theorem, and `period_integral`'s U′ ≠ 0 is the
  mathematically right convergence condition.
- **§6.7 avoids the classic o() trap by construction**, via `big_O` with
  explicit constants and `taylor_lagrange` with an explicit ξ-bound.
- **§9's diagnosis.** Identifying the unconstrained metavariable as a
  *specification* problem rather than a pedagogical one is correct, and it
  would be a problem with no learner present. Only the blacklist fix needed
  work.
- **§3's Richardson statement**, including "adding `abs` is what pushes it
  over", is accurate.
- **§12.2's linear algebra.** Verified: the dimension matrix over (M,L,T) for
  (P, m, κ, a) has rank 3, one group, null space spanned by (1, −½, ½, 0), and
  κ = MT⁻² is the right dimension for a stiffness. The rank half is sound and
  complete; only the physics half needed splitting.
- **§11's mathematics, throughout.** F = 2 sin t − 2t cos t differentiates to
  2t sin t exactly; F(π/2) − F(0) = 2; §11.2's antiderivative differentiates to
  1/(1+x³); the partial fractions A=1/3, B=−1/3, C=2/3 are right; the value is
  ln2/3 + √3π/9 = 0.835648848265, so `0.83565 ± 5e-6` and the enclosure
  [0.8356487, 0.8356489] both hold. **No calculus error, no arithmetic error
  and no bad bound was found anywhere in the document.**
- **§1's quotations are verbatim and in context**, checked against
  `units/readiness/problems.html`. Every problem in the course has a worked
  solution — 512 problems, 512 solutions, 1:1 in all 42 sheets — so §17's
  transcription-not-re-derivation argument is available.

### How much to trust what is stated above

Three findings are stated in this document as settled and **were not
adversarially verified**: the `oo`/endpoint gap (§5.1), unit 00's three missing
pieces of machinery (§5.1, §6.3, §6.8), and the absence of negation (§5.2,
§13). They came from a completeness pass run after the verification rounds.
They are mechanically checkable against the grammar, the derivative table and
the course files, and they are expected to hold — but they carry less evidence
than everything else here.

**One of the three has since been checked, and it was understated.** Stage 0
(2026-09-22, `STAGE0.md`) found the endpoint gap reaching further than §5.1's
framing of it: it was not only that `oo` needed a syntactic class, but that
`ftc`'s own regularity premise was stated on the closed interval and therefore
could not close a bounded, continuous, entirely ordinary integral. §6.4 is
corrected. The other two remain unverified, and the lesson generalises to
them — **a finding from the completeness pass is a hypothesis, and the cheap
way to test one is to try to use the thing.**

Three further items are **judgements rather than findings**, and this document
states them more flatly than the evidence warrants:

- **What the `closed` schema buys** (§9) rests on how much `?A := √π/2·erf(1)`
  asserts. Reviewers split between "nothing" and "considerably less than
  elementarity".
- **`cited` being weaker than it looks** (§14) is confident about the *shape*
  of the gap between a library's hypotheses and what the kernel checks, and
  uncertain about its *size*, since nobody could run Coquelicot here.
- **The MPFR recommendation** (§10) trades a reviewability claim for a
  correctness claim. That trade is a judgement about what §15 is for and it is
  the author's to make. The measurement behind it — the exact-rational blow-up
  — is not a judgement; that part is settled.

**The rule recount is still owed, and the one part now enumerated came in
above every estimate.** Three dimensions recounted independently and got
**~80, ~100 and ~110**, differing over whether to expand "limit laws", whether
§6.8's table is 20 entries or 45, and whether §6.9's regularity rules count
against the same figure. §14's cost cannot be priced until the table is
enumerated. **On 2026-09-22 §6.8 was enumerated on a stated basis and came to
70** — more than either figure the counters argued between, which means the
disagreement was not between a high and a low reading of the same table but
between three readings all below it. The remaining two disputes are untouched.
What the exercise established beyond the number is that **a stated basis is
what turns this from an argument into a count**, and §6.8's basis is now in
§6.8; the other sections still need theirs.

**What the kernel now checks, and what it does not (revision 10).** Every
obligation list in §11 is now what code emits, asserted against a list written
by hand before the code existed, and the rule statements of §5.1, §6.1–§6.4 and
§6.8 that P1 exercises have been run rather than read. That is more evidence
than any earlier revision had. But discharge is stubbed, so no obligation's
*truth* is checked, and the tags that name how each would close are untrusted
guesses. And the milestone's review and attack rounds never came back clean:
each upheld findings, and the last round's fixes were applied and re-run but not
reviewed again. The late findings were almost all bugs planted to test the
suite that it failed to catch, fixed by adding tests without changing what the
kernel does.

**A false `Proved.` reached the committed kernel, and review caught it before
any push** *(revision 10, consolidation review, 2026-09-24)*. The
consolidation build passed its whole suite and was committed. The skeptic
given it then found `rewrite pyth` erasing `D[x](abs x)`, and likewise a
divergent integral, and `close 1` reporting a plain `Proved.` with nothing
owed (§6.1, E57). It also found two gaps in the new orientation rule: an
enclosing range used without its order decided, and orders decided eagerly
at 30 s for a range nothing used (§6.4). Nothing had been pushed. The fix is
committed with both reproducers as must-refuse cases, and an independent
second review of the fix found no false `Proved.` and four minor points,
two of which became the refusal of trees in limits (§6.4) and `0^0 = 1`
(§5.1). **What it says about the evidence is the part to keep.** The suite
was green on a kernel that could prove a falsehood, because a suite checks
what was specified, and nobody had specified that a rewrite may not drop a
term. The adversarial review is what found it. **A green suite is evidence
about the cases written down, and a clean adversarial review is the stronger
signal**, however large the count of checks.

**One thing worth reading, and it is optional.** Waterproof (TU Eindhoven,
arXiv:2606.01875) is the closest existing artefact to the *interaction* §16
describes, and its published course evaluations are the only real evidence
anyone has about whether a tool like this gets used. Revision 5 called that
worth reading before stage 1. **Revision 6 demotes it**, because the question
it answers is not this project's falsifier. Adoption evidence for the general
class would matter if the case for building this rested on other people picking
it up. It does not: the tool is an addition to `mechanics-to-relativity` for
anyone working through it, and its own falsifier is §17's gate — *does the
average hint rung fall* — which is measured on use, not on uptake. Read it if
the interaction design stalls and a second example would help; do not treat it
as a gate.

---

## Colophon

**Read before stage 1**, in this order: §4.2's nearest neighbour — the CADE
2021 paper and the HolPy repository, for its rule set, its side-condition
automation and its 183-problem corpus with known verdicts, which §17 stage 0b
made a day of work and has since closed; and the section above on how much to
trust what is stated here. **Optional, not before stage 1:** Waterproof's
published course evaluations, which are adoption evidence for the class rather
than evidence about this tool — see the note above for why that is not a gate.

**Revision history.** Revision 1 was the original proposal. **Revision 2**
folded in the adversarial review, cut the scope to readiness P1–P5 plus unit
00, deferred verification, and corrected the numeric representation and the
term language. **Revision 3** rewrote §1 around who this is for, promoted the
recognizer and the palette to the product, added the progress signal, the
speculative probe, the attempt tree and the hint ladder, moved `auto`, `solve`
and the integrator out of v1, and removed the coupling between the course and
the tool's design. **Revisions 4 and 5** decided the implementation language
and the deployment.
Revision 4 chose OCaml on an extraction argument and rewrote §14, §15.3 and §16
around it; revision 5 withdrew the premise, settled on **Python in three tiers
with a browser UI**, separated (A) verified rules from (B) a verified kernel in
§14, reopened the prover question, and added §15.5's prohibition on SymPy in
the kernel. §17's estimate fell to ~3,900 lines (since ~4,300, with §8.9, `abs` and
`diverges`). No rule, no
judgement form and nothing in §15's claim changed across either. **On
2026-09-21** a first pass of stage 0b added §4.2's findings from driving HolPy
and its verdict: reimplement the core, with four things from HolPy to take into
consideration. Nothing else changed.

**Revision 6, 2026-09-22.** Three things happened on one day: the decoupling
test was re-run, stage 0b closed, and stage 0 ran to completion across three
passes. **No part of §15's claim changed, and nothing entered the trusted
base** — but two rule statements were wrong, a discharge method was missing and
a component was added, so this is a revision rather than an amendment.

**The decoupling pass.** §1's test was run over every reference to the course
in this document, which revision 3's sweep had done once and which §17 —
written later — had escaped. Three leaks, no mechanism touched: §17's stage 0
stopped being defined by unit 00, §10 stopped deriving the numeric kernel from
the course's five-significant-figures demand and derives it from §15 instead,
and §15.5 stopped calling the rule table "the course's mathematics". §1's own
summary sentence was corrected to match, including a claim that predated the
pass: the falsifier bank is generated from the rule table, not drawn from the
corpus. **The lesson is the habit, not the three edits** — the test works when
it is run and does not enforce itself, so run it over any new section before it
lands.

**Stage 0b closed.** Driving HolPy settled what reading its paper could not:
two of three side-condition traps go through its kernel as false results, so
the soundness property §15 exists to provide is *absent from its rules* rather
than merely unproved — which is the difference between a weaker version of this
and a different thing, and the reason the core is reimplemented rather than
reused. Its interaction was judged clunky and is not a source of inspiration
for §16.4, and §4.2 records why that is a verdict on HolPy rather than on §16's
request-per-move boundary. Its 183-problem corpus is a filed pointer whose
trigger is wanting a benchmark.

**Stage 0, three passes, forty-one goals, fourteen gaps** (`STAGE0.md`; every
goal verified against SymPy in the build-time-oracle role §15.5 allows). It also
retired its own framing: the output is a gap list, not an authoring rate,
because once the course has supplied the mathematics the drafting is mechanical
and the rate measures whoever does it. What the gaps changed:

- **§6.4** — `ftc`'s premises split across [a,b] and (a,b), because the
  closed-interval form could not close ∫₀¹ √(1−x²), an entirely ordinary
  integral under one of §8.5's own recognizer rows. The endpoint gap was one of
  three findings the review had flagged as *stated as settled and not
  adversarially verified*, and it was the one that was understated. The split
  does not over-admit: ∫₀¹ x^(−1/2) is still refused, because **F may misbehave
  at an endpoint and f may not**.
- **§6.5** — `ode_verify` corrected from `ring` to `field`, the same error
  class revision 2 fixed in §11.2 and left standing here.
- **§6.3** — all twenty-three derivative entries now state their output forms,
  since `sec` and `sech` are not in §5.1; plus `d_pow_int` wanting `n ≠ 0`.
- **§5.3** — a fifth method, **`by sign product`**, because four derivative
  entries emit positivity goals (`1 - u^2 > 0`, `u^2 - 1 > 0`) that no other
  method reaches. §11.2 was already making the move unnamed. Also: `pi` and
  `e_const` enter Fourier–Motzkin as opaque free variables, sound as intended
  and previously unstated.
- **§6.8** — enumerated on a stated basis, *per function and per direction an
  antiderivative can close through*, to **70 entries**; `ln_e`, `exp_zero`,
  `exp_one`, `atan_zero`, `tan_def`, `pyth_h`, the hyperbolic addition
  formulas and the three `abs` rules were all missing.
- **§8.9** — **`trig_norm`**, the one new component. §6.4's manual-rewrite
  consequence was scoped to trig *substitutions* and reaches ∫₀^{π/2} cos²x,
  which contains no substitution. The normaliser is untrusted, emits §6.8
  rewrites, runs inside the `D[x] F ≐ f` discharge rather than on the learner's
  goal, and is a canonicalisation rather than a search — which is why it sits
  in stage 1 without pulling `auto` forward. A third pass established that it
  is a **fallback after `field` fails, not a preprocessor**: ∫ tan²x closes as
  a ring identity in the atom `tan x`, and normalising first would emit a
  `cos x # 0` obligation the proof never needed.
- **§18 Q10** — `abs` in goals priced: ∫₋₁¹ |x| is **unstatable**, not merely
  unprovable, and the decision is owed before the parser.
- **§17** — rewritten. Stage 0 restated, stage 0b recorded closed, the
  authoring rate marked an upper bound inherited from a superseded model, the
  transcription argument stripped of its overstatement, and the falsifier bank
  given the observation that `ftc` collapses the substitution, so corpus
  coverage must not be read as move coverage.

**One number moved and one moved for the first time.** Stage 1 goes to ~4,300
lines with §8.9, `abs` in goals and `diverges`. And §6.8's
70 is the first part of the owed
rule recount to be counted rather than estimated — above all three of the
~80/~100/~110 readings, which means the disagreement was not between a high and
a low reading of the same table.

**Waterproof's evaluations were demoted to optional.** Revision 5 made them
required reading before stage 1, on the grounds that they are the only real
evidence about whether a tool of this kind gets used. That is adoption evidence
for the *class*, and the case for building this does not rest on other people
picking it up — it is an addition to `mechanics-to-relativity` for anyone
working through the course, and its own falsifier is §17's gate, which measures
*use* rather than *uptake*. **This is a distribution judgement and not a
coupling**: §1's boundary forbids the course determining how the tool works, and
says nothing about who the tool ships to. Bundling remains an open question
(§18 Q6), and this note does not settle it.

**§18 Q6 was settled: it lives in `tools/`, and the course points at it.**
A tool in its own right, available to anyone undertaking
`mechanics-to-relativity` — which is a *both*, where the question had offered
an either. The reference runs one way, course to tool, so §1's boundary is
structural rather than maintained by vigilance; and the course problems become
a separable package the tool loads, which turns §1's replaceability test from a
principle into a deliverable. Publishing stays a separate and later decision,
with §10's LGPL question attached to it.

**Three grammar questions were settled, which is what unblocks the parser.**
**Q10 — `abs` is admitted to goals**, with `d_abs` (needing no `sign` former,
since `u / abs u` is already in the grammar), the two sign rewrites and a
regularity entry. It costs no decidability claim, because §6.4 never made one;
`∫₋₁¹ |x| dx` becomes statable and still needs `int_split` at the kink, which
is the exercise rather than a shortfall. **Q11 — the `diverges` judgement is
in**, for `Int` and `Sum`, with `div_limit`, `div_compare`, `div_power` and
`div_pole`. It is **not** general negation: no `¬`, no negation-introduction,
no excluded middle against `conv`, and never a term, so `ring` and `field` are
untouched. Beyond the four target problems, it makes the FTC-across-a-pole
error **refutable rather than merely unprovable** — the trap §4.2 found HolPy
putting through its kernel, which this document had no way to *contradict*
before. **Q9 — limsup deferred with a trigger**, case by case rather than a
general endpoint-only sort: `oo` earned a syntactic class by appearing in three
constructs, `limsup` would appear in one, and §6.7's ratio-form radius rule
covers the corpus. Revisit when a second such construction arrives, or when a
target problem's *statement* needs one. Stage 1 grows to ~4,300 lines.

**What stage 0 could not do, and why stage 1 is next.** Nothing checked the
*encodings*. SymPy settles mathematics and has no notion of an obligation,
which is where §11.2's three errors lived and where gap 13 came within one step
of hiding. Every pass found things about the **rules**; none could find
anything about the **obligations**. That is a limit of the method rather than
of the effort, and the thing that lifts it is a kernel.

**Revision 7, 2026-09-23 — stage 0c, and the first thing checked by code.**
A `ring`/`field` spike (`spike/ring/`) ran §11.2 and found what stage 0's
method could not: an error in *how an obligation is closed*, rather than in
what the rules say. **One rule changed, and it is trusted**: `field` takes
facts, because §11.2's `rewrite sqrt_sq_val` had nothing to act on (§6.2,
§11.2). §15's claim is unchanged in form, since each fact is a theorem passed
as a handle, but the trusted procedure it rests on has grown a parameter,
which is why this is a revision. The other changes:

- **§6.2** — `field`'s obligation specified as *every divisor in its input*,
  replacing "every denominator it cancels", which cannot be implemented as
  stated. `ring`'s treatment of division, and atom identity up to arguments'
  normal forms, now stated.
- **§6.3** — `d_const` covers any term free of x. `-u` and `u / v` get no
  entries and are routed through `ring` and `field`, so the table stays at
  twenty-four.
- **§5.3** — method 4 tries the goal as written before normalising, for
  `d_atan`'s `1 + u^2`, an obligation §11.2 had never listed.
- **§16.2, §18 Q18** — measured and settled: not a risk at the corpus's sizes.
- **§17** — stage 0c closed. Its third question, what `ring`/`field` costs to
  write by hand, is explicitly *not* answered by a spike Claude wrote.

That the review and three stage-0 passes all missed the §11.2 error is the
lesson of this revision, and it confirms revision 6's closing note: **SymPy
and review check what the rules say; only running them checks how a proof uses
them.** Stage 1's headless kernel is where the rest of that class will turn up.

**Revision 8, 2026-09-23 — the recognizer, measured.** A second spike
(`spike/recognizer/`) scored §8.5's table against the technique the course's
own solutions use: 15/22 on the target corpus, and 3/9 held out from units
01–10. Rows fitted to the first set's misses reached 22/22 there and gained
nothing held out. That is the result that matters, and it is about the method
more than the table. The changes:

- **§8.5** — five rows: the chain rule, which was missing outright; the eˣ sin x
  cycle, which the parts row had been credited with and never matched;
  √(x² − a²); tan/tanh as f′/f; and the linear-over-quadratic split. Row seven
  is now ln|f|, stale since `d_abs` arrived in revision 6. Matching runs on the
  normalised goal. Two one-off techniques are recorded without rows.
- **§17** — the recognizer corpus gains a held-out rule and its first numbers.
  The table moves after stage 1's headless kernel. The assistance line's 400 is
  flagged as probably low. The gate's rung readings are to be taken only
  where the recognizer fired.
- **§18 Q15** — partly answered: reach before granularity.

No rule, judgement or trusted component changed. The lesson is the one
revision 7 drew about the kernel, now applied to the product: **a table scored
on the examples it was written from measures its author.** This one needed a
held-out set to show that, and so will every later version of it.

**Revision 9, 2026-09-23 — the first milestone, reviewed.** The
proof-of-life handoff in `WHAT.md` was reviewed along six dimensions:
- mathematical feasibility,
- scope,
- soundness and the trust boundary,
- estimate and measurement,
- consistency with this document,
- done criteria.

Each dimension's findings went to a skeptic told to refute them. Of 49, 48
survived, and they were merged into 18. Most were about the handoff, which was
rewritten. Five reached this document:
- **§5.3 / §6.8** — π has no sign under Fourier–Motzkin, so "`t ≥ 0` follows"
  was false and readiness P1 could not be completed by any discharge method.
  `pi_pos` is added, and it enters the constraint set whenever `pi` occurs. The
  same gap for e_const over stage 0's S3 range gives `e_gt_one`. Method 2 now
  adds its constraint only once the endpoints' order is known. The
  satisfiability pre-check's stated justification was false, and the true one
  is recorded: an unsatisfiable-with-constants-free set is unsatisfiable at
  their values, and nothing the kernel adds is false of them. The last two
  were noticed while applying the review, not by it.
- **§6.1** — a domain-limited equation can no longer be carried under `D[x]`
  or `lim`. That was an unsound rule statement no example had exercised, and
  §17's bank now carries it.
- **§11.1 / §11.2** — the `ftc` obligations are brought up to §6.4's split
  form, `cos_zero` is dropped where `ring` does its work, and the close's
  `3*sqrt 3 # 0` is listed.
- **§18 Q21** — what `rewrite` matches up to is open, with a default to trial.

The review itself was folded in and not kept, as the revision-2 review was.
**The pattern repeats a third time:** each round of *using* the design, by
encoding goals, then by running code, now by planning the build, has found an
unsound or unreachable step that every reading before it passed.

**Revision 10, 2026-09-24 — the first milestone, built.** `WHAT.md`'s
proof-of-life was built in `kernel/` against a frozen specification written
first: `GRAMMAR.md`, and `p1_expected.py` with both P1 proofs as move/args data
and their obligation lists derived by hand. The kernel proves readiness P1
modulo 6 and 14 admissions, with discharge stubbed, and its regression script
passes 225 checks. What reached this document:
- **§6.1 / §6.4** — `ftc` and rewriting under `Int` owe the range's
  orientation. Without it `ftc` proved ∫₁⁻¹ 1/x² ≐ 2. (The form of that
  debt, `lo ≤ hi`, was replaced by the consolidation's E56, below.)
- **§5.1 / §6.2 / §14** — the partial builtins are formers owing their natural
  domain, and `ring`, `field` and `norm_num` refuse `Int` and `D`. Without it
  `0*ln(-1) ≐ ?A` proved as `Proved.`. The owner chose this over committing to
  total semantics.
- **§5.1** — `D[x]` binds inside and is evaluated at x, and every former is
  charged at entry.
- **§5.3** — methods 4 and 5 widened for non-strict goals and rational
  content.
- **§6.1** — `# 0` counts as open under `D[x]`, and §18 Q21 is settled.
- **§6.2 / §6.3 / §6.8 / §6.9** — the a/d atom; `deriv` trusted while `ftc`
  accepts its output; one notation for §6.8's entries; and a stale `abs` line
  fixed.
- **§11** — both obligation lists brought up to what the kernel emits.
- **§15.2 / §15.3 / §16.3** — untrusted code called from trusted code, both
  protection mechanisms named, and a refusal shape for `/step`.
- **§15.2 / §17** — the line-count estimates removed, at the owner's call:
  auditability is argued from what the code does. The figures in the colophon
  above are kept as the record of what earlier revisions said.
- **§18** — Q22 (what becomes of an admission tagged `none`) and Q23 (how
  `Int` and `D` will state their definedness) are new.

The record is `PROOF_OF_LIFE.md`. **The pattern holds a fourth time:** building
the kernel found two unsound rule statements that the design review, the
encoding pass and the spikes had all passed.

**Revision 10, continued — `int_subst`, 2026-09-24.** The substitution move was
specified by hand before any code (`kernel/p1_expected.py` E36–E49, five of
them the owner's answers), then built, then given to a skeptic. The skeptic
found no false step. It did find one false theorem: a substitution created a
rational pole that the counter-point search never tried (E50). The suite passes
582 checks. What reached this document:
- **§6.4** — `int_subst` as built: forward and reverse modes, where each
  premise lives, endpoint equations decided in the step, the flip for a
  decreasing φ, and an occurrence selector that follows `rewrite`'s rules.
  Reading C¹ off `deriv` is sufficient, not necessary.
- **§5.1** — x = a cos θ, the canonical reversed case, is accepted through the
  flip.
- **§8.1 / §8.6** — the worked example's wrong guess was never legal, because
  its upper end does not map. The guess is now scaled, and the probe's value is
  corrected to 0.6023.
- **§8.4 / §8.5** — the chain-rule row is reverse-mode `int_subst`.
- **§11.1** — P1.1 runs from the sheet's own goal, modulo 5 admissions, all of
  them regularity. The endpoint line is two obligations, and `2 # 0` is listed.
- **§5.3 / §5.4 / §6.8 / §18 Q22** — `sqrt_nonneg` for the linear method, and
  rational roots as counter-points. Irrational poles stay admitted `none`, and
  Sturm sequences are recorded as the exact method for them.

**The pattern holds a fifth time, in a new place.** The flagship example's own
wrong guess, which §8.1 builds its argument on, had been marked legal since it
was written. Specifying the move was enough to find that.

**Revision 10, continued — the consolidation and two reviews, 2026-09-24.**
The consolidation step was specified by hand before any code
(`kernel/p1_expected.py` E51–E56, the owner deciding `int_flip`'s form and
the orientation rule), built, and given to a skeptic, whose findings were
specified (E57, E56 amended) and built in turn. An independent second review of that fix found no false
`Proved.`, and its two spec-level points are E57's amendment and E58. The
suite passes 655 checks. What reached this document:
- **§5.1 / §5.3 / §6.1 / §6.4** — reversed ranges everywhere (E56). Every
  step builds its interval from whichever order discharge proves, emits that
  order as its key, and refuses `orientation-undecided` when neither is
  proved. Enclosing ranges are decided first, and every order is decided
  lazily and memoised. E4's `lo ≤ hi` is superseded wherever it was stated,
  and the soundness argument is in §6.4: a proved order cannot be wrong, so
  no range is empty.
- **§6.4** — `int_flip`, `Int[x = a .. b] f ≐ Int[x = b .. a] −(f)`, in the
  form that lets `ftc` run after it (E51).
- **§5.3** — method 5 closes non-strict goals, with the parity over `<` and
  `≤` and no split of a −1 content under a non-strict target (E53).
- **§6.2 / §6.8** — `pyth`, `pyth_cos`, `sin_nonneg_on`, `cos_nonneg_on`,
  `cos_le_one` and `cos_ge_neg_one`, each with the one route that reads it
  (E54).
- **§6.1 / §15.2 / §15.4 / §18 Q23** — no rule may erase an `Int` or `D`
  node unless its definedness is owed (E57), after `rewrite pyth` proved a
  falsehood. `ftc`, `int_subst` and `int_flip` refuse a tree in a limit
  (§6.4).
- **§5.1** — `u^0` is 1 for every base, 0 included, and `e ^ e` still owes
  base > 0 (E58).
- **§11.1** — P1.1 runs officially from the sheet's goal, modulo 5 (E52).
- **§13** — ∫₀¹ √(1−x²) = π/4 by x = cos θ proves modulo 5, all regularity
  (E55).
- **How much to trust** — the false `Proved.`, recorded as what it was.

**The pattern holds a sixth time, and closer than before.** The earlier
rounds found their unsound steps while specifying or building, or found a
false value behind an admission (E50). This one found a plain `Proved.` for a
falsehood in code already committed with every check green, and what found
it was a reader trying to break it.

**This file is the whole design record.** The review document and the
revision-1 draft were folded in and deleted on 2026-09-20, before the project
was under version control, so there is no copy of either elsewhere; the git
history starts at revision 6. The exceptions are the two spikes' READMEs,
`spike/ring/README.md` and `spike/recognizer/README.md`, which hold their
working records; the findings above are folded from them. Where a number appears above, the measurement behind it is quoted with it.


