# Stage 0 — encoding goals against §5.1 and §6 as they stand

**2026-09-22. Forty-one goals across three passes, every one verified against SymPy
(F′ = f exactly, and F(b) − F(a) matched to a direct quadrature), plus the two
table sweeps they left owed, then eleven more aimed at §8.9. **Forty-one goals,
fourteen gaps**, four of them design defects. All folded.**

- **First pass, S1–S15** — against the rules as revision 5 left them. Seven
  gaps, all folded.
- **Second pass, S16–S30** — against the corrected rules, probing the parts of
  the table the first pass never reached. Three new gaps, and one verification
  that the first pass's own correction did not over-admit.

**Status, 2026-09-22. Gaps 1–7 are folded into `DESIGN.md`** — 1 into
§6.4, 2 into §6.5, 3 into §6.3, 4 into §6.8, 5 into §17's falsifier bank, 6
into §5.3, 7 into §18 Q10 — and §17 is rewritten to the framing this pass
arrived at. No mechanism changed. **Gaps 8–10, from the second pass, are
recorded below**; 8 and 10 are folded, and 9 carries a decision that is not
mine to take. The gap texts below quote the rules **as they
stood when the pass ran**, which is why §6.4 is cited with its old
closed-interval premise and §6.5 with `ring`.

## What this pass actually is, and how it differed from §17's stage 0

*(§17 was rewritten on 2026-09-22 to match what follows. This section records
why, and reads as it did when the pass ran.)*

§17 described stage 0 as *measuring the authoring rate*: a human authors ten
goals with a stopwatch, and the hours-per-goal number decides the scope. That
framing assumes a human is the one authoring, and it survives only as long as
that is true.

It isn't. The mathematics is given — the course carries a worked solution for
every problem — so what is left is **encoding**, and encoding can be drafted
mechanically and checked against an oracle. §15.5 already sanctions SymPy in
exactly that role: a build-time authoring oracle, never in the kernel. So this
pass drafted the goals and verified every F′ = f before recording it.

**What that changes.** The rate stops being the decision-relevant output,
because it measures whoever does the typing. What stays decision-relevant, and
what this file records, is the **gap list** — the things that break when you
try to write a goal in §5.1 and close it under §6. Those are syntactic and
table-level facts, checkable by anyone against the grammar and the rule table,
and they do not depend on the surrounding proof being well-formed: a missing
`ln_e` is missing whether or not the step around it is right.

**What this pass cannot do, and nothing before stage 1 can.** Nothing checks
the *encodings*. SymPy confirms the mathematics; it says nothing about whether
the obligation list is complete, which is precisely where §11.2's three errors
lived. Treat every proof script below as a draft whose mathematics is verified
and whose encoding is not.

## First pass — S1 to S15

Fifteen, spread across goal shapes rather than drawn from one unit — see §17's
stage 0, which this pass follows on that point.

| # | Shape | Goal | Value | Verified |
|---|---|---|---|---|
| S1 | bare definite integral | ∫₀¹ 3x²+2x | 2 | ✓ |
| S2 | nominally a substitution | ∫₀¹ x·exp(x²) | (e−1)/2 | ✓ |
| S3 | nontrivial domain obligation | ∫₁^e (ln x)/x | 1/2 | ✓ |
| S4 | answer schema does real work | ∫₀¹ 1/(1+x²) | π/4 | ✓ |
| S5 | ODE, linear drag | m v̇ = −bv, v(0)=v₀ | v₀exp(−bt/m) | ✓ |
| S6 | improper, `oo` endpoint | ∫₁^∞ x⁻² | 1 | ✓ |
| S7 | trig with a side condition | ∫₀^{π/4} 1/(cos x)² | 1 | ✓ |
| S8 | endpoint degeneracy | ∫₀¹ √(1−x²) | π/4 | ✓ |
| S9 | finite sum, closed form | Σ_{n=1}^N n | N(N+1)/2 | ✓ |
| S10 | limit | lim_{x→0} sin x / x | 1 | ✓ |
| S11 | partial fractions | ∫₀¹ 1/((x+1)(x+2)) | ln(4/3) | ✓ |
| S12 | ODE, quadratic drag | m v̇ = mg − bv², v(0)=0 | v∞tanh(gt/v∞) | ✓ |
| S13 | ODE, `quad_t` | m ẍ = −mg | ut − gt²/2 | ✓ |
| S14 | `abs` in a goal | ∫₋₁¹ \|x\| | — | **unwritable** |
| S15 | reversed limits | decreasing φ under `int_subst` | — | see gap 5 |

Representative encodings:

```
problem stage0.S3                         -- nontrivial domain obligation
  answer schema  closed
  goal  Int[x = 1 .. e_const] (ln x)/x  ≐  ?A
proof
  step ftc  F := (ln x)^2 / 2
       obl  x > 0                   @ [1,e_const]  by range; linear (x ≥ 1)
       obl  D[x] F ≐ (ln x)/x       @ [1,e_const]  by deriv; field
       obl  F ∈ C¹ ∧ (ln x)/x ∈ C⁰               by reg
  step rewrite [ln_e, ln_one]               -- ln_e: see gap 1
  step close  ?A := 1/2                     by norm_num
qed
```

*This encoding is as written against revision 5, and is out of date: its `ftc`
premises predate gap 1's split, and its range cannot be oriented without gap
6's correction. The current encoding is in `WHAT.md`'s proof-of-life handoff, as
a seed for the kernel's first problem files.*

```
problem stage0.S5                         -- ODE, linear drag
  var  m b v0 : R   with  m > 0, b > 0, v0 > 0
  fun  v : R -> R
  assume eom : ∀t. m * D[t] v ≐ -(b * v t)
  assume ic  : v 0 ≐ v0
  goal  ∀t. v t ≐ v0 * exp(-(b*t)/m)
proof
  step ode_verify  with candidate := (λt. v0 * exp(-(b*t)/m))
       obl  m * D[t] cand ≐ -(b * cand)     by deriv; field  @ m # 0
       obl  cand 0 ≐ v0                     by rewrite exp_zero; norm_num
qed
```

### The first pass's gaps

Ordered by what it costs to leave them alone.

### 1. `ftc` cannot close ∫₀¹ √(1−x²) as the rules stand — the endpoint gap, now concrete

The antiderivative is F = (x√(1−x²) + asin x)/2. At the right endpoint,
`d_sqrt` wants u > 0 and u = 1−x² is **0** at x = 1; `d_asin` wants |u| < 1 and
|x| is **1**. So F is not C¹ on the *closed* interval, and `ftc`'s first
premise is `Γ ⊢ F ∈ C¹([a,b])`.

The integrand is bounded and continuous and the integral is elementary —
π/4 — so this is not a convergence question. It is the rule being stated on a
closed interval when the antiderivative only behaves on the open one.

**The review listed the `oo`/endpoint gap as one of three findings "stated as
settled and not adversarially verified."** This verifies it, with a problem that
is one line long and sits in the middle of the target material: every
√(a²−x²) trig substitution — §8.5 has it as a recognizer row — lands here.

A route exists: §6.4's `int_improper` handles "a finite singularity", so the
endpoint can be approached as a limit. But then a *bounded, continuous*
integrand has to be routed through the improper-integral rule because its
**antiderivative** misbehaves, which is surprising enough to need saying out
loud. The alternative is restating `ftc` with F ∈ C⁰([a,b]) ∧ C¹((a,b)), which
is the standard form and is what most libraries carry.

### 2. `ode_verify` is stated wrong, in the error class §11.2 already caught once

§6.5: a candidate "is checked against the equation by `deriv` then `ring`".
S5's residual is `m·v₀·(−b/m)·E + b·v₀·E` with `E = exp(−bt/m)` opaque to
`ring`. It cancels only if `m/m` cancels — **not a ring operation**. It needs
`field`, which emits `m # 0`.

This is exactly the correction revision 2 made to §11.2 (`close … by ring`
divides by `sqrt 3`, so it is `by field`), unmade in §6.5. Any ODE whose
coefficients divide hits it, which is most of them: S5 and S12 both do.

### 3. The derivative table's entries need their *output forms* pinned, not just their names

§6.3 lists `d_tan` and `d_tanh` bare. But **`sec` and `sech` are not in §5.1**,
so the textbook forms sec²u and sech²u are unwritable. The entries must be
stated in the grammar's own vocabulary — `1 + (tan u)²` and `1 − (tanh u)²` —
or the rule produces a term the language cannot hold.

S7 and S12 both depend on this. It is a small fix and a systematic one: every
derivative whose usual statement reaches for sec, csc, cot or sech needs
restating. Worth a sweep of §6.3 rather than a patch.

### 4. The value-at-a-point constants are under-enumerated — four of the first five goals hit one

§6.8 lists `sin_zero`, `cos_pi_half`, `ln_one`, `atan_one`, `atan_one_sqrt3`,
`atan_odd`, `sin_pi_sixth`, `cos_pi_fourth` "and the rest". Needed here and not
listed: **`ln_e`, `exp_zero`, `exp_one`, `atan_zero`**.

Each is one line. The pattern is the finding: **no FTC step closes without
evaluating F at both endpoints**, so every authored goal ends in this table, and
"and the rest" carries more weight than it looks.

This is also a down payment on a debt the review left open — *the rule recount
is still owed* (~80 / ~100 / ~110 across three independent counts, with §6.8
one of the three things the counters disagreed about). Authoring enumerates it
as a side effect.

### 5. `ftc` collapses the substitution, so an authored corpus under-exercises `int_subst`

S2 is nominally the substitution problem — u = x² is what a learner does. The
*reference proof* never substitutes: hand `F = exp(x²)/2` to `ftc` and it
closes. That is §6.4's keystone working exactly as designed, and it makes
authoring cheaper than §17 assumes.

It also means **the authored corpus will not test `int_subst`** — the rule with
the most delicate hypotheses in the document (φ ∈ C¹, continuity on the
composed integrand, the derived domain) and the one HolPy got wrong in two of
three probes. Stage 1's regression suite would have a hole precisely where §6.4
is hardest.

Authored goals test the kernel's **checking**. They do not test the **moves**.
Those need a separate bank, and §17's falsifier bank — generated from rule side
conditions — is the right place for it.

### 6. Unstated: what Fourier–Motzkin does with `pi` and `e_const` in the constraint set

S3's range gives `1 ≤ x ≤ e_const`. §5.3 method 3 is "Fourier–Motzkin over ℚ on
the linear constraints", and `e_const` is not a rational. Here it is harmless —
`x > 0` follows from `x ≥ 1` alone — but **readiness P1 integrates over
[0, π/2]**, so the flagship example puts π into the constraint set too.

Treating named constants as free variables is almost certainly the intent and
is sound. It is never said, and §5.3's satisfiability pre-check has to agree.

*Correction, 2026-09-23 (`DESIGN.md` revision 9).* "Harmless" above was wrong.
`x ≥ 1` does not follow either: by-range gives `min(1, e_const) ≤ x`, and with
`e_const` unsigned the range cannot be oriented. The same holds for π over
[0, π/2]. Both constants now bring sign facts into the constraint set
(`pi_pos`, `e_gt_one`, §6.8). With them, S3's `x > 0` by range closes as
annotated. Its `ftc` obligations are in the closed-interval form revision 6
split (§6.4); the current encoding lives in `WHAT.md`, not here.

### 7. `abs` in a goal, confirmed with a concrete cost

∫₋₁¹ |x| dx cannot be written down: §5.1 admits `abs` only in side conditions
and domains. This confirms §18 Q10 rather than discovering anything, but it now
has a one-line example attached.

### Two things that held

Recorded because a gap list with no passes is not evidence of anything.

- **`telescope` covers finite closed-form sums with no induction rule.**
  S9's Σ_{n=1}^N n = N(N+1)/2 looked like it needed induction, which §6.7 does
  not have. It does not: the telescoping witness T(n) = n(n+1)/2 gives
  T(n) − T(n−1) = n, and §6.7's `telescope` takes an explicit witness. Reachable
  as stated.
- **§5.3's sign certificate handles `1 + x² # 0` cleanly** (S4), by method 4's
  sum-of-even-powers-plus-positive-rational, with the decomposition emitted and
  re-checked by `ring`. No enclosure engine, no factoriser.

## Second pass — S16 to S30

Fifteen more, chosen to reach the parts of §6 the first pass never touched:
`int_parts`, `int_split`, `int_improper`, `geometric`, `telescope`,
`lhopital`, one-sided limits, `taylor_lagrange`, `leibniz`, `energy_integral`,
`period_integral`, `buckingham`, the non-`closed` answer schema, and the
double-angle route into §6.4's out-of-ℚ(atoms) territory.

| # | Probes | Goal | Value | Verified |
|---|---|---|---|---|
| S16 | `int_parts` | ∫₀¹ x·eˣ | 1 | ✓ |
| S17 | inverse-trig constant | ∫₀^{1/2} 1/√(1−x²) | π/6 | ✓ |
| S18 | double angle, outside ℚ(atoms) | ∫₀^{π/2} cos²x | π/4 | ✓ |
| S19 | `geometric`, side condition | Σ_{n=0}^N rⁿ | (1−r^{N+1})/(1−r) @ r ≠ 1 | ✓ |
| S20 | `cite`, no derivation route | Σ_{n=1}^∞ 1/n² | π²/6 | ✓ |
| S21 | divergence, needs negation | Σ_{n=1}^∞ 1/n | ∞ | **unstatable** |
| S22 | `energy_integral` | m ẍ = −kx | dE/dt = 0 | ✓ |
| S23 | `period_integral`, U′ ≠ 0 | pendulum | 2π√(L/g) | ✓ |
| S24 | `leibniz` | ∂ₐ∫₀¹ xᵃ | −1/(a+1)² | ✓ |
| S25 | one-sided limit | lim_{x→0⁺} x·ln x | 0 | ✓ |
| S26 | `int_split` | ∫₀² x² at 1 | 8/3 = 1/3 + 7/3 | ✓ |
| S27 | `taylor_lagrange` | eˣ, order 3 | x³e^ξ/6 | ✓ |
| S28 | `buckingham` | T = f(L,g) | T ~ √(L/g), rank 2 | ✓ |
| S29 | non-`closed` schema | ∫₀¹ e^(−x²) | √π·erf(1)/2 | ✓ |
| S30 | genuinely improper | ∫₀¹ x^(−1/2) | 2 | ✓ (**blocked**, correctly) |

### 8. The constant table needs entries per function *and per direction*

S17 closes on `asin(1/2) ≐ pi/6`. §6.8 has **`sin_pi_sixth`** — sin(π/6) ≐ 1/2
— which is a different theorem, and `asin` is an opaque atom to `ring` and
`field`, so the inverse direction cannot be derived from the forward one.

The table currently carries the inverse direction for `atan` (`atan_one`,
`atan_one_sqrt3`, and `atan_zero` added by gap 4) and the forward direction for
`sin` and `cos`, which is not a design — it is the record of which problems
happened to be worked. **Every inverse-trig and inverse-hyperbolic
antiderivative closes through one of these**, and §5.1 admits six of them
(`asin`, `acos`, `atan`, `asinh`, `acosh`, `atanh`), so the systematic statement
is: *a named value needs an entry per function per direction an antiderivative
can close through.* That is a larger table than "and the rest" suggests, and it
sharpens gap 4 rather than repeating it.

### 9. §6.4's out-of-ℚ(atoms) cases reach much further than the two documented

§6.4 names two places the `D[x] F ≐ f` check leaves ℚ(atoms): trig identities
after §8.5's √(a²−x²) substitution, and algebraic constants like §11.2's
(√3)² ≐ 3. It then states the consequence: since `auto` is stage 3, *"between
those stages every trig-substitution close is a manual rewrite."*

**S18 is neither of those cases and lands outside ℚ(atoms) anyway.**
∫₀^{π/2} cos²x dx has no substitution in it at all. The antiderivative is
x/2 + sin(2x)/4, and to `field` the atoms `cos x`, `sin 2x` and `cos 2x` are
unrelated: the residual is ½ + C₂/2 − C₁² over ℚ(C₁, C₂), which is not zero.
It closes only with the double-angle formula, which §6.8 has among "the
addition formulas".

So the scope of the manual-rewrite consequence is not *trig substitutions* but
**any antiderivative written with a multiple angle** — which is most of the
standard trig-integral repertoire, and reachable with no substitution
anywhere. Stage 1's learner meets this on bread-and-butter integrals, not on
the exotic ones.

*This one carried a decision rather than a repair, and it was taken:* **the
normalisation lands.** §8.9 adds `trig_norm`, a canonicaliser for trig
polynomials in a single base angle — untrusted, emitting §6.8 rewrites, running
inside the `D[x] F ≐ f` discharge rather than on the learner's goal, and a
normalisation rather than a search, which is why it can sit in stage 1 without
pulling `auto` forward. §17 grows a row (~200 lines, 15–30 hours). The
alternative — widen the stated consequence and let the learner do the
rewrites — was rejected because the integrals it lands on are the ordinary
ones, and §1 puts expansion on the bookkeeping side of the line rather than the
technique-choosing side.

### 10. `leibniz` over an improper integral is unstated

S24 differentiates ∫₀¹ xᵃ dx under the integral sign, giving −1/(a+1)², and
the integral is **improper for −1 < a < 0** while remaining convergent. §6.4
gives `leibniz` a uniform-domination obligation and gives improper integrals a
separate rule, `int_improper`, as a limit. How the two compose is not stated,
and readiness P7 — which §18 Q5 names as where `leibniz` is wanted — is the
place it would matter. Not obviously a defect; definitely unaddressed.

### The first pass's own correction, checked

**Gap 1's fix does not over-admit, and S30 is the proof.** Splitting `ftc`'s
premises across [a,b] and (a,b) was meant to admit ∫₀¹ √(1−x²), where the
*antiderivative* misbehaves at an endpoint and the integrand is fine. The risk
was that it would also admit genuinely improper integrals.

It does not. ∫₀¹ x^(−1/2) dx = 2 has F = 2√x ∈ C⁰([0,1]) and F ∈ C¹((0,1))
with F′ = f on the interior — the first three premises all hold — but
`f ∈ C⁰([a,b])` **fails**, since f → ∞ as x → 0⁺. The rule blocks it and
`int_improper` is still required. The corrected statement draws exactly the
line it was meant to: *F may misbehave at an endpoint; f may not.*

### Also confirmed, without new findings

- **`geometric` needs r ≠ 1** (S19), and the side condition is real rather than
  defensive — SymPy's own answer is a `Piecewise` splitting on exactly it.
- **`energy_integral` gives dE/dt = 0** for m ẍ = −kx (S22), and
  `period_integral`'s U′ ≠ 0 is non-degenerate for the pendulum away from
  θ₀ ∈ {0, π} (S23).
- **§6.6 is as decidable as §12.2 claims** (S28): the (L,T) matrix over (T,L,g)
  has rank 2 with null space spanned by (2,−1,1), giving T ~ √(L/g).
- **§9's `closed` whitelist bites correctly** (S29): ∫₀¹ e^(−x²) is
  √π·erf(1)/2, `erf` is a declared symbol, and the goal needs the explicit
  special-function escape rather than passing as `closed`.
- **The negation gap, second sighting** (S21): Σ 1/n diverging is unstatable,
  as §5.2 and §18 Q11 record. Two of thirty goals now hit it.

## Third pass — S31 to S42, aimed at `trig_norm`

Eleven multiple-angle goals, written to test §8.9 rather than the kernel. Each
was checked twice: **does `field` alone fail** (every distinct trig call
replaced by an independent atom), and **does §8.9's stated reduction reach
zero**.

| # | Goal | Atoms `field` sees | field alone | after `trig_norm` |
|---|---|---|---|---|
| S31 | ∫₀^{π/2} cos²x = π/4 | cos 2x, cos x | ½ + A₀/2 − A₁² → fails | 0 |
| S32 | ∫₀^{π/2} sin²x = π/4 | cos 2x, sin x | fails | 0 |
| S33 | ∫₀^{π} sin² 2x = π/2 | cos 4x, sin 2x | fails | 0 |
| S34 | ∫₀^{π/2} sin x cos x = ½ | cos x, sin 2x, sin x | fails | 0 |
| S35 | ∫₀^{π/2} cos³x = 2/3 | cos x, sin x | fails | 0 |
| S37 | ∫₀^{π/2} sin 3x cos x = ½ | 4 atoms | fails | 0 |
| S38 | ∫₀^{π} sin 2x sin 3x = 0 | 4 atoms | fails | 0 |
| S39 | ∫₀^{π/2} cos⁴x = 3π/16 | cos 2x, cos 4x, cos x | fails | 0 |
| S41 | ∫₀¹ cosh²x | cosh 2x, cosh x | fails | 0 |
| S36 | ∫₀^{π/4} tan²x = 1 − π/4 | tan x | **closes** | see gap 13 |
| S42 | ∫₀^{π/2} dx/(1+cos x) = 1 | tan x/2, cos x | fails | 0 (base = x/2) |

**The design works on every case it was built for.** Nine multiple-angle
integrals, `field` alone failing on all nine with the residual shown, and the
reduction closing all nine. That is the worked example §8.9 did not have.
Two further confirmations: **half-angle bases work** — S42's base is x/2, with
cos x expanded *into* it, which is the Weierstrass direction and the one where
the base is smaller than anything appearing in the goal — and the **canonical
form claim holds**, S35 reducing sin³ through sin·(1−cos²) to degree one in sin.

Three findings, and the first is the one worth having.

### 13. `trig_norm` must run *after* `field` fails, not before it

S36 is the case that does not want normalising. ∫₀^{π/4} tan²x dx closes on
F = tan x − x with no normalisation at all: `d_tan` yields `1 + (tan x)^2`, so
the residual is a **ring identity in the single atom `tan x`**.

Run unconditionally as a preprocessing step, `trig_norm` rewrites
`tan x → sin x / cos x`, converts a free `ring` close into a `field` close,
and **emits a `cos x # 0` obligation the original proof never needed**. The
tactic is not sign-preserving with respect to difficulty: it can make a
closable goal harder.

So it is a **fallback, not a preprocessor** — try `field`, and normalise only
on failure. §8.9 was written as though normalising first were free. Folded.

### 14. Hyperbolic coverage was asserted; `pyth` does not supply it

§8.9 claims trig *and hyperbolic* atoms. S41 needs `cosh²u − sinh²u ≐ 1`,
which is **not an instance of `pyth`** — the sign differs, and a normaliser
reducing hyperbolic atoms with `pyth` would be *unsound* rather than
incomplete. §6.8 listed `pyth` and "the addition formulas" with no hyperbolic
analogue named.

### 12. `trig_norm` needs `tan_def`, which §6.8 did not have

The reduction targets polynomials in `sin u` and `cos u`, so it must be able to
leave a `tan` atom — and `tan u ≐ sin u / cos u @ cos u # 0` was in no listed
entry. It also makes the general point behind gap 13: this rewrite is a *field*
operation, so the tactic changes the **obligation set** and not only the
syntax.

§6.8 gains `tan_def`, `pyth_h` and the hyperbolic addition formulas; the
enumeration goes from 64 to **67**.

## What this says about stage 0

The gap curve is flattening slowly, and is not flat. Across forty-one goals:
**four gaps from the first five, three from the next ten, three from the next
fifteen, three from the last eleven** — a falling rate per goal, but no sign of stopping, and the later
gaps are not the smaller ones. Gap 1 verified something the review had
explicitly marked unverified; gap 3 is a systematic constraint on how §6.3 must
be written; gap 9 widens a consequence §6.4 states too narrowly and carries a
decision with it.

What did change between the passes is the *kind* of gap. The first pass found
rules stated wrongly. The second found rules stated **too narrowly** — a
consequence understated (9), a table built ad hoc rather than systematically
(8), an interaction between two rules never considered (10). That is what you
would expect from a document that has been reviewed hard for correctness and
never once used.

So stage 0 is worth running, and was **misdescribed in §17** — since corrected
there. It is not "measure the authoring rate". It is:

> **Try to encode goals against §5.1 and §6 as they stand, and list what
> breaks.** The output is a gap list, not a number.

The rate question does not disappear, it relocates: if goals are drafted
mechanically and a human reviews them, the quantity that prices the corpus is
**review time**, not authoring time. And review has a problem stage 0 cannot
solve — §1 is explicit that the learner has no calculus fluency, so reviewing a
drafted encoding is a weak check. The thing that makes authoring both cheap and
trustworthy is the kernel, which is an argument for getting a minimal one
standing earlier than §17 orders it.

## Next

Thirty goals is where this stops being the cheapest thing to do. What it leaves:

- **One decision, from gap 9**, and it is the only item here that is not
  bookkeeping: does §6.4's manual-rewrite consequence simply widen, or does a
  narrow double-angle normalisation land before `auto`? The second is a new
  component and belongs in §15.5's build-versus-reuse table, not in a sentence.
- ~~**Two sweeps now owed.**~~ **Both run, 2026-09-22.** §6.3 now states all
  twenty-three right-hand sides; all parse under §5.1, and the sweep turned up
  **gap 11** — `d_asin`, `d_acos`, `d_atanh` and `d_acosh` emit positivity
  obligations (`1 - u^2 > 0`, `u^2 - 1 > 0`) that none of §5.3's five methods
  discharges. **Now fixed** — see the gap 11 decision below. §6.8 enumerated to
  **64 entries** on gap 8's basis, against the recount's "20 or 45".
- **Two citations to re-check.** Whether §15.5's `is_RInt_derive` still matches
  §6.4's split-interval form, owed before §14 counts it `cited`; and how
  `leibniz` and `int_improper` compose (gap 10), owed before readiness P7.
- **`abs` in goals** (§18 Q10), which changes the grammar and is owed before
  the parser is built.
- **The recount, one section down and two to go.** §6.8 came to 64 — above
  every estimate, so the totals move up rather than settling. §6.7's "limit
  laws" and §6.9's regularity rules are the two remaining disputes, and each
  wants the same treatment: state the basis, then count.
- ~~**Gap 11 needs deciding before stage 1.**~~ **Decided 2026-09-22:** §5.3
  gains a fifth method, `by sign product` (factor, re-check the factorisation
  with `ring`, combine the factors' signs), and `cite` becomes sixth. Four
  named §6.8 lemmas were the rejected alternative — cheaper, and wrong by
  §6.8's own criterion, since `1 - u^2` is not an opaque atom. §11.2's
  `1 + x^3 # 0` is now an instance of the named method rather than an unnamed
  move.

The sweeps have landed and gap 11 is decided, so **a third pass is unblocked**.
The third pass ran and §8.9 survived it with two corrections and a missing
table entry, none of which touched its shape. Nothing is outstanding.

**The rate has stopped falling.** Three gaps from the last eleven goals is the
same rate as the previous fifteen, and the third pass was the narrowest of the
three — one component, one shape of integral. That is the argument for
stopping the authoring passes here and letting the next findings come from
stage 1, where a kernel checks the encodings instead of SymPy checking the
mathematics. Every pass so far found things *about the rules*; none could find
anything about the **obligations**, which is where §11.2's errors lived and
where gap 13 came within one step of hiding.
