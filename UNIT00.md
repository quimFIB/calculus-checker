# Unit 00's quadrature cases: what the kernel lacks (gap list, 2026-09-26)

**Status (2026-09-26):** the owner approved finishing §17's gate corpus
("Go ahead") and asked for the work to go on unsupervised. This file is the
gap list, written before any code, as `P3.md` was for readiness P3.
G1 and G3–G5 are built (p1_expected section 26; `app/assist/CLASSIFY.md`);
G2 was not needed (E125), and the build added G8 and G9 below; G8 and G2
were built next (section 27), then P3(b) (section 28), G9 (section 29) and G6 (section 30). The corpus and its reading are `app/GATE.md`. It
names the lettered parts that make up the gate's unit 00 share, probes each
against the kernel as it stands (main at 4034076), and picks the smallest
cut.

## The gate's corpus, as §17 names it

§17's gate is "readiness P1–P5 and unit 00's quadrature cases". Two
findings change what that means in practice:

- **Readiness P4 is series** (sums in closed form, convergence tests, a
  radius of convergence). §17's stage 1 kernel list has no series rules:
  `Sum`, `conv` and `diverges` on series are §6.7, stage 2 ("series and
  limit rules"). P4 stays out of the stage 1 gate, as P3 parts 2–3 do, and
  the gate report lists it as not yet workable rather than averaging it
  in.
- **"Quadrature cases" is read per lettered part** (§17: "the unit is the
  lettered part, not the problem"). A unit 00 part is in when its
  mathematics is an integral to evaluate, a candidate solution to verify
  against its equation, or a classification. Numbers to four significant
  figures are stage 2 (certified numbers) and stay out; so does anything
  asymptotic (`big_O`, stage 2).

| Part | What it asks | In? | Needs |
|---|---|---|---|
| P1 (a)–(e) | classify each force as F(t), F(v), F(x) or none; the first reduction | yes | G5 (classify), G6 for the reductions as checked steps |
| P2, P5, P6, P11 | dimensional analysis, the pi theorem, scaling | no | §6.6 `buckingham`, stage 2 |
| P3 (a) | v(t) for linear drag on the way up, t↑ and h in closed form | yes | G1, G2, G3 |
| P3 (b) | t↑ < v₀/g from ln(1 + z) < z | yes, built (section 28) | a strict `taylor_lagrange` and bound's `scale` (E138–E140) |
| P3 (c), (d) | expansion in b; a numeric descent time | no | `big_O`, certified numbers (stage 2) |
| P4 (a) | quadratic drag: c, v(t) = v∞ tanh(gt/v∞), x(t) = (v∞²/g) ln cosh(gt/v∞) | yes | G1, G2, G3, G4 |
| P4 (b), (c) | four numbers; the asymptotic lag | no | stage 2 |
| P7 | period for V = k\|x\|ⁿ, a Beta function | no | `abs` rules (§13), Beta |
| P8 | convergence at a turning point | no | `diverges` and comparison; not a quadrature |
| P9 (a) | V from F, equilibria and their type | yes | nothing new for V; G3 for V′ at the equilibria |
| P9 (b)–(d), P10 | numbers, a series in θ₀ | no | stage 2 |

So the unit 00 share of the gate is P1, P3(a), P4(a) and P9(a), each
lettered part split into the goals its worked solution states.

## What already works (probed)

- The separated integrals prove with parameters signed in the goal's
  domain: `Int[w = v0 .. V] m/(-(m*g) - b*w) == ?A @ m > 0, b > 0, g > 0,
  v0 > 0, V in [0, v0]` takes `ftc` with F = −(m/b) ln(mg + bw).
- P1(c)'s first reduction, ∫₀ᵗ F₀e^(−s/τ)/m ds, takes `ftc`, and `exp_zero`
  finishes it.
- P9(a)'s V(x) = −∫₀ˣ(−κs + αs³) ds proves outright (`ftc`, `close`).
- ∫₀ⱽ dw/(1 − w²) takes `ftc` with F = ½ ln((1 + w)/(1 − w)), the course's
  "or partial fractions and two logarithms".
- Regularity already covers all sixteen builtins (`domains.py`: sinh,
  cosh, tanh and asinh are total, acosh and atanh have rows).

## Gaps

| # | Gap | Needed by | Kind |
|---|---|---|---|
| G1 | **No move closes an equation without `?A`.** `close` needs `?A` as the rhs, and no move evaluates a `D` node in a goal: `D[t] t^2 == ?A` refuses `close 2*t` with the residual `D[t](t^2) - 2*t`. §6.5's `ode_verify` (a candidate checked against its equation by `deriv` then `field`) has no move, and neither has an initial condition such as v(0) = v₀. | P3(a), P4(a), P9(a) | kernel: a move |
| G2 | **Missing exp and ln entries.** P3's t↑ = τ ln(1 + v₀/v∞) puts exp(−t↑/τ) into v(t↑) and h; closing needs exp(ln u) = u (u > 0), exp(−u) = 1/exp u, and a sign for ln: the range [0, τ ln(1 + z)] is refused `orientation-undecided` until ln u > 0 for u > 1 can be cited.  **Not built (E125):** the reference proofs take t↑ and h as quadratures in v, so no proof needs these entries; substituting t↑ into v(t) meets G8 first. **Built with G8 (E133)**, ln u > 0 as ln1p_pos, ln(1 + u) > 0 @ u > 0. | P3(a) | entries |
| G3 | **Hyperbolic functions have no derivative rule.** `deriv` knows sin, cos, exp, sqrt, ln and atan only: `atanh w` and `cosh s` refuse `deriv-no-rule`. P4 needs atanh (the quadrature), tanh (v(t)) and ln cosh (x(t)). | P4(a) | kernel: §6.3 rules |
| G4 | **Hyperbolic entries.** tanh u = sinh u / cosh u, cosh²u − sinh²u = 1 (field's fact for the tanh derivative), cosh u > 0 (ln cosh's former), and the values at 0 (sinh 0 = 0, cosh 0 = 1, tanh 0 = 0, atanh 0 = 0). | P4(a) | entries |
| G5 | **Classification.** §12.1's `classify` reads the free variables of the right-hand side. It is a tactic report, not a judgement (§5.2), so it belongs in the untrusted assistance layer: F(t), F(v), F(x) or none, with the reason. | P1 | assistance |
| G6 | **Hypotheses about an unknown function, and §6.5's derived lemmas.** P1's "first reduction" as a checked step needs the equation of motion as a hypothesis on a declared function (`m*D[t] v(t) == ...`), v ∈ C¹, the chain rule for declared functions (`deriv.py`: "d_chain waits for declared"), and `sep_autonomous`, `quad_t` and `energy_integral`, each derived from `int_subst` and `ftc`. **Built (section 30):** `install(goal, assumptions)` takes Γ, laws and C^k on declared functions over an interval, and the three rules read it and mint a handle each; P1(a)–(c) prove outright, as `kernel/problems/ode/` (E160, outside the gate's corpus), with `.dx`/page syntax for Γ and the three moves. The chain rule for declared functions is still not in `deriv.py`: the rules check F against f with the variable free. | P1(a)–(c) as proofs | kernel: hypotheses and three rules |
| G8 | **field keeps an App's argument as written** (found by the build, E125). exp(−b·((m/b)·L)/m) is not the atom exp(−L), and rewrite matches up to `ring`, which cannot cancel b/b. So v(t↑) = 0, the course's own "set v = 0" read on v(t), is stuck; the reference proofs take t↑ and h as quadratures in v instead. The fix touches the trusted normaliser (field-normal atom arguments) or rewrite (matching up to field). **Built (section 27, E131):** field cancels exact factors in an atom's argument, and the course's v(t↑) = 0 and h prove with exp_neg, exp_ln and ln1p_pos. | P3(a) as the course writes it | kernel |
| G9 | **Discharge is linear in the variables** (E126). u/w < 1 from u ≤ V < w with w > 0 is bilinear and is admitted; P4's quadrature is stated in the scaled form z = u/w. **Built (section 29):** discharge method 7, `clear`, multiplies through by a denominator of certified sign; the unscaled integral proves outright. | P4(a) unscaled | discharge |
| G7 | Numbers to four figures (t↑ = 0.1111 s, c = 0.2594 kg/m, t₉₉ = 14.84 s). | P3, P4 | stage 2 |

## The smallest cut

**G1–G5, in that order, and G6 recorded, not built.** With G1–G4 every
in-scope part except P1's reductions is a sequence of checked goals: the
separated integral (already works), the candidate verified against its
equation and its initial condition (G1), and the closed forms for t↑, h and
x(t) (G2, G4). G5 gives P1 its classifications on the page. P1's
reductions are then worked the way §8.3 describes stage 1 ("with the
learner supplying the candidate"): the integral the reduction produces is a
goal, and whether it is the right reduction is read against the
classification, not proved. G6 is a trusted-base extension (hypotheses
enter Γ) with a larger review, and nothing in the gate's reading needs it;
it is the next kernel step after the gate, not before it.

**G1 is `verify`, §6.5's `ode_verify` in general form.** On an equation
goal l == r @ G with no `?A`: every `D[x] e` node of either side is
replaced by `deriv`'s output (its side conditions emitted at the node's
position domain, where the `D` former already owes Reg(e, 1)), then
`l − r == 0` is checked by `ring` or `field` with facts, exactly as
`close`'s check. The theorem is the original goal. An initial condition is
the same move on a goal with no `D` node. Specified in p1_expected
section 26 before any code.
