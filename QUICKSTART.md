# Quickstart: the language by worked examples

Twelve short lessons, each a complete script that the kernel checks to
`Proved.` They start with the smallest proof there is and end with an
equation of motion. On the way they cover every move a stage-1 problem
needs, the rewrite entries, and what a refusal looks like. The scripts
are the files in `tutorial/`. `app/test_tutorial.py` checks every one of
them, and every other example on this page, so nothing here has drifted
from what the checker does.

**This comes before the gate.** None of these twelve goals is one of the
gate's seventeen problems (`app/GATE.md`). The gate records how far up the
hint ladder you go on each problem. If you learn the notation while doing
the gate, the early problems cost hints for syntax, the late ones don't,
and the gate "passes" on notation rather than calculus. Get the language
here first. See [Before the gate](#before-the-gate) at the end.

## Starting it

```
./calc
```

Then open http://127.0.0.1:8765/. It needs Python 3.12 or newer.

The page has three panes:

- **Problem** (left): the problem picker; **Your own goal**, a form with
  Goal, Functions and Assuming fields; **Parse echo**, which shows how a
  term you type is read; and **Attempts**, the tree of everything you have
  tried, with retracted branches kept and struck through.
- **Script** (centre): where you type tactics. `Alt+↓` checks the next
  sentence, `Alt+↑` retracts the last one, and `Ctrl+Enter` checks or
  retracts up to the cursor. Checked text is shaded green. Editing inside
  it retracts back to the sentence you edited.
- **Goals** (right): the current goal, its obligations, a palette of moves
  and rewrites that fit (click one to insert it), and a progress note.
  Below them are the **Evaluate** and **Classify** boxes and the
  **Response**: the last success or refusal.

**Running a lesson on the page.** Every lesson file starts with a header
sentence, which the page takes in the left pane rather than the script:

- `problem stage0.S1.` means: choose `stage0.S1` in the picker and press
  Start.
- `goal G @ D functions f/1 assuming ... .` means: open **Your own goal**,
  put `G @ D` in Goal, `f/1` in Functions and each assumption on its own
  line in Assuming, then press Start.

Paste the rest of the file into the script pane and step through it. The
`(* ... *)` comments can stay: they are comments to the checker too.

**Running a lesson in Emacs.** Load the mode once, with
`(load "/path/to/calculus-checker/emacs/dx-mode.el")` in your init, then
open the file itself. `dx-mode` (Emacs 29+) runs `./calc --lsp` and
checks the whole buffer as you type. The checked part is shaded, a refused sentence is
underlined, and `*dx-goals*` shows the goal at point. Useful keys: `C-c C-l`
goals window, `C-c C-t` next hint, `C-c C-a` use the suggestion, `C-c C-e`
evaluate, `C-c TAB` complete a move into its template. Doom users:
`emacs/doom/dx/README.org`.

## Writing terms

The kernel's grammar (`kernel/GRAMMAR.md`) is strict on purpose: each of
these refusals stops a misreading that would otherwise prove something
you did not mean.

| Write | Not | Why |
|---|---|---|
| `2*x` | `2x` | no implicit multiplication |
| `exp(x)`, `exp x` | `e^x` | `e_const` is the number e; `e^x` would be a different function |
| `sin x`, `x*y` | `sinx`, `xy` | a name is one letter (plus digits or `_suffix`) or a Greek word: `v0`, `x_1`, `theta` |
| `ln x` | `log x` | |
| `1/2` | `0.5` | no decimals |
| `(sin x)^2` or `sin(x^2)` | `sin(x)^2` | ambiguous, so refused |
| `x*(x + 1)` | `x(x + 1)` | only declared functions are called |

Other conventions:

- A function's argument can go without brackets, but binds tightly:
  `sin x*y` is `(sin x)*y`. Type a term in **Parse echo** to see how it
  reads.
- The constants are `pi` and `e_const`. Infinity is `oo`, and appears only as
  an integral's end or an open interval's end, such as `[0, oo)`.
- `Int[x = a .. b] e` is the integral of `e` over x from a to b.
  `D[x] e` is the derivative of `e` with respect to x.
- A goal is `left == right`, or an order `<=` `<` `>=` `>`, optionally
  followed by `@` and what may be assumed: `@ a > 0, b > 0`, or an interval
  `@ b in [0, 1)`. `?A` is the unknown value you are asked to find.
- A tactic is one sentence ending in `.`. `(* ... *)` is a comment.

## Lesson 1: the whole loop

`ftc F` claims that F is an antiderivative of the integrand. The kernel
differentiates F by its rule table and compares F′ with the integrand, using
`ring` (algebra with `+ - *` and whole powers). If they agree, the integral
becomes F(b) − F(a). `close V` names the value.

`tutorial/01-ftc.dx`:

```dx
(* Lesson 1. The whole loop: an integral, an antiderivative, a value.
   Goal: Int[x = 0 .. 1] 3*x^2 + 2*x == ?A *)
problem stage0.S1.

(* You propose F. The kernel differentiates it, checks F' against the
   integrand with ring, and replaces the integral by F(1) - F(0). *)
ftc x^3 + x^2 by ring.

(* The goal is now 1^3 + 1^2 - (0^3 + 0^2) == ?A. Name the value. *)
close 2 by ring.
```

Get it wrong and the kernel says by how much:

```dx
problem stage0.S1.
ftc x^3 + x.
(* refused: ftc-check-failed *)
```

The response reads `ring leaves lhs - rhs = -2*x + 1` and shows where F′ and
the integrand diverge. **Nothing is accepted that was not checked.** The
status line's `0 machine-checked` is honest: the kernel itself is not
formally verified (`DESIGN.md` §14).

Behind every step is a list of **obligations**: what must be true for the
step to be valid. For `ftc` these are that F is continuous on [0, 1] and
differentiable inside, and that F′ matches the integrand. Each is shown
with how it was discharged (`reg`, `deriv+ring`, …). An obligation that is
false refuses the step, and so does a goal that owes one. An integral
across a pole is refused before any move:

```dx
goal Int[x = -1 .. 1] 1/x^2 == ?A.
(* refused: obligation-decided-false *)
```

The response reads `x^2 # 0 @ [-1, 1] is false at x = 0`.

## Lesson 2: values must be evaluated

`close` accepts only a value in closed form: `exp 1` is not an answer,
`e_const` is. The **entries** (listed [below](#the-entries)) are the
known facts that make that step: `rewrite E at T` replaces the subterm
`T` using entry `E`.

`tutorial/02-evaluate.dx`:

```dx
(* Lesson 2. Values must be fully evaluated: exp 1 is not an answer,
   e_const is. The rewrite entries turn one into the other.
   Goal: Int[x = 0 .. 1] x*exp(x^2) == ?A *)
problem stage0.S2.

(* The inner derivative is 2x, so F carries a 1/2. *)
ftc exp(x^2)/2 by ring.

(* Now exp(1^2)/2 - exp(0^2)/2 == ?A. The entry exp_one says
   exp 1 == e_const; `at` names the subterm to rewrite. *)
rewrite exp_one at exp(1^2).
rewrite exp_zero at exp(0^2).
close (e_const - 1)/2 by ring.
```

Closing too early names the entry still to use:

```dx
problem stage0.S2.
ftc exp(x^2)/2.
close (exp 1 - exp 0)/2.
(* refused: close-not-evaluated *)
```

`exp 1 can still be evaluated (exp_one)`. And when an antiderivative is off
by a constant factor, the refusal carries a corrected sentence. On the
page, **Use this** puts it in place of yours. In Emacs it is `C-c C-a`.

```dx
problem stage0.S2.
ftc exp(x^2).
(* refused: ftc-check-failed *)
```

`Your F′ is 2 times the integrand. Scale F by 1/2.`, with the suggestion
`ftc (exp(x^2))/2 by ring.`

## Lesson 3: `ring` and `field`

`by ring` is the default. `by field` also divides, and every divisor it
uses becomes an obligation that it is nonzero. Use `field` when F′ or the
value has a quotient in it.

`tutorial/03-field.dx`:

```dx
(* Lesson 3. ring knows + - * and whole powers. field also knows
   division, and every divisor it uses becomes an obligation that it
   is nonzero. Goal: Int[x = 1 .. e_const] (ln x)/x == ?A *)
problem stage0.S3.

(* D[x] (ln x)^2/2 is ln x * (1/x): a quotient, so field. The
   obligations pane now lists x # 0 and x > 0 (ln's domain) on the
   range, each discharged with a method. *)
ftc (ln x)^2 / 2 by field.
rewrite ln_e at ln e_const.
rewrite ln_one at ln 1.
close 1/2 by ring.
```

## Lesson 4: substitution, "let u = x²"

`int_subst` has two modes. **Reverse**, the one you would say out loud:
name the new variable as a function of the old one, give the new ends, and
write the integrand in the new variable after `reverse`.

`tutorial/04-subst-reverse.dx`:

```dx
(* Lesson 4. Substitution the way you would say it: "let u = x^2".
   Goal: Int[x = 0 .. 1] x*exp(x^2) == ?A, lesson 2's integral again. *)
problem stage1.S2R.

(* Reverse mode: u := g(x) with g = x^2, `from 0 to 1` the new ends
   g(0) and g(1), and `reverse f` the integrand in u. The kernel checks
   x*exp(x^2) == f(g(x)) * g'(x), that is exp(x^2)/2 * 2x. *)
int_subst x := x^2 as u from 0 to 1 reverse exp(u)/2 by ring.

(* Int[u = 0 .. 1] exp(u)/2 == ?A *)
ftc exp(u)/2 by ring.
rewrite exp_one at exp 1.
rewrite exp_zero at exp 0.
close (e_const - 1)/2 by ring.
```

## Lesson 5: substitution, x = φ(t)

**Forward**: name the old variable as a function of the new one. This is
the mode for killing a root.

`tutorial/05-subst-forward.dx`:

```dx
(* Lesson 5. Forward substitution, x := phi(t): kill a root.
   Goal: Int[x = 0 .. 1] x*sqrt(1 - x) == ?A *)
problem stage1.SUB1.

(* x = 1 - t^2 makes 1 - x a square. `from 1 to 0` names the t that
   lands on each old end, in order: phi(1) = 0 and phi(0) = 1, which
   the kernel checks. The new integral runs from t = 1 to t = 0, and
   ftc takes it as it stands. *)
int_subst x := 1 - t^2 as t from 1 to 0 by ring.

(* sqrt(t^2) is t only because t >= 0 on the range; sqrt_sq carries
   that condition, and the kernel discharges it from the range. *)
rewrite sqrt_sq with u := t at sqrt(1 - (1 - t^2)).
ftc (2/5)*t^5 - (2/3)*t^3 by ring.
close 4/15 by ring.
```

Entries with a side condition (`sqrt_sq`: `sqrt(u^2) == u @ u >= 0`) are
instantiated with `with u := T;`, and the condition becomes an obligation.

## Lesson 6: facts, for the checks

A `rewrite` changes the goal. A `fact` changes nothing: it binds an entry to a
name, and `using h` hands it to a check (`ftc`, `close`, `bound`,
`verify`). Use one when `ring` or `field` needs an identity to see that two
sides agree.

`tutorial/06-facts.dx`:

```dx
(* Lesson 6. Facts: an entry bound to a name and handed to a check.
   Goal: Int[x = 0 .. 1] sqrt(1 - x^2) == ?A, a quarter of the unit disc. *)
problem consolidation.QC1.

int_subst x := cos theta as theta from pi/2 to 0 by ring.

(* cos is decreasing here, so the kernel flips the range: the new
   integral runs over [0, pi/2] and holds sqrt(1 - (cos theta)^2).
   Turn the inside into a square, then take the root, which needs
   sin theta >= 0 on the range (discharged for you). *)
rewrite pyth_cos with u := theta at (cos theta)^2.
rewrite sqrt_sq with u := sin theta at sqrt(1 - (1 - (sin theta)^2)).

(* F' comes out in sin^2 and cos^2 together; ring alone cannot see
   they add to 1. `fact` binds the identity to h_pyth, and
   `using h_pyth` gives it to the check. *)
fact h_pyth := pyth_cos with u := theta.
ftc (theta - sin theta * cos theta)/2 by field using h_pyth.
rewrite sin_pi_half at sin(pi/2).
rewrite cos_pi_half at cos(pi/2).
rewrite sin_zero at sin 0.
close pi/4 by ring.
```

## Lesson 7: your own goal, with parameters

Anything after `@` is assumed. Parameters are ordinary letters, and the
obligations use the assumptions: here the range [0, a] is only a range
because a > 0.

`tutorial/07-parameters.dx`:

```dx
(* Lesson 7. Your own goal, with a parameter and an assumption about it.
   Everything after @ is what you may assume. *)
goal Int[x = 0 .. a] x^2 == ?A @ a > 0.

ftc x^3/3 by ring.
close a^3/3 by ring.
```

A reversed range is legal. `int_flip` turns ∫ₐᵇ f into ∫ᵦᵃ −f when you want
it the usual way round:

```dx
goal Int[x = 1 .. 0] 2*x == ?A.
int_flip.
ftc -(x^2).
close -1.
```

## Lesson 8: integration by parts, and occurrences

`tutorial/08-parts.dx`:

```dx
(* Lesson 8. Integration by parts: Int u v' = [u v] - Int u' v. *)
goal Int[x = 0 .. 1] x*exp x == ?A.

(* Name u and v (not v'); the kernel checks u * D[x] v against the
   integrand. `in x` is the integration variable. *)
int_parts in x with u := x; v := exp x by ring.

(* 1*exp 1 - 0*exp 0 - (Int[x = 0 .. 1] 1*exp x) == ?A. The integral
   is no longer the whole left side, so point ftc at it: occurrence 0
   is the first Int, counted left to right. *)
ftc exp x occurrence 0 by ring.

(* A rewrite replaces every match of its subterm. *)
rewrite exp_one at exp 1.
rewrite exp_zero at exp 0.
close 1 by ring.
```

`occurrence N` works the same way wherever a move could apply at more than
one place (`ftc`, `int_improper`, `rewrite`, `int_subst`, `int_flip`,
`int_parts`).

## Lesson 9: an infinite end

`tutorial/09-improper.dx`:

```dx
(* Lesson 9. An infinite end: F(oo) is a limit, and the kernel takes it. *)
goal Int[x = 0 .. oo] exp(-x) == ?A.

(* Like ftc, but also checks that F has a finite limit at the infinite
   end and puts that limit in F(oo)'s place: here 0. *)
int_improper -exp(-x) by ring.

(* -0 - (-exp(-0)) == ?A. exp_zero matches exp(-0) up to ring. *)
rewrite exp_zero at exp(-0).
close 1 by ring.
```

## Lesson 10: an inequality, from Taylor's theorem

Not every goal has a `?A`. An order goal is proved by building a fact that
implies it. `taylor_lagrange` mints the lower or upper bound of a Taylor
remainder, provided the last derivative you list has a known sign. `bound`
closes the goal from that fact.

`tutorial/10-taylor.dx`:

```dx
(* Lesson 10. An order goal: prove an inequality, not find a value.
   Taylor's theorem with a monotone remainder, then `bound`. *)
goal b^2/2 <= exp b - (1 + b) @ b in [0, 1).

fact h0 := exp_zero.

(* Expand f = exp u at 0, valid on [0, 1), read at u = b. derivs lists
   f', f'', f''' (here all exp u). With three listed, the polynomial
   is order n = 1 (1 + b), and the last derivative's sign (>= 0:
   increasing) bounds the remainder between f''(0)*b^2/2 and
   f''(b)*b^2/2. `lower` binds the left one to hl:
   exp 0 * b^2/2 <= exp b - (exp 0 + exp 0 * b). The goal is unchanged. *)
taylor_lagrange hl := lower of exp u in u from 0 to 1 at b derivs exp u; exp u; exp u increasing by ring.

(* bound closes an order goal from one order fact. hl says exp 0
   where the goal says 1, so h0 goes to field too. *)
bound by field using hl, h0.
```

Without `h0`, `bound` shows exactly what is missing:

```dx
goal b^2/2 <= exp b - (1 + b) @ b in [0, 1).
taylor_lagrange hl := lower of exp u in u from 0 to 1 at b derivs exp u; exp u; exp u increasing by ring.
bound by field using hl.
(* refused: bound-check-failed *)
```

The residual is `(1/2)*b^2*exp 0 - (1/2)*b^2 + b*exp 0 - b + exp 0 - 1`,
which is `exp 0` everywhere 1 should be.

## Lesson 11: checking a candidate solution

`verify` closes an equation with no `?A`. It differentiates every `D` node
and checks the two sides agree. Solving a differential equation is then
guess and check: propose y(t), and let `verify` confirm it.

`tutorial/11-verify.dx`:

```dx
(* Lesson 11. Checking a candidate solution of a differential equation.
   Does y = y0 exp(-k t) satisfy y' = -k y? *)
goal D[t] (y0*exp(-k*t)) == -k*(y0*exp(-k*t)) @ k > 0.

(* verify differentiates every D[t] node with the rule table, then
   checks the two sides agree by ring (or field). No ?A, no value. *)
verify by ring.
```

An initial condition is the same move on a goal with no `D`:

```dx
goal y0*exp(-k*0) == y0 @ k > 0.
rewrite exp_zero at exp(-k*0).
verify by ring.
```

The **Classify** box on the page reads a force F in m x″ = F and says which
case it is: F(t) (integrate once), F(v) (separate), F(x) (multiply by
velocity), or none, with the parameter that would fix it. Try `F0*cos(omega*t)`.

## Lesson 12: reasoning from an equation of motion

When the solution is not in hand, state what you know about the unknown
function and derive from that. `functions v/1` declares v; `assuming`
names each fact about it. Three moves read such a law, one per case the
Classify box names: `quad_t` for F(t), `sep_autonomous` for F(v),
`energy_integral` for F(x). Each mints a handle that `verify` then uses.

`tutorial/12-ode.dx`:

```dx
(* Lesson 12. Reasoning from an equation of motion you did not solve.
   `functions v/1` declares v as an unknown function of one argument;
   `assuming` states what is known about it on s in [0, oo): the law
   (named eom) and that v is C^1 (named regv). *)
goal v(t) == v(0) + F0*t/m @ m > 0, t >= 0 functions v/1 assuming eom: m*D[s] v(s) == F0 for s in [0, oo); regv: v in C^1 for s in [0, oo).

(* A force that depends on time only (here constant): integrate once.
   quad_t reads eom as m v' = R(s), checks your antiderivative F of
   R/m, and binds h: v(t) == v(0) + (F(t) - F(0)). *)
quad_t h := eom from 0 to t in u antiderivative F0*u/m regs regv by field.
verify by field using h.
```

## The moves

| Move | Does | Lesson |
|---|---|---|
| `ftc F` | ∫ f → F(b) − F(a), checking F′ = f | 1 |
| `close V` | names `?A`; V must be fully evaluated | 1, 2 |
| `rewrite E at T` | replaces T by an entry | 2 |
| `int_subst` | substitution, forward or `reverse` | 4, 5 |
| `fact h := E` | binds an entry for `using h` | 6 |
| `int_flip` | ∫ₐᵇ f → ∫ᵦᵃ −f | 7 |
| `int_parts` | ∫ u v′ → [u v] − ∫ u′ v | 8 |
| `int_improper F` | `ftc` with a limit at an infinite end | 9 |
| `taylor_lagrange` | mints a Taylor remainder bound | 10 |
| `bound` | closes an order goal from one order fact | 10 |
| `verify` | closes an equation by differentiating and checking | 11 |
| `quad_t`, `sep_autonomous`, `energy_integral` | derive from a law in Γ | 12 |

The full syntax, every optional clause included, is `app/SCRIPT.md`. The
page's **Tactics** button shows a short version, and `C-c TAB` in Emacs
expands a move name into its template.

## The entries

These are everything `rewrite` and `fact` can name. Schema letters (`u`,
`v`, `a`) are filled with `with u := T;`. Conditions after `@` become
obligations.

**Values**, for evaluating before `close`:

| Entry | States |
|---|---|
| `sqrt_zero` | `sqrt 0 == 0` |
| `sin_pi_half` | `sin(pi/2) == 1` |
| `cos_pi_half` | `cos(pi/2) == 0` |
| `sin_zero` | `sin 0 == 0` |
| `cos_zero` | `cos 0 == 1` |
| `sin_pi` | `sin pi == 0` |
| `cos_pi` | `cos pi == -1` |
| `ln_one` | `ln 1 == 0` |
| `ln_e` | `ln e_const == 1` |
| `exp_zero` | `exp 0 == 1` |
| `exp_one` | `exp 1 == e_const` |
| `atan_zero` | `atan 0 == 0` |
| `atan_one_sqrt3` | `atan(1/sqrt 3) == pi/6` |
| `sinh_zero` | `sinh 0 == 0` |
| `cosh_zero` | `cosh 0 == 1` |
| `tanh_zero` | `tanh 0 == 0` |
| `atanh_zero` | `atanh 0 == 0` |

**Identities**, to rewrite or to hand to a check:

| Entry | States |
|---|---|
| `sqrt_sq` | `sqrt(u^2) == u @ u >= 0` |
| `atan_odd` | `atan(-u) == -atan u` |
| `sqrt_sq_val` | `(sqrt a)^2 == a @ a >= 0` |
| `pyth` | `(sin u)^2 + (cos u)^2 == 1` |
| `pyth_cos` | `(cos u)^2 == 1 - (sin u)^2` |
| `sin_add` | `sin(u + v) == sin u * cos v + cos u * sin v` |
| `cos_add` | `cos(u + v) == cos u * cos v - sin u * sin v` |
| `sin_odd` | `sin(-u) == -sin u` |
| `cos_even` | `cos(-u) == cos u` |
| `tan_def` | `tan u == sin u / cos u @ cos u # 0` |
| `tanh_def` | `tanh u == sinh u / cosh u` |
| `cosh_sq` | `(cosh u)^2 == 1 + (sinh u)^2` |
| `exp_neg` | `exp(-u) == 1/exp u` |
| `exp_ln` | `exp(ln u) == u @ u > 0` |

**Signs and bounds**, usually as a `fact`:

| Entry | States |
|---|---|
| `pi_pos` | `pi > 0` |
| `e_gt_one` | `e_const > 1` |
| `sqrt_pos` | `sqrt a > 0 @ a > 0` |
| `sqrt_nonneg` | `sqrt a >= 0 @ a >= 0` |
| `sin_nonneg_on` | `sin u >= 0 @ u >= 0, u <= pi` |
| `cos_nonneg_on` | `cos u >= 0 @ u >= 0, u <= pi/2` |
| `cos_le_one` | `cos u <= 1` |
| `cos_ge_neg_one` | `cos u >= -1` |
| `exp_pos` | `exp u > 0` |
| `cosh_pos` | `cosh u > 0` |
| `ln1p_pos` | `ln(1 + u) > 0 @ u > 0` |

## When you are stuck

- **`?`, `??`, `???`** (`C-c C-t`): three hint levels on the current
  integral: what kind of move, which technique, how for this integral.
  **The highest level you use is what the gate measures.**
- **The refusal** says which kind of stuck it is: nothing matches (and
  what would), a condition failed (with the counterexample), or the
  algebra does not close (with the residual, and often a corrected
  sentence).
- **The palette**, under the goal, lists moves that fit and rewrites that
  match.
- **Parse echo** shows how a term is read.
- **∫ Evaluate** (`C-c C-e`) asks SymPy for the value and has the kernel
  prove it, writing the proof as a script. It needs SymPy in `python3`,
  or `./calc --sympy PYTHON`. It gives away the whole answer, and it is
  not counted as a hint (see below).

## Before the gate

`app/GATE.md` is the test of whether this tool teaches: seventeen problems
in a fixed order, with the highest hint level you use on each one recorded.
It passes if the last third needs less help than the first third. To keep
that reading honest:

- **Work the twelve lessons first**, so that the notation is not what you are
  learning during the gate.
- **Don't read a gate problem's `reference_proof`** in
  `kernel/problems/` before working it. The page never shows it.
- **Leave `ode.P1A_SEP`, `ode.P1B_ENERGY` and `ode.P1C_QUAD` until
  after the gate.** They are not gate problems, but their antiderivatives
  answer `unit00.P3A_SEPARATE`, `unit00.P9A_V` and `unit00.P1C_REDUCE`.
- **∫ Evaluate is not recorded as a hint.** The work file counts
  evaluations, but the gate's reading uses only the hint level. Using it on
  a gate problem would make the problem look easy without the tool having
  taught anything.

Other problems in the picker that are not in the gate and are safe to
practise on: `stage1.SUB2` (a root in the divisor) and `trig.COS_SQ`.
