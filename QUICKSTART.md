# Quickstart: the language by worked examples

Twelve short lessons, each a complete script that the kernel checks to
`Proved.` They start with the smallest proof there is and end with an
equation of motion. On the way they show what each move needs, the
entries you evaluate with, and what a refusal tells you. Each lesson ends
with an exercise for you to write yourself.

The lesson scripts are `tutorial/01-ftc.dx` to `12-ode.dx`. The exercises
are in `tutorial/exercises/`, and their solutions in `tutorial/solutions/`.
`app/test_tutorial.py` proves every lesson and every solution, runs
every other example on this page, and checks that the text quoted after
each refusal is what the checker says.

## Starting it

```
./calc
```

Then open http://127.0.0.1:8765/. It needs Python 3.12 or newer.

The page has three panes:

- **Problem** (left): the problem picker, with Start, Export, Import and
  **Start fresh**; **Your own goal**, a form with Goal, Functions and
  Assuming fields; **Parse echo**, which shows how a term you type is
  read; and **Attempts**, the tree of everything you have tried, with
  retracted branches kept and struck through.
- **Script** (centre): where you type tactics. `Alt+↓` checks the next
  sentence, `Alt+↑` retracts the last one, and `Ctrl+Enter` checks or
  retracts up to the cursor. Checked text is shaded green. Editing inside
  it retracts back to the sentence you edited. The toolbar also has the
  hint buttons `?` `??` `???`, **Tactics** (a short syntax list),
  **Pretty** (two-dimensional input) and **∫ Evaluate**.
- **Goals** (right), from the top:
  - the current goal, and a progress note after each step;
  - a palette of moves and rewrites that fit (click one to insert it);
  - the **Antiderivative card**, a collapsible list of standard forms and
    their antiderivatives, with the rows that match the goal's integral
    marked;
  - **Factor over ℚ**, **Factor over ℝ** and **Partial fractions**, when
    the goal's first integral is a quotient of polynomials;
  - the facts you have bound, and the obligations.

  Below them are the **Evaluate** and **Classify** boxes and the
  **Response**, which holds the last success, refusal or hint.

**Running a lesson on the page.** Every lesson file starts with a header
sentence, which the page takes in the left pane rather than the script:

- `problem stage0.S1.` means: choose `stage0.S1` in the picker and press
  Start.
- `goal G @ D functions f/1 assuming a1; a2.` means: open **Your own
  goal**, put `G @ D` in Goal, `f/1` in Functions and each assumption on
  its own line in Assuming. Leave out the header's `;` between assumptions
  and its final `.`, then press Start.

Paste the rest of the file into the script pane and step through it. The
`(* ... *)` comments can stay: they are comments to the checker too.

**Start resumes saved work.** The page saves every goal's work and brings
it back on Start. So when a second example uses the same problem or goal
as one you have finished, as several below do, press **Start fresh**. The
old work is kept as a `.prev.json` file, one generation only: a second
Start fresh replaces it.

**Running a lesson in Emacs.** Load the mode once, with
`(load "/path/to/calculus-checker/emacs/dx-mode.el")` in your init, then
open the file itself. `dx-mode` (Emacs 29+) runs `./calc --lsp` and
checks the whole buffer as you type. The checked part is shaded and a
refused sentence is underlined. Press `C-c C-l` to lay out the two side
windows, since nothing opens them for you:

- `*dx-goals*` shows the goal at point;
- `*dx-response*` shows a refusal's full message and suggestion, hints
  and evaluations.

The other keys are `C-c C-t` for the next hint, `C-c C-a` to use a
refusal's suggestion, `C-c C-e` to evaluate, and `C-c TAB` to complete a
move name into its template. Emacs saves no work: the buffer is your
work. Doom users: `emacs/doom/dx/README.org`.

## Writing terms

The grammar (`kernel/GRAMMAR.md`) is strict on purpose: each of these
refusals stops a misreading that would otherwise prove something you did
not mean.

| Write | Not | Why |
|---|---|---|
| `2*x` | `2x` | no implicit multiplication |
| `exp(x)`, `exp x` | `e^x` | bare `e` is not a name. `e_const` is the number e, but `e_const^x` is a real power that no derivative rule handles, so write eˣ as `exp x` |
| `sin x`, `x*y` | `sinx`, `xy` | a name is one letter (plus digits or `_suffix`) or a Greek word: `v0`, `x_1`, `theta` |
| `ln x` | `log x` | |
| `1/2` | `0.5` | no decimals |
| `(sin x)^2`, `sin(x^2)` | `sin(x)^2` | ambiguous, so refused |
| `exp(-x)` | `exp -x` | an unbracketed argument cannot start with `-` |
| `x^(-1)` | `x^-1` | bracket a negative exponent |
| `x*(x + 1)` | `x(x + 1)` | only declared functions are called |

Write roots with `sqrt`. `x^(1/2)` parses, but no rule differentiates a
fractional power, so an antiderivative written that way is always
refused.

A real power whose exponent becomes a whole number, such as `2^x` at
x = 1, prints as `rpow(2, 1)`, not `2^1`. The two differ: `rpow(2, 1)`
is only defined because 2 > 0, while `2^1` is plain multiplication. The
entry `rpow_int` turns one into the other and owes that condition.
Auto-simpl applies it for you.

A function's argument can go without brackets. It takes in a power but
stops at `*`, `/`, `+` and `-`. `D[x]` reads its argument the same way,
so bracket anything longer than one factor. **Parse echo** shows how
anything reads, under the functions of the goal you have started:

| You type | It reads |
|---|---|
| `sin x*y` | `sin x * y` |
| `sin x^2` | `sin(x^2)` |
| `D[t] w*tanh(t)` | `D[t] w * tanh t` |
| `D[t] (w*tanh(t))` | `D[t](w*tanh t)` |

The rest of the notation:

- The constants are `pi` and `e_const`. Infinity is `oo`, and appears only
  as an integral's end or an open interval's end, such as `[0, oo)`.
- `Int[x = a .. b] e` is the integral of `e` over x from a to b.
  `D[x] e` is the derivative of `e` with respect to x.
- A goal is `left == right`, or an order `<=` `<` `>=` `>`, optionally
  followed by `@` and what may be assumed: `@ a > 0, b > 0`, or an
  interval `@ b in [0, 1)`. `?A` is the unknown value you are asked to
  find. A chain such as `0 < x < 1` is written `0 < x, x < 1`.
- In obligations: `e # 0` means e ≠ 0. `e in C^0(I)` means e is continuous
  on I. `e in C^1(I)` means e is differentiable on I, with a continuous
  derivative. `[a, b]` includes its ends and `(a, b)` does not. What
  follows `@` is where the claim must hold.
- A tactic is one sentence ending in `.`. `(* ... *)` is a comment.

## Lesson 1: the whole loop

`ftc F` claims that F is an antiderivative of the integrand. The kernel
differentiates F by its rule table and compares F′ with the integrand
using `ring`, which is algebra with `+ - *` and whole powers. If they
agree, the integral becomes F(b) − F(a). `close V` names the value.
This lesson turns **auto-simpl** off first, so that you name it.

`tutorial/01-ftc.dx`:

```dx
(* Lesson 1. The whole loop: an integral, an antiderivative, a value.
   Goal: Int[x = 0 .. 1] 3*x^2 + 2*x == ?A *)
problem stage0.S1.

(* Auto-simpl finishes a goal that is only constants by itself. It is
   off for this lesson, so that you name the value yourself. *)
Unset Auto Simpl.

(* You propose F. The kernel differentiates it, checks F' against the
   integrand with ring, and replaces the integral by F(1) - F(0). *)
ftc x^3 + x^2 by ring.

(* The goal is now 1^3 + 1^2 - (0^3 + 0^2) == ?A. Name the value. *)
close 2 by ring.
```

Once the goal is only constants, as it is after `ftc` here, nothing is
left but evaluating it. **Auto-simpl**, which is on unless you turn it
off, does that by itself. So with it on, the proof is the `ftc` alone:

```dx
problem stage0.S1.
ftc x^3 + x^2 by ring.
```

The status pane lists what auto-simpl did, here `close 2 by ring.` It
does the arithmetic, and applies the entries of lesson 2 that a value
still needs, but never chooses a technique. Each of those steps is an
ordinary move the kernel checks as if you had typed it, and if one
fails, the goal is left as `ftc` left it. `Unset Auto Simpl.` turns it
off from that point of the script, and `Set Auto Simpl.` turns it back
on. Lessons 2 and 6 turn it off, because the moves it would make are
what they teach.

With it off, `simpl.` does the arithmetic when you ask, and closes with
the result, `?A := 2`. It is still a `close`: the computed value is
checked as a typed one is.

```dx
problem stage0.S1.
Unset Auto Simpl.
ftc x^3 + x^2 by ring.
simpl.
```

Get it wrong and the kernel says by how much (press Start fresh first):

```dx
problem stage0.S1.
ftc x^3 + x.
(* refused: ftc-check-failed "ring leaves lhs - rhs = -2*x + 1" *)
```

The response reads `ring leaves lhs - rhs = -2*x + 1` and shows where F′
and the integrand diverge. **Nothing is accepted that was not checked.**
The status line's `0 machine-checked` is honest: the kernel itself is not
formally verified (`DESIGN.md` §14).

Behind every step is a list of **obligations**: what must be true for the
step to be valid. For `ftc` these are:

- the integrand is continuous on [0, 1] (`C^0`);
- F is continuous on [0, 1] and continuously differentiable inside
  (`C^1`);
- F′ is the integrand.

Each obligation is shown with how it was discharged (`reg`, `deriv+ring`,
…). An obligation that is false refuses the step, and so does a goal
that owes one. An integral across a pole is refused before any move:

```dx
goal Int[x = -1 .. 1] 1/x^2 == ?A.
(* refused: obligation-decided-false "x^2 # 0 @ [-1, 1] is false at x = 0" *)
```

The response reads `x^2 # 0 @ [-1, 1] is false at x = 0`.

**Your turn:** `tutorial/exercises/01-ftc.dx`,
`goal Int[x = 0 .. 2] 4*x^3 - 3*x^2 + 1 == ?A.`

## Lesson 2: values must be evaluated

`close` accepts only a value in closed form: `exp 1` is not an answer,
`e_const` is. The **entries** (listed [below](#the-entries)) are the
known facts that take you there: `rewrite E at T` replaces the subterm
`T` using entry `E`.

`tutorial/02-evaluate.dx`:

```dx
(* Lesson 2. Values must be fully evaluated: exp 1 is not an answer,
   e_const is. The rewrite entries turn one into the other.
   Goal: Int[x = 0 .. 1] x*exp(x^2) == ?A *)
problem stage0.S2.

(* This lesson makes the moves auto-simpl would make after ftc, so it
   is off. *)
Unset Auto Simpl.

(* The inner derivative is 2x, so F carries a 1/2. *)
ftc exp(x^2)/2 by ring.

(* Now exp(1^2)/2 - exp(0^2)/2 == ?A. The entry exp_one says
   exp 1 == e_const; `at` names the subterm to rewrite. *)
rewrite exp_one at exp(1^2).
rewrite exp_zero at exp(0^2).

(* e_const/2 - 1/2 == ?A: only constants, and only arithmetic left.
   simpl does it and closes, here with ?A := (1/2)*e_const - 1/2.
   close (e_const - 1)/2 would do as well: any form of the value
   passes, as long as it is evaluated. *)
simpl.
```

With auto-simpl on, `ftc exp(x^2)/2.` alone proves this: auto-simpl
makes these two rewrites and the `close` itself. They are the moves
the refusals below would name, in the same order.

Closing too early names the entry still to use:

```dx
problem stage0.S2.
Unset Auto Simpl.
ftc exp(x^2)/2.
close (exp 1 - exp 0)/2.
(* refused: close-not-evaluated "exp 1 can still be evaluated (exp_one)" *)
```

The response reads `exp 1 can still be evaluated (exp_one)`. With
auto-simpl off, `simpl` is no way round it. It does the literal
arithmetic, inside a function's argument too, and nothing else: applying
an entry is your move, and it names the one left the same way.

```dx
problem stage0.S2.
Unset Auto Simpl.
ftc exp(x^2)/2.
simpl.
(* refused: close-not-evaluated "exp 1 can still be evaluated (exp_one)" *)
```

When an antiderivative is off by a constant factor, the refusal carries
a corrected sentence. On the page, **Use this** puts it in place of
yours; in Emacs it is `C-c C-a`.

```dx
problem stage0.S2.
ftc exp(x^2).
(* refused: ftc-check-failed "Your F′ is 2 times the integrand. Scale F by 1/2." "ftc (exp(x^2))/2 by ring." *)
```

The response reads `Your F′ is 2 times the integrand. Scale F by 1/2.`,
with the suggestion `ftc (exp(x^2))/2 by ring.`

**Your turn:** `tutorial/exercises/02-evaluate.dx`,
`goal Int[x = 0 .. pi/2] cos x == ?A.`

## Lesson 3: `ring` and `field`

`ring` is the default check. Dividing by a number is just a
coefficient to it, as in lesson 2's `exp(x^2)/2`. Any other quotient
`a/d` it treats as `a` times an opaque `1/d`, so it passes whenever both
sides hold the same quotients. `field` also cancels and
combines divisors, and every divisor it uses becomes an obligation that
it is nonzero. **Start with `ring`. If its residual still has a `1/(…)` of
something that is not a number, switch to `field`.**

```dx
goal Int[x = 1 .. 2] (x + 1)/x == ?A.
ftc x + ln x by ring.
(* refused: ftc-check-failed "ring leaves lhs - rhs = -x*(1/x) + 1" *)
```

The response reads `ring leaves lhs - rhs = -x*(1/x) + 1`: `ring` cannot
cancel x against 1/x.

`tutorial/03-field.dx`:

```dx
(* Lesson 3. ring treats a quotient a/d as a times an opaque 1/d, so
   it passes when both sides hold the same quotients. When a divisor
   has to cancel, as x*(1/x) = 1 does here, it takes field.
   Goal: Int[x = 1 .. 2] (x + 1)/x == ?A *)
goal Int[x = 1 .. 2] (x + 1)/x == ?A.

(* F' is 1 + 1/x; the integrand is (x + 1)*(1/x). by ring leaves
   -x*(1/x) + 1. by field cancels, and owes x # 0 on (1, 2), which
   the obligations pane shows discharged from the range. *)
ftc x + ln x by field.

(* That leaves 2 + ln 2 - (1 + ln 1) == ?A, only constants, and
   auto-simpl finishes: it rewrites ln 1 by the entry ln_one, then
   closes with ln 2 + 1. The status pane lists both moves. *)
```

**Your turn:** `tutorial/exercises/03-field.dx`,
`goal Int[x = 1 .. 2] (x^2 + 1)/x^2 == ?A.`

## Lesson 4: substitution, "let u = x²"

`int_subst` has two modes. **Reverse** is the one you would say out loud:
u is a function of the old variable.

**Try the hints first.** Before reading the script, start `stage1.S2R`
and press `?`, `??` and `???` (in Emacs, `C-c C-t` three times). They name the
kind of move, then the technique, then how it applies here, in that order.

`tutorial/04-subst-reverse.dx`:

```dx
(* Lesson 4. Substitution the way you would say it: "let u = x^2".
   Goal: Int[x = 0 .. 1] x*exp(x^2) == ?A, lesson 2's integral again. *)
problem stage1.S2R.

(* Reverse mode. Read `x := x^2 as u` as "replace x by u, where
   u = x^2": the name before := is the variable the integral is over
   now, the one after `as` is the new one. `from 0 to 1` are u's ends
   (0^2 and 1^2), and `reverse` gives the integrand in u. The kernel
   checks x*exp(x^2) == exp(x^2)/2 * 2x, that is f(u(x)) * u'(x). *)
int_subst x := x^2 as u from 0 to 1 reverse exp(u)/2 by ring.

(* Int[u = 0 .. 1] exp(u)/2 == ?A. After ftc, auto-simpl makes
   lesson 2's two rewrites and closes. *)
ftc exp(u)/2 by ring.
```

**Your turn:** `tutorial/exercises/04-subst-reverse.dx`,
`goal Int[x = 0 .. 1] 2*x*(x^2 + 1)^3 == ?A.`

## Lesson 5: substitution, x = φ(t)

**Forward** mode is the other direction: the old variable is a function
of the new one. This is the mode for killing a root.

`tutorial/05-subst-forward.dx`:

```dx
(* Lesson 5. Forward substitution, x := phi(t): kill a root.
   Goal: Int[x = 0 .. 1] x*sqrt(1 - x) == ?A *)
problem stage1.SUB1.

(* x = 1 - t^2 makes 1 - x a square. `from 1 to 0` names the t that
   lands on each old end, in order: phi(1) = 0 and phi(0) = 1, which
   the kernel checks. The new integral is written as f(phi(t)) *
   phi'(t), with phi' as the rule table produces it, unsimplified:
   Int[t = 1 .. 0] (1 - t^2)*sqrt(1 - (1 - t^2))*(0 + (0*t^2 + (-1)*(2*t^1*1)))
   The last factor is -2t. ring sees through that form, so nothing
   needs tidying by hand. Two plain-number ends are kept as written,
   so the range stays 1 .. 0, and ftc takes it as it stands. *)
int_subst x := 1 - t^2 as t from 1 to 0 by ring.

(* sqrt(t^2) is t only because t >= 0 on the range; sqrt_sq carries
   that condition, and the kernel discharges it from the range. *)
rewrite sqrt_sq with u := t at sqrt(1 - (1 - t^2)).

(* The integrand is now (1 - t^2)*t*(-2t) = 2t^4 - 2t^2. *)
ftc (2/5)*t^5 - (2/3)*t^3 by ring.

(* Only constants left: auto-simpl computes 4/15 and closes. *)
```

An entry with a condition (`sqrt_sq`: `sqrt(u^2) == u @ u >= 0`) is
instantiated with `with u := T;`, and in a `rewrite` its condition
becomes an obligation at once.

**Your turn:** `tutorial/exercises/05-subst-forward.dx`,
`problem stage1.SUB2.`

## Lesson 6: facts, for the checks

A `rewrite` changes the goal. A `fact` changes nothing: it binds an entry
to a name, and `using h` hands it to a check. Use one when a check needs
an identity to see that two sides agree.

- **Facts go to `field`**: write `by field using h`. `ring`, which is also
  what you get with no `by`, takes none, and a `using` list under it is
  refused as `bad-args`. The one exception is `bound`'s single order
  fact.
- **A fact's left side must be one function application, or a power of
  one**, such as `(sqrt a)^2` or `exp 0`. `pyth`, whose left side is a
  sum, can be bound, but every check refuses it (`field-fact-shape`). Use
  `pyth_cos` instead.
- **A fact's condition is checked where the fact is used,** not when you
  bind it. A refusal can come from the `with` in an earlier `fact`.

Without the fact, the refusal names it:

```dx
goal Int[x = 0 .. 1] sqrt(x + 1) == ?A.
ftc (2/3)*(x + 1)*sqrt(x + 1) by field.
(* refused: ftc-check-failed "The difference is zero by the identity sqrt_sq_val: the answer is right, written another way" "Bind it as a fact and check by field using it." *)
```

The response reads `The difference is zero by the identity sqrt_sq_val:
the answer is right, written another way`, followed by `Bind it as a fact
and check by field using it.`

`tutorial/06-facts.dx`:

```dx
(* Lesson 6. Facts: a known identity bound to a name and handed to a
   check. Goal: Int[x = 0 .. 1] sqrt(x + 1) == ?A *)
goal Int[x = 0 .. 1] sqrt(x + 1) == ?A.

(* The last two moves are ones auto-simpl would make, so it is off. *)
Unset Auto Simpl.

(* F = (2/3)(x + 1)^(3/2), written with sqrt. Its derivative has
   1/(2*sqrt(x + 1)) in it; clearing that divisor, field meets
   (sqrt(x + 1))^2, an opaque square, so the check needs
   (sqrt a)^2 == a with a := x + 1. `fact` binds it to h; its
   condition, x + 1 >= 0, is checked where h is used. *)
fact h := sqrt_sq_val with a := x + 1.

(* Facts go to field only: `by field using h`. *)
ftc (2/3)*(x + 1)*sqrt(x + 1) by field using h.

(* (2/3)*(1 + 1)*sqrt(1 + 1) - (2/3)*(0 + 1)*sqrt(0 + 1) == ?A.
   simpl does arithmetic, inside sqrt too, so sqrt(1 + 1) would come
   out as sqrt 2, a closed form. sqrt(0 + 1) would come out as
   sqrt 1, which an entry still evaluates, and that move is yours.
   sqrt_sq's left side, sqrt(u^2) with u := 1, is sqrt(1^2), equal
   to sqrt(0 + 1) up to ring, so it applies there. *)
rewrite sqrt_sq with u := 1 at sqrt(0 + 1).

(* Now simpl computes (4/3)*sqrt 2 - 2/3. *)
simpl.
```

With `using` but no `by field`:

```dx
goal Int[x = 0 .. 1] sqrt(x + 1) == ?A.
fact h := sqrt_sq_val with a := x + 1.
ftc (2/3)*(x + 1)*sqrt(x + 1) using h.
(* refused: bad-args "ftc takes F, check, facts" *)
```

That message, `ftc takes F, check, facts`, is not much help; it means the
check refused the facts. Inside `ftc` only, `field` also tries the trig
entries on its own after failing: the addition formulas, parity,
`tan_def` and `pyth_cos`, on sin, cos and tan of multiples of one angle.
So a trig identity of that kind needs no fact there, but one mixing two
angles, such as sin(x + 1) against sin x and cos 1, does.

**Your turn:** `tutorial/exercises/06-facts.dx`,
`goal Int[x = 0 .. 3] x/sqrt(x + 1) == ?A.`

## Lesson 7: your own goal, with parameters

Anything after `@` is assumed. Parameters are ordinary letters, and the
obligations use the assumptions.

`tutorial/07-parameters.dx`:

```dx
(* Lesson 7. Your own goal, with a parameter and an assumption about it.
   Everything after @ is what you may assume. The kernel must know
   which of 0 and a is the lower end before it can state anything on
   the range; a > 0 tells it (a < 0 would too). *)
goal Int[x = 0 .. a] x^2 == ?A @ a > 0.

ftc x^3/3 by ring.
close a^3/3 by ring.
```

`simpl` computes only constants, so a value with a parameter in it is
named with `close`. Auto-simpl, for the same reason, leaves this goal to
you:

```dx
goal Int[x = 0 .. a] x^2 == ?A @ a > 0.
ftc x^3/3 by ring.
simpl.
(* refused: bad-tactic "simpl computes the value of a goal that is only constants, and this one has the variable a" *)
```

Without an assumption that orders the ends, the goal itself is refused:

```dx
goal Int[x = 0 .. a] x^2 == ?A.
(* refused: orientation-undecided "the order of 0 and a is not decided" *)
```

A reversed range is legal. `int_flip` turns `Int[x = b .. a] e` into
`Int[x = a .. b] -e` when you want it the usual way round:

```dx
goal Int[x = 1 .. 0] 2*x == ?A.
int_flip.
ftc -(x^2).
```

Auto-simpl closes it with `?A := -1`.

**Your turn:** `tutorial/exercises/07-parameters.dx`,
`goal Int[x = 0 .. a] 2*x + c == ?A @ a > 0.`

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

(* Only constants are left, and auto-simpl finishes: rewrite exp_one
   at exp 1, then exp_zero at exp 0, then close 1. A rewrite replaces
   every copy of its `at` term that is written exactly the same, so
   each one takes both copies here. *)
```

`occurrence N` works the same way wherever a move could apply at more than
one place (`ftc`, `int_improper`, `rewrite`, `int_subst`, `int_flip`,
`int_parts`).

**Your turn:** `tutorial/exercises/08-parts.dx`,
`goal Int[x = 0 .. pi] x*sin x == ?A.`

## Lesson 9: an infinite end

`tutorial/09-improper.dx`:

```dx
(* Lesson 9. An infinite end: F(oo) is a limit, and the kernel takes it. *)
goal Int[x = 0 .. oo] exp(-x) == ?A.

(* Like ftc, but also checks that F has a finite limit at the infinite
   end and puts that limit in F(oo)'s place: here 0. *)
int_improper -exp(-x) by ring.

(* -0 - (-exp(-0)) == ?A, and auto-simpl finishes: rewrite exp_zero at
   exp(-0), then close 1. The `at` term is the goal's own, exp(-0);
   exp_zero's left side, exp 0, only has to equal it up to ring, which
   it does. *)
```

**Your turn:** `tutorial/exercises/09-improper.dx`,
`goal Int[x = 1 .. oo] 1/x^2 == ?A.`

## Lesson 10: an inequality, from Taylor's theorem

Not every goal has a `?A`. An order goal is proved by building a fact that
implies it. `taylor_lagrange` mints the lower or upper bound of a Taylor
remainder, provided the last derivative you list has a known sign. `bound`
closes the goal from that fact. The hint buttons read integrals, so on an
order goal they answer `the goal holds no integral`.

`tutorial/10-taylor.dx`:

```dx
(* Lesson 10. An order goal: prove an inequality, not find a value.
   Taylor's theorem with a monotone remainder, then `bound`. *)
goal b^2/2 <= exp b - (1 + b) @ b in [0, 1).

fact h0 := exp_zero.

(* The general rule: `of f in u from a to c at p derivs D1; ...; Dm`
   lists f's first m derivatives. The Taylor polynomial has order
   n = m - 2: T = f(a) + D1(a)(p - a) + ... + Dn(a)(p - a)^n/n!.
   `increasing` says Dm >= 0 on (a, c), so D(n+1) grows, and then with
   W = (p - a)^(n+1)/(n+1)!:
     lower:  D(n+1)(a) * W  <=  f(p) - T
     upper:  f(p) - T  <=  D(n+1)(p) * W
   (`decreasing` swaps a and p.) Here f = exp u, a = 0, p = b, m = 3,
   so n = 1, T = exp 0 + exp 0 * (b - 0) and W = (b - 0)^2/2. `lower`
   binds hl: exp 0*((b - 0)^2/2) <= exp b - (exp 0 + exp 0*(b - 0)).
   The goal is unchanged. *)
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
(* refused: bound-check-failed "(1/2)*b^2*exp 0 - (1/2)*b^2 + b*exp 0 - b + exp 0 - 1" *)
```

The residual is `(1/2)*b^2*exp 0 - (1/2)*b^2 + b*exp 0 - b + exp 0 - 1`,
which is `exp 0` everywhere 1 should be. No pane shows what a minted fact
states, so the rule in the comment above is how to know.

**Your turn:** `tutorial/exercises/10-taylor.dx`,
`goal exp b - (1 + b) <= exp b * b^2/2 @ b in [0, 1).`

## Lesson 11: checking a candidate solution

`verify` closes an equation with no `?A`. It differentiates every `D` node
and checks the two sides agree. Solving a differential equation then
becomes guess and check: propose y(t), and let `verify` confirm it.

`tutorial/11-verify.dx`:

```dx
(* Lesson 11. Checking a candidate solution of a differential equation.
   Does y = y0 exp(-k t) satisfy y' = -k y? *)
goal D[t] (y0*exp(-k*t)) == -k*(y0*exp(-k*t)) @ k > 0.

(* verify differentiates every D[t] node with the rule table, then
   checks the two sides agree by ring (or field). No ?A, no value.
   First derivatives only: a D inside a D is refused. *)
verify by ring.
```

An initial condition is the same move on a goal with no `D`:

```dx
goal y0*exp(-k*0) == y0 @ k > 0.
rewrite exp_zero at exp(-k*0).
verify by ring.
```

A second derivative is refused:

```dx
goal D[t] D[t] (A*cos(w*t)) == -w^2*(A*cos(w*t)).
verify by ring.
(* refused: verify-nested-D "second derivatives are not built" *)
```

The **Classify** box on the page reads a force F in m x″ = F and names
the case:

- F(t): integrate once;
- F(v): separate;
- F(x): multiply by the velocity;
- constant: every case applies, and integrating once is the shortest;
- none: with each parameter that, set to zero, would reduce it to one
  case, if there is any.

Try `F0*cos(omega*t)`.

**Your turn:** `tutorial/exercises/11-verify.dx`,
`goal D[t] (y0/(1 + y0*t)) == -(y0/(1 + y0*t))^2 @ y0 > 0, t >= 0.`

## Lesson 12: reasoning from an equation of motion

When the solution is not in hand, state what you know about the unknown
function and derive from that. `functions v/1` declares v, and
`assuming` names each fact about it. Three moves read such a law, one for
each case Classify names:

- `quad_t` for F(t) and a constant force;
- `sep_autonomous` for F(v);
- `energy_integral` for F(x).

Each mints a handle that `verify` then uses. This lesson works
`quad_t`. The other two take more clauses (`rate`, `range`, `given`,
`kinematic`), described in `app/SCRIPT.md`.

`tutorial/12-ode.dx`:

```dx
(* Lesson 12. Reasoning from an equation of motion you did not solve.
   `functions v/1` declares v as an unknown function of one argument;
   `assuming` states what is known about it on s in [0, oo): the law
   (named eom) and that v is C^1 (named regv). *)
goal v(t) == v(0) + F0*t/m @ m > 0, t >= 0 functions v/1 assuming eom: m*D[s] v(s) == F0 for s in [0, oo); regv: v in C^1 for s in [0, oo).

(* A constant force, the simplest case of one that depends on time
   only: integrate once. quad_t reads eom as m v' = R(s), checks your
   antiderivative F of R/m, and binds h: v(t) == v(0) + (F(t) - F(0)). *)
quad_t h := eom from 0 to t in u antiderivative F0*u/m regs regv by field.
verify by field using h.
```

**Your turn:** `tutorial/exercises/12-ode.dx`,
`goal v(t) == v(0) + F0*sin(w*t)/(m*w) @ m > 0, w > 0, t >= 0 functions v/1 assuming eom: m*D[s] v(s) == F0*cos(w*s) for s in [0, oo); regv: v in C^1 for s in [0, oo).`

## Complex numbers

`i` is the imaginary unit. A complex variable is declared in the header,
`complex z, w`, after the goal (and before `functions`); every other letter
is real. `re`, `im`, `conj` and `abs` are what they say. `Log`, `Arg` and
`Sqrt` are the principal branches. `log[θ]`, `arg[θ]` and `sqrt[θ]` cut
along the ray at angle θ instead, and θ must be a number like `2*pi`.

An equation between complex terms holds when the real parts agree and the
imaginary parts agree, and the kernel checks exactly that:

```dx
goal z*conj z == ?A complex z.
close (re z)^2 + (im z)^2.
```

A complex constant is evaluated when it is in the form `a + b*i`, with a
and b real and evaluated. `rewrite parts at T` turns T into that form, and
the real entries finish it. Auto-simpl makes those moves itself, so a
constant goal is one `simpl.`:

```dx
goal (1 + i)^8 == ?A.
simpl.
```

By hand, with the values of `ln` and `Arg` at the end:

```dx
goal Log(-1) == ?A.
Unset Auto Simpl.
rewrite parts at Log(-1).
rewrite ln_one at ln 1.
rewrite arg_neg with u := -1 at Arg(-1).
close i*pi.
```

Closing too early names `parts`:

```dx
goal (1 + i)^8 == ?A.
Unset Auto Simpl.
close (1 + i)^8.
(* refused: close-not-evaluated "(1 + i)^8 can still be evaluated (parts)" *)
```

There is no order on complex numbers, so `z < 1` is refused: compare
`re z`, `im z` or `abs z` instead. `ln z` and `sqrt z` are refused too,
because those are the real functions: write `Log z` and `Sqrt z`.

Calculus in a real variable works on complex values, part by part, and
that is often the short way to a real integral. ∫₀^∞ e^{−x} sin x dx is
the imaginary part of ∫₀^∞ e^{(−1+i)x} dx, and the limit at `oo` comes from
the modulus: |e^{(−1+i)x}| = e^{−x} → 0.

```dx
goal Int[x = 0 .. oo] exp(-x)*sin x == ?A.
int_improper im(exp((-1 + i)*x)/(-1 + i)) by field.
```

`D[z]` is the complex derivative. It takes only what is holomorphic:
`D[z] conj z` is refused `deriv-not-holomorphic`, and so are `re`, `im`,
`abs` and `Arg`. `Log` and `Sqrt` differentiate where their argument is off
the cut, which they owe:

```dx
goal D[z] Log z == 1/z @ re z > 0 complex z.
verify by field.
```

A contour integral is defined by its parametrisation. `cint_param`
replaces it with ordinary integrals in a real variable `t`, one per piece
of the path, which `ftc` then closes:

```dx
goal CInt[w on circle(0, 1)] 1/w == ?A complex w.
cint_param.
(* Int[t = 0 .. 2*pi] (1/exp(i*t))*(i*exp(i*t)) == ?A *)
ftc i*t by field.
```

Paths are `seg(a, b)`, `arc(c, r, t1, t2)`, `circle(c, r)` and
`path[s = a .. b] phi`, joined by `++` and reversed by `rev`. A join owes
that one piece ends where the next starts.

On a closed path, `residues` applies the residue theorem in one move. It
finds the poles, counts how often the path winds round each, and replaces
the integral by 2πi times the winding-weighted residues. Here it writes
`2*pi*i*(1/(i + i))`, since only the pole at `i` is inside, and
auto-simpl evaluates that to `pi`:

```dx
goal CInt[w on circle(i, 1)] 1/(w^2 + 1) == ?A complex w.
residues.
```

Every hypothesis of the theorem is owed: the path is closed, the function
is holomorphic off the poles, and no pole lies on the path. A function
with a cut needs a region that avoids the cut, given as open half-planes
and disks: `residues in re w > 0.` for `Log w` on `circle(2, 1)`.

An integral over the whole real line closes in a half-plane:
`residues upper` (or `lower`) replaces it with 2πi times the residues
there. That needs the integrand to decay, and the kernel checks it: a
rational function needs the denominator's degree at least two above the
numerator's, and with a factor `exp(i*a*x)` (Jordan's lemma) one above,
with `a > 0` for upper. `int_even` turns an even integrand on `[0, oo)` into
half of the whole line:

```dx
goal Int[x = 0 .. oo] 1/(x^2 + 4)^2 == ?A.
int_even.
residues upper.
```

## The moves

| Move | Does | Lesson |
|---|---|---|
| `ftc F` | ∫ f → F(b) − F(a), checking F′ = f | 1 |
| `close V` | names `?A`; V must be fully evaluated | 1, 2, 7 |
| `simpl` | `close V` with V computed, once the goal is only constants; with auto-simpl on, also the entries a value still needs | 1, 2, 6 |
| `Set Auto Simpl`, `Unset Auto Simpl` | turn auto-simpl on (the default) or off: after a move that leaves only constants, it makes the evaluation moves and closes, each checked by the kernel | 1, 2, 6 |
| `rewrite E at T` | replaces T by an entry | 2 |
| `rewrite parts at T` | replaces a complex T by `re T + i*im T` | Complex numbers |
| `int_subst` | substitution, forward or `reverse` | 4, 5 |
| `fact h := E` | binds an entry for `by field using h` | 6 |
| `int_flip` | `Int[x = b .. a] e` → `Int[x = a .. b] -e` | 7 |
| `int_parts` | ∫ u v′ → [u v] − ∫ u′ v | 8 |
| `int_improper F` | `ftc` with a limit at an infinite end | 9 |
| `taylor_lagrange` | mints a Taylor remainder bound | 10 |
| `bound` | closes an order goal from one order fact | 10 |
| `verify` | closes an equation by differentiating and checking | 11 |
| `quad_t` | derives from a law in the assumptions | 12 |
| `sep_autonomous`, `energy_integral` | the same for F(v) and F(x); not worked here | 12 |

The full syntax, with every optional clause, is `app/SCRIPT.md`. That
includes `taylor_lagrange`'s `strictly` and `bound`'s `scale`, which the
lessons do not use. The page's **Tactics** button shows a short version,
and `C-c TAB` in Emacs expands a move name into its template.

## The entries

These are everything `rewrite` and `fact` can name. Schema letters (`u`,
`v`, `a`) are filled with `with u := T;`. Conditions after `@` become
obligations: at once for `rewrite`, and for `fact` wherever it is used.

A rewrite's `at T` is a subterm copied from the goal, and it replaces every
copy written exactly the same way. When the entry's left side is a
function applied to something, only the argument has to agree with `T`
up to `ring`, so `exp_zero at exp(-0)` and `sqrt_sq with u := 1 at
sqrt(0 + 1)` both work. A real power's base and exponent are matched the
same way. Any other left side, such as the power `(cos u)^2`, must match
`T` exactly.

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

**One family**, written with a whole number for `n`: `rpow_int` states
`rpow(u, n) == u^n @ u > 0` for each n, as in `rewrite rpow_int with
u := 2; n := 1 at rpow(2, 1)`. It turns a real power with a whole
exponent into plain multiplication, and owes `u > 0`.

**The argument**, `Arg` of a value on an axis or to the right of 0:

| Entry | States |
|---|---|
| `arg_pos` | `Arg u == 0 @ u > 0` |
| `arg_neg` | `Arg u == pi @ u < 0` |
| `arg_i_pos` | `Arg(i*u) == pi/2 @ u > 0` |
| `arg_i_neg` | `Arg(i*u) == -pi/2 @ u < 0` |
| `arg_right` | `Arg(u + i*v) == atan(v/u) @ u > 0` |

**Periodicity**, `sin_period` and `cos_period`: `sin(u + 2*pi*k) == sin u`
and the same for cos, k a whole number, written `with u := 0; k := 2`.
They bring sin and cos of any multiple of π back to the values above.

**One more family**, `arg_branch`, moves between cuts:
`arg[θ] w == Arg w + 2*pi*k` when the right side lies in (θ − 2π, θ],
written `with w := T; theta := 2*pi; k := 1`.

**Identities**, to rewrite with or to hand to a check as a fact (all but
`pyth`, whose left side is a sum):

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

**Signs and bounds.** These cannot be rewritten and are not facts a check
accepts. As a `fact`, one serves as the order fact `bound` closes from.
The kernel also uses them itself to discharge obligations.

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

- **`?`, `??`, `???`** (`C-c C-t`) are three hint levels on the current
  integral: what kind of move, which technique, how for this integral.
- **The refusal** says which kind of stuck it is:
  - nothing matches, with what would;
  - a condition failed, with the counterexample;
  - the algebra does not close, with the residual and often a corrected
    sentence.
- **The Antiderivative card** and **the palette**, under the goal, list
  what fits the current integrand. **Factor over ℚ/ℝ** and **Partial
  fractions** break up a quotient of polynomials, and the kernel checks
  each result before it is shown.
- **Parse echo** shows how a term is read.
- **∫ Evaluate** (`C-c C-e`) asks SymPy for the value and has the kernel
  prove it, writing the proof as a script. It gives the whole answer away.
  It needs a Python with SymPy: `python3` if that has it, otherwise
  `./calc --sympy PYTHON` on the page. In Emacs, set `dx-calc-args` to
  `("--lsp" "--sympy" "PYTHON")`, or set `CALC_SYMPY` in Emacs's
  environment.

More practice among the picker's problems: `stage0.S3` (∫ ln x / x),
`consolidation.QC1` (a quarter circle by x = cos θ) and `trig.COS_SQ`.

## If you will run the gate

`app/GATE.md` is a separate experiment, not needed to use the tool. You
work seventeen problems in a fixed order. For each problem that is worked
and on which the recognizer names a technique (ten of the seventeen), it
takes the highest hint level you pressed. It then compares the mean over
the first third of those problems with the mean over the last third,
and needs at least six of them for a verdict. None of the lessons or
exercises is one of its problems. If you plan to run it:

- **Work it on the page.** Only the page (`./calc`, without `--lsp`)
  saves the work files `app/gate.py` reads, in `calc-work/`. A problem
  worked in Emacs counts as not worked, and hints asked there are not
  recorded.
- **Only the `?` `??` `???` buttons are recorded**, and only when they
  answer: a button that refuses (`the goal holds no integral`) records
  nothing. Nothing else is recorded:
  - the palette;
  - the Antiderivative card;
  - Factor and Partial fractions;
  - Classify;
  - ∫ Evaluate;
  - the text and suggestions of every refusal. A "No rule matches here"
    refusal repeats the level-1 hint and lists the rewrites and moves that
    fit.

  Using these on a gate problem makes it look easier than it was.
- **Some material contains gate answers.** Leave these until after:
  - `ode.P1A_SEP`, which answers `unit00.P3A_SEPARATE`, `unit00.P3A_TOP`
    and part of `unit00.P3A_HEIGHT`;
  - `ode.P1B_ENERGY`, which answers `unit00.P9A_V`;
  - `ode.P1C_QUAD`, which answers `unit00.P1C_REDUCE`;
  - `kernel/GRAMMAR.md` §9, which works gate problems 1 and 2;
  - `DESIGN.md` §11;
  - `UNIT00.md`;
  - `kernel/p1_expected.py`;
  - `app/assist/gate_labels.json`;
  - every problem file's `reference_proof`.
