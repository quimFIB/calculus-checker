# Evaluating integrals — DESIGN.md §8.2 brought forward

The owner (2026-09-26): "Since we have decided a more comfortable way to
input integrals, maybe we should provide some option to evaluate
integrals." On the decision card (numeric only / numeric plus a costed
symbolic hint / full evaluator / not now) the owner chose **full
evaluator**: the closed form, any time, free. Written before the code.

This is §8.2's integrator, which DESIGN.md marks "not in v1" and "wired,
off by default, one line to enable". The owner's choice is that line.
What §8.2 fixes still holds and is the shape of this cut:

- **One entry point,** `integrate : goal -> candidate option`, with §8.2's
  failure taxonomy.
- **The proposer is SymPy, shelled out to** (§8.2, §15.5: 16/16 on the
  course's sample). It is untrusted and outside the trusted base.
- **Nothing is shown as a value unless the kernel proved it.** Like
  STUCK.md's suggestions, the candidate becomes tactic sentences that run
  through `kernel.step` from the goal, recording nothing. A candidate the
  kernel does not accept in full is reported as §8.2's third failure,
  "found F, could not verify it", never as a value.

So the evaluator can fail to answer, but it cannot give a wrong answer
with `✓` beside it. §8.2's own argument applies: a buggy proposer costs a
rejected step.

## Where it sits

```
app/assist/integrate.py      integrate(goal_text, functions) -> result; runs
                             the proposer, builds the sentences, has the
                             kernel check them, adds the numeric value
app/assist/sympy_propose.py  the proposer: a script run as a subprocess by
                             the Python that has SymPy; GRAMMAR text in,
                             GRAMMAR text out, one JSON object each way
app/api.py                   POST /evaluate/goal (the goal's text) and
                             POST /evaluate/check (the kernel's half, fast)
app/server.py                POST /evaluate: runs the proposer itself, outside
                             the worker, then /evaluate/check (review 5)
app/lsp.py                   dx/evaluate, the same two halves
app/page/index.html          an Evaluate button on the goal, and a scratch box
emacs/dx-mode.el             C-c C-e
app/test_integrate.py        the cases below
```

The app stays stdlib-only. SymPy lives in whatever Python `--sympy`
names (default: the first of `$CALC_SYMPY`, then `python3` if it can
`import sympy`). With no SymPy, `/evaluate` still answers with the numeric
value and says how to enable closed forms. Nothing under `kernel/` changes.

## What is evaluated

A **definite integral**, `Int[x = a .. b] f`, proper or improper
(`oo`/`-oo` ends), in one variable, over GRAMMAR's builtin functions.
Declared functions (`f/1`) cannot be evaluated: they are unknown.
Indefinite integrals are not in this cut: the kernel has no goal form that
checks F′ = f without an interval. There are two ways in:

1. **The goal.** `POST /evaluate {session, node}` evaluates the node's
   goal when it is `Int[...] f == ?A`. Any other goal shape is refused
   `not-an-integral-goal`, and the response names the shape it wants.
2. **A term.** `POST /evaluate {term, functions?}` evaluates any integral
   the learner types or selects, pretty or text. The API installs the
   scratch goal `term == ?A` in a throwaway session, which is dropped
   after the check.

## Enabling it

SymPy is not a dependency of the app. To get closed forms, give the
checker a Python that has it:

```
python3 -m venv ~/.calc-sympy && ~/.calc-sympy/bin/pip install sympy
./calc --sympy ~/.calc-sympy/bin/python          # the page
./calc --lsp --sympy ~/.calc-sympy/bin/python    # the language server
```

or set `CALC_SYMPY` to that Python (Emacs starts `./calc --lsp` with
Emacs's own environment). Without it, evaluation answers `no-proposer`
with the numeric value. `app/test_integrate.py`'s SymPy cases run when
`CALC_SYMPY` is set, and are skipped otherwise.

## The result

```
{ "status": "proved" | "unverified" | "outside-grammar" | "not-found" | "no-proposer",
  "term": str,                        the integral, as GRAMMAR text
  "value": str | null, "value_tex": str | null,
  "antiderivative": str | null,       F, as GRAMMAR text
  "sentences": [str],                 the checked tactic script (proved only)
  "numeric": {"value": float, "digits": int} | {"skipped": str},
  "residual": str | null, "refusal": {code, message} | null,
  "message": str }
```

- **proved.** The sentences are
  `ftc F by ring.` (or `by field.`, or `int_improper F by field.` for an
  improper integral) and then `close V.`. The kernel accepted all of them
  from the goal, and the last node's report is `Proved.`. `value` is V.
  The UI shows it with `✓`, and can insert the sentences into the script.
- **unverified** (§8.2's third message). SymPy gave F, and possibly V,
  but the kernel refused a sentence. The response shows the refusal, its
  residual and its stuck explanation. F and V are shown as SymPy's claim,
  marked unverified, beside the numeric value. The classic causes are an
  identity the kernel did not find, or a branch cut, which is exactly
  where §3 says a CAS is wrong. The kernel's `ftc` obligations
  (F ∈ C¹ on the interval) are what catch a branch cut.
- **outside-grammar.** SymPy's answer uses a function GRAMMAR has no word
  for (`erf`, `Si`, `li`, `polylog`, `LambertW`, `gamma`, …). The message
  names it: "SymPy writes this with erf, which this grammar does not
  have". This is §8.2's first failure, re-worded. **It never says "no
  elementary antiderivative"**: §8.2 revision 2 forbids that claim.
- **not-found.** SymPy returned the integral unevaluated, or ran past its
  time. The message is §8.2's second one: "not found; one may well exist".
- **no-proposer.** SymPy is not installed. The message says how to point
  `--sympy` at a Python that has it.

Every status carries `numeric`: probe.py's Gauss–Kronrod value, marked
`~` as UI.md §4 marks every probe value, never `✓`. When SymPy's V and
the probe disagree beyond probe's digits on an unverified result, the
message says so.

## The proposer

`sympy_propose.py` reads `{"var", "lo", "hi", "integrand"}` as GRAMMAR
text and turns it into SymPy:

- `pi`, `oo`, `e_const` and the sixteen builtins map one to one;
- `^` becomes `**`;
- the variable is declared real (so √(x²) is |x|, not x).

It computes `integrate(f, (x, lo, hi))` for V and `integrate(f, x)` for F.
It prints both back as GRAMMAR text with its own printer:

- `Abs` becomes `abs`, `exp(1)` becomes `e_const`, `log` becomes `ln`;
- rationals are written `p/q`, and powers `^`.

Any node the printer does not know makes the answer `outside-grammar`,
naming that node's function. 
It runs under a wall-clock limit (`--eval-timeout`, default 5 s) in its
own process, killed at the limit, outside the worker (review 5).

Everything it prints is parsed by the kernel's own parser like typed text.
So a malformed answer is refused at parse, not trusted.

## From F to a proof (revised by review 1–3)

A two-sentence script proves almost nothing: after `ftc` the goal is the
literal F(b) − F(a), and `close` checks with ring/field; it never
evaluates `exp 0` or `cos pi`. So the evaluator builds the script with
the kernel steering, every sentence checked as it goes, from the goal's
node, recording nothing:

1. **ftc.** `ftc F by ring.`, else `by field.` (for an improper
   integral, `int_improper F by field.`). On `ftc-check-failed` or
   `int-improper-check-failed`, adopt the refusal's STUCK.md suggestion,
   which the kernel has already checked (typically
   `fact hK := sqrt_sq_val with a := 3.` then `ftc F by field using hK.`).
   Fact names are `h1, h2, …`, skipping any already on the path.
2. **Rewrite planner.** `close S.`, where S is the goal's own side, always
   passes the ring check. E27 then refuses it with `close-not-evaluated`,
   naming the §6.8 entry in the message and the subterm in the residual.
   The planner emits `rewrite ENTRY at SUBTERM.` and repeats, up to 12
   rewrites. Any other refusal ends the planner.
3. **close.** `close V by field using <facts>.`, V being SymPy's value.
   If it is refused, try `close S'.` with S' the evaluated side the
   planner reached, when the kernel accepts it.

The result is `proved` only when the last report is exactly `Proved.`
(review 6); `Proved modulo N admissions` is `unverified`, with the
admissions listed. When `ftc` passed but the closing failed, `sentences`
holds the checked prefix and `antiderivative_checked` is true: F is proved
to be an antiderivative even though V was not reached.

**Shapes of F (review 3).** SymPy's F is often in a shape the §6.8 table
cannot match: `atan(2*sqrt(3)*x/3 - sqrt(3)/3)` reaches `atan(sqrt(3)/3)`,
which `atan_one_sqrt3` does not match, while
`(1/sqrt 3)*atan((2*x - 1)/sqrt 3)` proves. The proposer returns up to
four shapes, and the evaluator tries them in order:
- SymPy's own F;
- the same with rationalised surds written as k/√n;
- linear arguments written (a*x + b)/c;
- logs combined into one quotient, which helps improper limits (oo − oo).

## UI

- **Page.** An **Evaluate** button in the goal pane evaluates the current
  goal. Beside it, a scratch box takes an integral in text or pretty form
  (a MathLive field, as PRETTY.md) and evaluates that. The result shows
  under it:
  - the value, rendered, with `✓` when proved;
  - F;
  - the numeric value, marked `~`;
  - for `proved`, an **Insert** button that inserts the sentences at the
    cursor, as the palette does.
- **LSP.** `dx/evaluate {textDocument, position}` evaluates the goal at
  that position (the same rule as `dx/goals`).
  `dx/evaluate {textDocument, term}` evaluates a term. It is answered on
  its own thread, like `dx/hint`, and honours `$/cancelRequest`.
- **Emacs.** `C-c C-e` evaluates the goal at point. With an active region,
  it evaluates the region's text as a term. The result goes in
  `*dx-response*`. With a prefix (`C-u C-c C-e`), a proved result's
  sentences are inserted at point.

## Bookkeeping

The owner chose "free": evaluation costs nothing and gates nothing. The
session counts it, as it keeps `max_rung` for hints: `evaluations`
appears in `/tree` and in the exported work file, so a reader of a work
file can see that the answer was asked for. There is no penalty and no
banner.

## Done when

`app/test_integrate.py`, with SymPy present (the tests are skipped
otherwise, and one test checks the `no-proposer` answer by pointing
`--sympy` at a Python without it):

1. S1, `Int[x = 0 .. 1] 3*x^2 + 2*x`: `proved`, value `2`, and the
   sentences replayed through `/tactic` reach `Proved.`.
2. Readiness P1(2), `Int[x = 0 .. 1] 1/(1 + x^3)`: `proved`, with §11.2's
   atan form (review 3). Also ∫₀¹ eˣ and ∫₀^π sin x: `proved` through the
   rewrite planner.
3. `Int[x = 0 .. oo] exp(-x)`: `proved` through `int_improper`, value `1`.
4. `Int[x = 0 .. 1] exp(-x^2)`: `outside-grammar` naming `erf`, with a
   numeric value ≈ 0.746824.
5. §4.2's Maple example `Int[x = -1 .. 1] sqrt(x^2)`: `outside-grammar`
   or `unverified`, with SymPy's claim `1`; never `0`, never `proved`
   (review 7).
6. A goal that is not an integral is refused `not-an-integral-goal`; a
   declared function in the integrand is `not-found` with a message.
7. `/evaluate {session, node}` on S1's n0 increments `evaluations`, and
   the exported work file shows it.
8. The proposer's time limit kills it: a pathological integrand under
   `--eval-timeout 1` answers `not-found` within about 2 s.
9. Page: Evaluate on S1 shows `2 ✓`, and Insert puts two sentences in the
   script that check to Proved. LSP: `dx/evaluate` on S1 returns
   `proved`. ERT: `C-c C-e` on S1 writes the value into `*dx-response*`.
10. Nothing under `kernel/` changes.

## Review (2026-09-26), folded in before the code

A skeptic read this file, ran cases 1–5 through SymPy 1.14 and the
in-process API, and found five blockers. What changed:

1. **The script needs rewrites.** Only S1 proved with `ftc` + `close`.
   `exp(-x)` on [0, oo) stops at residual `exp(-0) - 1`. The rewrite
   planner above, driven by E27's own `close-not-evaluated`, replaces
   "Choosing V".
2. **Facts.** Any F with √3 needs `fact h := sqrt_sq_val with a := 3.`
   and `using h`: adopted from STUCK.md's checked suggestion.
3. **Shapes of F.** SymPy's F for P1(2) does not reach the table's forms;
   the reference F proves in 9 sentences. The proposer returns several
   shapes. P1(2) `proved` is the target; `unverified` is recorded as a
   known gap, not a pass.
4. **The scratch goal is never a registered session.** `/session` takes
   save ownership of the goal's key and moves its work file, so a term
   equal to the learner's open goal would stop the learner's saving. The
   check builds an unregistered session and never calls `_own` or `_save`.
5. **The proposer runs outside the worker.** A route in api.py runs inside
   the worker under its lock and its 10 s step timeout. So `server.py` and
   `lsp.py` run the proposer themselves, one at a time, and only then call
   the fast `/evaluate/check {session?, node?, term?, candidates}`. A node
   retracted in between answers `stale`. Cancelling kills the SymPy
   process too. `--eval-timeout` defaults to 5 s: every case measured took
   under 0.6 s, SymPy's import included.
6. `proved` means exactly `Proved.`; admissions make it `unverified`.
7. **F and V are printed separately.** A Piecewise F reads "no single F on
   this range"; V may still be shown as SymPy's claim. Done-when 5 accepts
   `outside-grammar` or `unverified` for √(x²), never the value 0; the
   kernel has no derivative rule for `abs`.
8. **Printer.** Reject `I`, `nan`, `zoo` and an infinite V ("SymPy says it
   diverges", unverified, never a value); `RootSum` reads "roots of a
   polynomial of degree n"; reject `floor`, `exp_polar`, `lowergamma` and
   `Integral` (not-found). `E` prints as `e_const`, `Pow(u, 1/2)` as
   `sqrt`, other rational powers as `^`. For `log(u)` with u < 0 on the
   range, also try `ln(-(u))`.
9. **No `sympify`.** The proposer parses with the kernel's own
   `terms.parse_term` (kernel/ is stdlib-only and imports under the venv)
   and builds the SymPy tree from that, so no text is ever eval'd.
10. **Parameters.** A goal with parameters and a domain (`@ a > 0`) passes
   the domain facts to SymPy as assumptions; a parameter with no domain
   fact is refused `has-parameters`.
11. **More statuses.** A term the kernel refuses to install is
   `refused-goal`, with the refusal. `sentences` holds the checked prefix
   (see above).
12. **numeric.digits** is the agreement, in significant digits, between
   probe runs at the default and at half the tolerance.
13. **Insert** only at the node the sentences were checked from; anywhere
   else the page re-checks them first. The work file records the
   evaluator's sentences (not only a count) in `evaluations`.
14. **Tests added:** ∫₀¹ eˣ and ∫₀^π sin x (the planner), a fact-name
   clash with `h1`, admissions, `nan` and `I` values, a Piecewise F, the
   scratch goal not taking ownership, a `/step` during a slow proposal,
   cancelling one, and the timeout with an injected slow proposer.
15. Nit: the garbled sentence about F − F(lo) is gone; `C-c C-e` is free.
