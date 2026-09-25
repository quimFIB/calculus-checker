# Three kinds of stuck — DESIGN.md §8.7

WHAT.md's next step: a refused move says *what to do next*, not only what
failed. Written before the code.

Untrusted (tier 2). The kernel's refusal (code, message, residual) is
shown exactly as before; this adds an explanation beside it. Every
suggestion that names a concrete fix is **checked before it is shown**:
by the kernel's own `field` (an exact equality), never by floating point.
A suggestion that fails its check is not shown. So the explanation can be
unhelpful, never wrong about the algebra.

## Where it sits

```
app/assist/stuck.py   explain(refusal, goal, move, args) and admitted(node)
app/api.py            the refusal gains "stuck"; a node gains "stuck"
app/page/index.html   the response box shows it under the refusal
```

## The shape

```
"stuck": { "kind": "no-match" | "obligation" | "algebra" | "other",
           "headline": str,
           "lines": [str],
           "suggest": str | null }     -- a tactic sentence, checked
```

A refusal response becomes `{"refusal": {code, message, residual,
stuck}}`. A rendered node gains `"stuck"`, null unless the step admitted
a new obligation.

## 1. Nothing matches (`no-match`)

Codes: `rewrite-target-not-found`, `rewrite-lhs-mismatch`,
`ftc-no-integral`, `int-subst-no-integral`, `int-flip-no-integral`,
`int-improper-no-integral`, `int-improper-finite`, `close-no-mvar`,
`bad-tactic`.

Headline: "No rule matches here". Lines: what does match, from the
palette (UI.md §2): the rewrites at the named target, if any, else every
palette rewrite (at most five); and the recognizer's rung 1 for the first
`Int`, or "The recognizer has no row for it" when it has none. Closing
line: "? for a nudge." `suggest`: when a rewrite was refused and the
palette has exactly one rewrite at that target, its sentence.

## 2. An obligation will not discharge (`obligation`)

Codes: `obligation-decided-false`, `obligation-refuted`,
`orientation-undecided`, `divisor-normalises-to-zero`.

Headline: "The move applies, but a condition it needs fails". Lines: the
kernel's message (which names the condition and, when it found one, the
point where it fails); then one line per move:
- `rewrite`: "The entry holds only where its hypothesis does; over this
  range it does not. This rewrite is wrong here, or the range needs
  splitting."
- `ftc`, `int_improper`: "F or the integrand is undefined somewhere on
  the range: the integral may be improper there, or F is the wrong
  antiderivative."
- `int_subst`, `int_parts`, `int_flip`, `close`: "The step's side
  condition fails on this range."

For a **node** whose step admitted new obligations: kind `obligation`,
headline "Accepted, with N admission(s)", one line per admitted key with
its reason, and "A fact the kernel can use, or a narrower range, would
discharge it; the proof will read Proved modulo N admissions until then."

## 3. The step is legal and the algebra does not close (`algebra`)

Codes: `ftc-check-failed`, `int-improper-check-failed`,
`int-subst-check-failed`, `int-parts-check-failed`, `close-check-failed`.
The residual r is the kernel's lhs − rhs (for `ftc`, F′ − integrand; for
`close`, the goal's side − the value).

The headline names what r is (`D[t] F − integrand = r`, `your value is
off by r`). Then, first that applies:

1. **A known identity closes it.** For each `sqrt a` in r, the fact
   `sqrt_sq_val with a := a`; for each `sin u` or `cos u`, `pyth_cos with
   u := u`. If `field(r, 0, facts)` holds with those facts (tried one at a
   time, then together), the line names the identity (§8.7: a correct
   trig or surd answer must not be diagnosed as a slip) and `suggest` is
   the `fact` sentence; a further line says to add `by field using h`.
2. **F is off by a constant factor** (`ftc`, `int_improper`). If
   r = λ·f for the integrand f, with λ a rational found by sampling r/f
   and confirmed exactly by `field(r, λ·f)`, and λ ≠ −1: "Your F′ is
   (1 + λ) times the integrand" and `suggest` is `ftc F/(1+λ)` in its
   simplest spelling (`2*(F)` for 1/2), itself confirmed by
   `field(D[x](F/(1+λ)), f)` with shapes.deriv.
3. **F is off by a constant term's derivative**: r is free of x and
   nonzero: "F′ − integrand is the constant c: F has an extra c·x".
4. **Otherwise** a numeric sample over the range: r at three points of
   the `Int`'s range (a quarter, a half, three quarters; finite ranges
   only, no free symbols), "where the two diverge" (§8.7). For `close`,
   the value of the goal's side in floating point beside the value's.

Numbers in lines are floats printed to 6 significant figures, marked `≈`;
they are navigation, like the probe (§8.6).

## `other`

Every other code: headline "Refused: <code>", no lines, the kernel's
message standing alone.

## Deliberately not in this cut

Splitting a range (`cases`, `int_split` are not in the kernel yet, so the
advice can only name the split); matching the residual against every
§6.8 identity (only the two above, the ones §8.7 names); explaining
`bad-args` shapes beyond the kernel's message.

## Done when

1. `app/assist/test_stuck.py`: each kind on its own examples, among them
   §8.7's own three: `sqrt_sq` over [−1, 0] (obligation), `ftc sin t −
   t*cos t` for 2t·sin t suggesting `ftc 2*(sin t - t*cos t)` which the
   kernel then accepts (algebra, factor), and the surd π√3/9 against
   π/(3√3) suggesting `sqrt_sq_val` with which `close ... by field using
   h` is accepted; `close 1` for sin² + cos² naming `pyth_cos`; a wrong
   rewrite target (no-match).
2. Every `suggest` the tests produce is replayed through `/tactic` and
   accepted.
3. `/tactic` and `/step` refusals carry `stuck` (`app/test_api.py`), and
   the page shows it (`app/test_page.py`).
4. Nothing under `kernel/` changes; the kernel suite still passes.
