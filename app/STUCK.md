# Three kinds of stuck — DESIGN.md §8.7

WHAT.md's next step: a refused move says *what to do next*, not only what
failed. Written before the code.

Untrusted (tier 2). The kernel's refusal (code, message, residual) is
shown exactly as before; this adds an explanation beside it. Every
suggestion is **checked before it is shown, by the kernel itself**: the API
runs its sentences through `kernel.step` from the same node, in order,
recording nothing (kernel states are values; no node is added), and a
suggestion the kernel does not accept in full is not shown. `field` and
floating point only *find* candidates. So the explanation can be
unhelpful, never wrong about what the kernel will accept.

## Where it sits

```
app/assist/stuck.py   explain(refusal, goal, move, args) and admitted(node)
app/api.py            /step and /tactic catch the Refusal, attach "stuck"
                      (they hold the node, the move and its args), and
                      re-raise; a node gains "stuck"
app/page/index.html   the response box shows it under the refusal
```

## The shape

```
"stuck": { "kind": "no-match" | "obligation" | "algebra" | "other",
           "headline": str,
           "lines": [str],
           "suggest": [str] | null }   -- tactic sentences, in order,
                                          all accepted by the kernel
```

A refusal response becomes `{"refusal": {code, message, residual,
stuck}}`. A rendered node gains `"stuck"`, null unless the step admitted
a new obligation.

## 1. Nothing matches (`no-match`)

Codes: `rewrite-target-not-found`, `rewrite-lhs-mismatch`; the
`-no-integral`, `-wrong-variable` and `-ambiguous` codes of `ftc`,
`int_subst`, `int_parts`, `int_flip` and `int_improper` that the kernel
raises; `ftc-`, `int-subst-` and `int-parts-infinite-endpoint` and
`int-improper-finite` (each with a first line naming the move that takes
it: `int_improper`, or `ftc`); `close-no-mvar`.

Headline: "No rule matches here". Lines: what does match, from the
palette (UI.md §2): the rewrites at the named target, if any, else every
palette rewrite (at most five); and the recognizer's rung 1 for the first
`Int`, or "The recognizer has no row for it" when it has none. Closing
line: "? for a nudge." `suggest`: when a rewrite was refused and the
palette has exactly one rewrite at that target (the target read and
printed canonically), its sentence, if the kernel accepts it.

## 2. An obligation will not discharge (`obligation`)

Codes: `obligation-decided-false`, `obligation-refuted`,
`orientation-undecided`.

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
- `orientation-undecided`, whatever the move: the order of the limits
  cannot be decided; state it in the domain or give numbers.

For a **node** whose step admitted new obligations: kind `obligation`,
headline "Accepted, with N admission(s)", one line per admitted key with
its reason, and "A fact the kernel can use, or a narrower range, would
discharge it; the proof will read Proved modulo N admissions until then."

## 3. The step is legal and the algebra does not close (`algebra`)

Codes: `ftc-check-failed`, `int-improper-check-failed`,
`int-subst-check-failed`, `int-parts-check-failed`, `close-check-failed`,
`int-subst-endpoint-mismatch`, and `divisor-normalises-to-zero` (raised by
`field` inside a check: headline "A divisor in the step is zero", the
kernel's message, "rewrite that quotient"). The residual r is the kernel's
lhs − rhs: for `ftc` and `int_improper` F′ − integrand, for `close` the
goal's side − the value, for `int_subst`/`int_parts` the body − the
rewritten body, for the endpoint mismatch the new limit's image − the old.

The headline names what r is (`D[t] F − integrand = r`, `The goal's side
− your value = r`, `The two sides differ by r`). Then, first that applies:

1. **A known identity closes it.** For each `sqrt a` in r, the fact
   `sqrt_sq_val with a := a`; for each `sin u` or `cos u`, `pyth_cos with
   u := u`. If `field(r, 0, facts)` holds with those facts (tried one at a
   time, then together; any refusal reads as no), the line names the
   identity (§8.7: a correct trig or surd answer must not be diagnosed as
   a slip) and `suggest` is the `fact` sentences, each binding a name not
   bound on the path (`h`, `h1`, …), then the refused move again with
   `by field using` its facts and the new ones. The kernel must accept the
   whole list, the re-issued move included: `field` here ignores the
   fact's hypothesis and the divisors, which the kernel's check charges.
   (`ftc` already runs trig normalisation, so `pyth_cos` fires for
   `close`, `int_improper`, `int_subst` and `int_parts`.)
Steps 2 to 4 are for `ftc` and `int_improper` only, on the `Int` the move
acted on (its `occurrence`, else the first):

2. **F is off by a constant factor.** Sample r/f at the quarter, half and
   three-quarter points of the range (finite, numeric ends only); if the
   three agree to 1e-9, λ is that float as a fraction with denominator at
   most 1000, confirmed exactly by `field(r, λ·f)`. If λ ≠ −1: "Your F′ is
   (1 + λ) times the integrand", and `suggest` is the move again with
   F := c·F for c = 1/(1 + λ) (`2*(F)`, `(F)/3`, `2*(F)/3`), every other
   clause (`occurrence`, `by`, `using`) kept, if the kernel accepts it.
3. **F is off by a constant term's derivative**: r is free of x and
   nonzero: "F′ − integrand is the constant c: F has an extra c·x". No
   suggestion.
4. **Otherwise** r at the same three points, "where the two diverge"
   (§8.7).

For `close` with no identity: the goal's side and the value in floating
point (integrals by the probe's quadrature). For other moves: r's value
when it is a closed number, else the headline alone.

Numbers in lines are floats printed to 6 significant figures, marked `≈`;
they are navigation, like the probe (§8.6).

## `other`

Every other code, `bad-tactic` among them (a sentence that does not
parse has no move to explain): headline "Refused: <code>", no lines, the
kernel's message standing alone.

## Deliberately not in this cut

Splitting a range (`cases`, `int_split` are not in the kernel yet, so the
advice can only name the split); a suggestion for the constant-term case
(it would hand over the answer); matching the residual against every
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
2. Every `suggest` the tests produce is replayed through `/tactic`, every
   sentence in order, and accepted.
3. `/tactic` and `/step` refusals carry `stuck` (`app/test_api.py`), and
   the page shows it (`app/test_page.py`).
4. Nothing under `kernel/` changes; the kernel suite still passes.

## Review (2026-09-25), folded in

An independent skeptic read this spec against DESIGN.md §8.7 and the
kernel (10 findings, 2 blocking). Folded above: codes the kernel raises
that the spec missed (`int-subst-endpoint-mismatch`, the `int_parts`
move-scoped codes, the `-ambiguous`, `-wrong-variable` and
`-infinite-endpoint` codes); where `explain` gets its context (inside
`/step` and `/tactic`, not in the generic refusal path); `bad-tactic` is
`other`; the `close` headline's sign; "checked" now means the kernel
accepted every sentence, fact and re-issued move alike, with fresh fact
names; `pyth_cos` cannot help `ftc`; λ's sampling and rounding; steps
2–4 limited to `ftc` and `int_improper`; `orientation-undecided`'s own
line and `divisor-normalises-to-zero` as algebra; refusals from `field`
read as no.
