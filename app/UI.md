# The full UI: palette, card, progress, probe, KaTeX — DESIGN.md §16.4

WHAT.md's next step after the recognizer: the rest of stage 1's assistance
and UI lists (§17, "Size") that the page does not yet show. Written before
the code.

Everything here is untrusted (tier 2 and the client). Nothing it computes
enters a proof: the palette and the card suggest, the progress signal and
the probe describe, KaTeX draws. A bug here can show a wrong suggestion or
a wrong picture; every verdict on screen is still `kernel.report`'s.

## Where it sits

```
app/assist/palette.py    the palette and the antiderivative card (§8.5)
app/assist/progress.py   the progress signal (§8.5)
app/assist/probe.py      the speculative probe, floating point (§8.6)
app/tex.py               Term -> TeX, and a reader for exactly that TeX
app/page/katex/          KaTeX 0.18.9, vendored (MIT, its LICENSE kept)
app/server.py            also serves /katex/* from that directory
app/api.py               /palette, and progress, probe and TeX on nodes
app/page/index.html      the panes below
```

Standard library only on the server. The page still loads nothing from
outside: KaTeX is served by `./calc` itself (§16.1, §17 "vendored KaTeX
and no dependencies").

## 1. KaTeX

`tex.tex(x)` prints a Term, a Rel or a goal as TeX: `\int_{a}^{b} f \,
\mathrm{d}x`, `\frac{a}{b}`, `\sqrt{a}`, `a^{n}`, `\sin x`, `\ln`, `\operatorname{atanh}`,
`\pi`, `e` for `e_const`, `?A` as `\,?A`, `D[x] f` as
`\frac{\mathrm{d}}{\mathrm{d}x} f`, `#` as `\neq 0`, relations as
`= \le < \ge >`, a goal's domain after `\quad\text{for}\;`. Parentheses
follow `terms.show`'s precedence, never fewer.

**A wrong renderer is worse than none** (API.md), so the printer is tested
by a round trip rather than by eye: `tex.read` parses exactly the TeX
`tex.tex` emits back to a Term, and `read(tex(t)) == t` holds for every
term of every problem file, every goal of every reference proof's nodes,
and a generated family of terms (every node type, nested to depth 4, with
negative literals, fractions and powers in every position). A second test
renders every problem's goal with the vendored KaTeX in the headless
browser and requires no `.katex-error`.

**The API.** `/parse` fills `katex` (no longer null). A rendered node gains
`goal_tex` and `theorem_tex`. The page draws the goal, theorem and the
statement's formal goal with KaTeX and keeps the plain string beside it,
selectable, since a learner copies terms into tactics.

## 2. The palette and the card

```
GET /palette ?session&node
  -> { moves: [{move, sentence, why}],
       rewrites: [{entry, at, sentence}],
       card: [{id, form, antiderivative, matches}] }
```

- **moves**: which of the kernel's moves apply to the goal's shape. `ftc`,
  `int_subst`, `int_parts` when the goal holds an `Int`; `int_improper`
  when an `Int` has an infinite end; `int_flip` when an `Int`'s limits are
  both literals in the wrong order; `close` when the goal has `?A`
  and no `Int` or `D` left; `fact` always. `sentence` is a SCRIPT.md
  skeleton with `_` for what the learner supplies (`ftc _.`), `why` one
  line.
- **rewrites**: each `ENTRIES` equation whose left side matches a subterm
  of the goal's non-`?A` side **syntactically**, with the schema variables
  bound by first-order matching (an `App` left side matches by function
  name and then its argument pattern). `sentence` is the complete tactic
  (`rewrite sin_zero at sin 0.`). It says what matches, not that the move
  will be accepted: side conditions are the kernel's (§8.5, "what is even
  legal here").
- **card**: the antiderivative card, the forms of recognizer row 2 plus the
  inverse-trig and hyperbolic forms, ~20 rows, each with its
  antiderivative as TeX. `matches` is true for each form that
  `recognizer.card_form` finds among the summands of the first `Int`'s
  integrand.

The page shows the palette under the goal (moves and rewrites as buttons
that insert the sentence at the cursor; nothing is stepped until the
learner steps) and the card as a collapsible table with matches
highlighted.

## 3. The progress signal

A rendered node with a parent gains:

```
"progress": { "signal": "finishable" | "rule now matches" |
                        "technique named" | "no progress" | "worse" |
                        "closed",
              "detail": str }
```

Computed from the parent's goal and this one, first applicable wins:
1. **closed**: the goal is closed.
2. **finishable**: the first `Int`'s integrand is on the card or is a
   rational function, and the parent's was not.
3. **rule now matches**: a palette rewrite (entry, at) is present that the
   parent's palette did not have.
4. **technique named**: the recognizer's first row for the first `Int`
   changed from none to a row, or to a different row.
5. **worse**: strictly more distinct atoms (the `field` normaliser's) or
   a deeper term, and nothing above fired, unless the parent's first row
   was **parts cycle** (§8.5: the cycle gets worse before it closes).
6. **no progress** otherwise.

`detail` says which measure fired (`atoms 4 -> 6`, `sqrt_sq now matches
at sqrt(t^2)`), never a verdict. The page shows it under the goal, marked
as a heuristic.

## 4. The speculative probe

A rendered node with a parent gains:

```
"probe": { "before": float, "after": float, "digits": int,
           "agree": bool } | { "skipped": str } | null
```

The value of the goal's non-`?A` side is computed in floating point at the
parent and at this node, and compared. `digits` is the number of agreeing
significant digits (capped at 12); `agree` is `digits >= 8`. Integrals
are evaluated by adaptive Gauss–Kronrod (7–15) with an error target of
1e-12 and a depth bound; an infinite end is mapped to a finite one by
x = t/(1 − t). It is **skipped**, with the reason, when a side holds a
symbol other than bound variables (`symbols a, k`), a `D` node, a
function not in `math`, or when evaluation fails or exceeds its budget
(50 000 integrand evaluations). `null` for `n0` and for a closed node.

The page shows it as `~ probe: 2.0000000000 vs 2.0000000000, 12 digits
agree` or `~ probe: … VALUE CHANGED`, always with `~` and never `✓`
(§8.6: navigation, not evidence). It never enters the obligation pane.

## 5. The status line

`Proved.` (or the report) `· assisted · max rung N · M rules ·
0 machine-checked`: `max rung` is the highest hint rung asked in the
session (0 when none), `rules` the number of accepted steps on the current
path. The session records the max rung; `/tree` returns it as `max_rung`.

## Deliberately not in this cut

Rung 4 (`!`, applying a row); the per-step timeout and cancellation;
persistence and export; §8.7's classification of refusals into three kinds
of stuck (the residual is already shown); the probe over symbolic
parameters; the factoriser and partial-fraction solver.

## Done when

1. `tex.read(tex.tex(t)) == t` over the corpus and the generated family
   (`app/test_tex.py`), and every problem's goal renders in KaTeX without
   an error (`app/test_page.py`).
2. `/palette` lists `sqrt_sq` at `sqrt(t^2)` after P1.1's substitution,
   `ftc` for S1, and a highlighted card row for S1's polynomial; the
   progress signal reads `rule now matches` there, and `finishable` after
   COS_SQ's rewrites (`app/test_api.py`, `app/assist/test_palette.py`).
3. The probe agrees on every accepted step of every reference proof whose
   goal is numeric, and reports a changed value for a planted wrong step
   made through `/step` on a goal whose kernel check does not catch it,
   or, when no such step exists, on `probe.compare` called directly with
   two different integrals (`app/assist/test_probe.py`).
4. The page shows the goal in KaTeX, the palette, the card, progress and
   probe, and a palette button inserts its sentence (`app/test_page.py`).
5. Nothing under `kernel/` changes; the kernel suite still passes.
