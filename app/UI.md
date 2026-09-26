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
`\pi`, `\mathrm{e}` for `e_const` (and `\exp` for `exp`, never
`e^{…}`, which reads as a real power), a product always as `\cdot`
(never juxtaposition: `2*0` is not `20`), `|a|` for `abs`, `\infty`,
names as a letter or `\theta`-style Greek base, digits inline and
`_suffixes` as one subscript (`x1`, `x_{1}` and `x_{ab\_c}` stay
distinct; a name that fits no pattern, like `omicron`, is
`\mathit{…}`), `?A` as `\,?A`, `D[x] f` as
`\frac{\mathrm{d}}{\mathrm{d}x} f`, `#` as `\neq 0`, relations as
`= \le < \ge >`, a goal's domain after `\quad\text{for}\;`, each
interval bare or named as `show` prints it (R4), `Reg` as `e \in C^{k}(…)`, and `/\` as
`\wedge`. Parentheses follow `terms.show`'s precedence, except that
`\frac`, `\sqrt` and `|…|` group themselves and take none inside. A bare
application argument follows the grammar's own convention: `\sin x \cdot y`
is `(sin x)*y`, as `sin x*y` is.

**A wrong renderer is worse than none** (API.md), so the printer is tested
by a round trip rather than by eye: `tex.read` transliterates exactly the
TeX `tex.tex` emits back to GRAMMAR.md text and hands it to the trusted
parser (`terms.parse_goal`, §15.6's `parse(print(t)) ≡ t`), so a reader
private to this module cannot agree with the printer on a wrong picture; and `read(tex(t)) == t` holds for every
term of every problem file, every goal of every reference proof's nodes,
and a generated family of terms (every node type, nested to depth 4, with
negative literals, fractions and powers in every position). A second test
renders every problem's goal with the vendored KaTeX in the headless
browser and requires no `.katex-error`.

**The API.** `/parse` fills `katex` (no longer null). A rendered node gains
`goal_tex` and `theorem_tex`. The page draws the goal, theorem and the
statement's formal goal with KaTeX and keeps the plain string beside it,
selectable, since a learner copies terms into tactics.

**Obligations and residuals (2026-09-26, the owner's ask).** Each
obligation carries `key_tex` and a refusal `residual_tex`, from the same
printer, under the same round trip (every obligation key of every
reference proof's nodes is read back). The page draws them inline in
KaTeX's text style, so a fraction stays about a line high in the table,
with the plain text as the tooltip; when there is no TeX, or KaTeX
refuses it, the plain text is shown as before.

## 2. The palette and the card

```
GET /palette ?session&node
  -> { moves: [{move, sentence, why}],
       rewrites: [{entry, at, sentence}],
       card: [{id, form, antiderivative, matches}] }
```

- **moves**: which of the kernel's moves apply to the goal's shape. `ftc`,
  `int_subst`, `int_parts` when the goal holds an `Int` with finite ends
  (each refuses an infinite one); `int_improper` when an `Int` has an
  infinite end; `int_flip` when a finite `Int`'s limits evaluate (in
  floating point) in the wrong order; `close` when the goal has `?A`
  and no `Int` or `D` left; `fact` always. `sentence` is a SCRIPT.md
  skeleton with `_` for what the learner supplies (`ftc _.`), `why` one
  line.
- **rewrites**: each `ENTRIES` equation whose left side matches a subterm
  of the goal's sides (both when there is no `?A`, as the kernel's
  `_sides`), first syntactically with schema variables bound by
  first-order matching, then as the kernel's rewrite reads an `App` left
  side: function name, and the argument up to ring. With no schema
  variable that is `ring_equal` (`sin(2*(pi/2))` is `sin pi`); with one,
  each subterm of the argument is tried as its value (`sqrt(1 - (1 - t^2))`
  is `sqrt_sq` with `u := t`); with two, syntactic only. So the palette
  under-approximates what the kernel would accept. `sentence` is the complete tactic
  (`rewrite sin_zero at sin 0.`). It says what matches, not that the move
  will be accepted: side conditions are the kernel's (§8.5, "what is even
  legal here").
- **card**: the antiderivative card, the forms of recognizer row 2 plus the
  inverse-trig and hyperbolic forms, 19 rows, each with its
  antiderivative as TeX. `matches` is true for a row when
  `recognizer.card_form` names one of that row's forms for some summand
  of the first `Int`'s integrand (palette.CARD lists the names per row).
  Rows no card form names (1/x, tan, the inverse hyperbolics, f′/f, aˣ)
  are reference only and never marked.

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
2. **finishable**: `close` applies (no `Int` or `D` left under `?A`), or
   the first `Int`'s integrand is on the card (every summand, row 2 of the
   recognizer) or is a rational function; and the parent's was not, or
   the step removed an `Int`. So the `ftc` that finishes is never `worse`.
3. **rule now matches**: a palette rewrite (entry, at) is present that the
   parent's palette did not have. (After `int_subst` renames the variable
   an old match can read as new; recorded, not fixed.)
4. **technique named**: the recognizer's first row for the first `Int`
   changed from none to a row, or to a different row (a row becoming
   none does not count).
5. **worse**: both goals hold an `Int`, and the new one has strictly
   more distinct atoms (names, applications, real powers, calls,
   integrals and derivatives, counted structurally, so an improper `Int`
   counts like any other) or is deeper, and nothing above fired, unless
   the parent's first row was **parts cycle** (§8.5: the cycle gets worse
   before it closes).
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
parent and at this node, and compared. `digits` is the number of agreeing digits on the scale
max(|a|, |b|, 1), capped at 12, so float noise at a zero value
(`sin(2*(pi/2))` is 1.2e-16) agrees; `agree` is `digits >= 8`. An integral
that does not reach its error target is skipped, never reported as
changed. Integrals
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

`Proved.` (or the report) `· N admissions · assisted · max rung N ·
M rules · 0 machine-checked` (§16.4): `admissions` counts the current
node's obligations the kernel admitted, `max rung` is the highest hint
rung asked in the session (0 when none), `rules` the number of accepted
steps on the current path. The session records the max rung, so
`GET /hint` now changes session state (only that number); `/tree`
returns it as `max_rung`.

## Review (2026-09-25), folded in

An independent skeptic read this spec against DESIGN.md and the code
(11 findings, 3 blocking). Folded above: the finishing `ftc` read as
`worse` (rule 2 now covers `close`, `worse` needs an `Int` on both
sides); the palette missed the rewrites the reference proofs take, which
match up to ring (the ring matching above); the round trip used a
private reader (it now ends in the trusted parser, with the TeX table
above); `ftc`, `int_subst` and `int_parts` offered at infinite ends;
atoms undefined on an improper `Int`; digits undefined near 0; criterion
3's planted step does not exist; the card's contract; the status line's
`0 admissions`. KaTeX's provenance is recorded in
`app/page/katex/SOURCE`. Not folded: an old match reading as new after a
rename (recorded in rule 3).

## Deliberately not in this cut

Rung 4 (`!`, applying a row); the per-step timeout and cancellation;
persistence and export; §8.7's classification of refusals into three kinds
of stuck (since built: STUCK.md); the probe over symbolic
parameters; the factoriser and partial-fraction solver.

## Done when

1. `tex.read(tex.tex(t)) == t` over the corpus and the generated family
   (`app/test_tex.py`), and every problem's goal renders in KaTeX without
   an error (`app/test_page.py`).
2. `/palette` lists `sqrt_sq` at `sqrt(t^2)` after `parts.P1_PARTS`'s
   substitution, `ftc` for S1 and no `ftc` for P5, and a highlighted card
   row for S1's polynomial; every palette rewrite sentence on every
   reference node is accepted by `/tactic` or refused only for a side
   condition, never `bad-tactic` or `rewrite-lhs-mismatch`; the progress
   signal reads `rule now matches` after P1_PARTS's substitution and
   `finishable`, never `worse`, at every finishing `ftc`
   (`app/test_api.py`, `app/assist/test_palette.py`).
3. The probe agrees on every accepted step of every reference proof whose
   goal is numeric. Since §8.6 (revision 10) says an accepted step can
   change the value only through an admission, and the reviewer's attempt
   at one (`sqrt_sq` over [−1, 0]) was refused, the VALUE CHANGED path is
   tested on `probe.compare` with §8.6's own pair (2 against 0.6023),
   and a rendered node is tested to carry the probe
   (`app/assist/test_probe.py`, `app/test_api.py`).
4. The page shows the goal in KaTeX, the palette, the card, progress and
   probe, and a palette button inserts its sentence (`app/test_page.py`).
5. Nothing under `kernel/` changes; the kernel suite still passes.
