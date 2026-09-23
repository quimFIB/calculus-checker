# Recognizer spike

DESIGN.md §8.5's recognizer table, run against the technique the course's own
worked solutions use (§17's *recognizer corpus*). The question it answers is
whether the table's rows are the right granularity before all of them get
written. Standard library only. It reuses `../ring/` for terms, `deriv` and
`field`.

```
python3 report.py            # V1 and V2 against the corpus and the held-out set
python3 report.py --ladder   # also rungs 1–3 for every entry
python3 -m unittest -v       # 13 tests, <1 s
```

**Status: done 2026-09-23. Folded into DESIGN.md as revision 8** (§8.5, §17,
§18 Q15).

## What is here

| File | What |
|---|---|
| `shapes.py` | Is it a polynomial / rational function / quadratic in x, sign of a coefficient, is f′/f's ratio constant. Built on the ring spike's normaliser |
| `rows.py` | The table. **V1** = §8.5's seven rows plus the antiderivative card it describes, as written. **V2** = V1 plus five rows the V1 misses asked for |
| `corpus.py` | 22 integrals from readiness P1/P2/P5 and unit 00, each labelled with the technique the course's solution uses and quoting the line the label comes from. Plus **9 held out** from units 01–10 |
| `report.py` | Scores each table: agree / alternative / wrong row / silent / no row for this technique |
| `test_recognizer.py` | Shape tests, the pinned scores, and one test per finding |

## Result

| | Corpus (22) | Held out (9) |
|---|---|---|
| **V1**: §8.5 as written | 15 strict, 16 lenient | 3 strict, 4 lenient |
| **V2**: + 5 rows fitted to the corpus's misses | 22 / 22 | **3 strict, 4 lenient** |

**The table as designed names the course's technique for 15 of 22 target
integrals, and for 3 of 9 elsewhere in the course.** V2's perfect corpus score
is worthless as evidence. It was written by looking at those misses, and on
integrals it had not seen it gained nothing. Every row added to fix a specific
miss fixed that miss and no other. The held-out set was not used to change any
row, so its score is the only honest one here.

## Findings

1. **Adding rows is not the fix.** The held-out misses are different in kind
   from the corpus's, and a row written for one example does not reach the
   next. At this corpus size, that is what a long tail looks like. The cost of
   the table is not in writing rows. It is in making the matchers see through
   algebra, and in testing them on integrals they were not written against.

2. **Rows match the written form, not the mathematics.** Three of the six
   held-out misses are this, and each would need a normalisation step, not a
   new row:
   - `sin t·(−sin t) + (−cos t)·cos t` is −1 after `pyth`, but the rows see the
     raw term and the Weierstrass row fires on a constant. The recognizer
     should run on the goal *after* `ring` and §8.9's `trig_norm`, not before.
   - `1/(u·ln(1/u))` is f′/f with f = ln(1/u), but the row takes the whole
     syntactic denominator as f. It should try each factor of the denominator.
   - `1/√(2ε + 2GM/r − h²/r²)` is a quadratic under the root once r² is
     cleared, and the course does exactly that. The row only tests polynomials.

3. **§8.5 has no row for the chain rule**: f′(x)·g(f(x)) → u = f(x), the
   commonest substitution there is. `x·e^{x²}` matches nothing. `sin x·cos² x`
   gets the Weierstrass substitution, which is correct but absurd when u = cos x
   does it in one line. `w/√(1 − w²)` gets a trig substitution. The row is hard
   to write, because "is a factor the derivative of something inside another
   factor" is a search. `field`'s constant-ratio test (used here for f′/f) is
   the tool for it.

4. **The parts row misses its own canonical example.** §8.5 says the
   `P(x)·e^{ax}` row "knows about" ∫ eˣ sin x, the cycle case. But its pattern
   needs a polynomial factor, and eˣ sin x has none. Unit 06 P7's
   `e^{−γu/2} sin ω_d u` is silent for that reason. (The course guesses and
   verifies there instead, which is the other thing no row can say.) The other
   parts miss is unit 10 P3's `(1 − x²)ⁿ` with symbolic n. That needs a
   reduction formula, parts with dv = dx, which no row states.

5. **Row 5 is stale.** §8.5 states f′/f → ln f with f > 0, because "nothing in
   §6 differentiates `abs`". Revision 6 added `d_abs`, so the textbook ln|f|
   with f ≠ 0 is now checkable.

6. **What worked.** The card, partial fractions, parts, Weierstrass and root
   substitution rows never missed an integral of the shape they state. Where
   they went wrong, the cause was matching the raw form (finding 2) or an
   integral outside what they state (findings 3–4). Symbolic
   coefficients were no obstacle once "symbol = positive" was assumed, and
   unknown signs (`a − e`) are treated as "not ruled out" rather than as a
   refusal. The ladder text at rung 3 is specific enough to act on
   (`report.py --ladder`).

## What it means for the plan

- **§17's gate is exposed to this.** On held-out problems the ladder would
  show nothing at rungs 1–3 about half the time. So the gate's "which rung
  gets used most" reading would mostly measure recognizer coverage, not
  learning.
- **Estimate.** Writing rows is quick: each V2 row is a few lines. The
  matcher robustness in finding 2 and the chain-rule row in finding 3 are the
  real work, and both want the normal forms stage 1's kernel produces. That
  favours building the kernel before the table.
- **The held-out practice should be kept.** Score the table on units it was not
  written against, and never tune on that set. Otherwise, as V2 shows, the
  score measures what the author looked at.

## Limits

The labels are the course's own for every entry except U01-P9, where the
course only says the integral is elementary and the label is mine (flagged in
`corpus.py`). Thirty-one integrals is a small sample: the finding is the
*shape* of the result (V2 gains nothing held out), not the percentages.
Parameters are assumed positive, which the course's problems declare but a
problem file would have to state.
