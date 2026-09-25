# The recognizer — DESIGN.md §8.5, first build

§8.5's table of integrand shapes and the technique each calls for, built on
the stage 1 kernel's normal forms, scored the way §17 (revision 8) requires,
and wired to the page as hint rungs 1–3. Written before the code.

Untrusted (tier 2, §16.1). It reads terms and asks the kernel's `field` and
`deriv` questions, but nothing it returns enters a proof: a row names a
technique, and the learner still types the move, which the kernel checks.

## Where it sits

```
app/assist/recognizer.py   rows, matchers, recognize(), ladder()
app/assist/shapes.py       shape tests on the kernel's normal forms
app/assist/corpus.py       the development set, with its labels
app/assist/heldout_2026_09_25.json
                           the held-out set (below); never read to write a row
app/assist/score.py        the scores, printed; pinned by test_recognizer.py
app/api.py                 GET /hint answers rungs 1–3
```

## Rows

In this order; the first row that matches is the one rung 2 names. Each has
a `family` (what a label is compared against), rung 1's `category`, rung
2's `technique`, rung 3's `detail` with parameters filled from the integrand,
and a `cost`: what the move will ask for in return.

| # | family | matches (on the normalised integrand, variable x) |
|---|---|---|
| 1 | identity first | a trig polynomial of degree ≥ 2 in sin/cos of one linear angle (power reduction, product to sum), or an integrand that `trig_norm`'s reduction makes a constant or strictly simpler |
| 2 | standard | every summand is on the card: a constant, a polynomial, x^p, sin/cos/exp/sinh/cosh of a linear argument, 1/(x² + a²), 1/(a² − x²), 1/√(a² − x²), c/(linear)^k with k ≥ 2 |
| 3 | log | c/(linear); f′/f for f a factor of the denominator (the constant-ratio test, `field`); tan u, tanh u of a linear u |
| 4 | chain-rule substitution | some nonlinear u, an argument of an application or the base of a power in the integrand, with integrand[u := U]/u′ free of x (`field` decides D[x] of it ≐ 0) |
| 5 | parts cycle | exp(linear) times sin or cos(linear) |
| 6 | parts | a polynomial of degree ≥ 1 times sin/cos/exp/sinh/cosh of a linear argument; ln, atan, asin of a linear argument times a polynomial (degree ≥ 0) |
| 7 | split numerator | (degree 1)/(irreducible degree 2) |
| 8 | partial fractions | any other rational function whose denominator has degree ≥ 2 |
| 9 | trig substitution | √(q) with q quadratic, negative leading coefficient |
| 10 | hyperbolic substitution | √(q), q quadratic with positive leading coefficient: sinh when the completed constant is positive, cosh when negative |
| 11 | Weierstrass | rational in sin θ and cos θ of one angle θ = x, and no row above matched |
| 12 | root substitution | √(u) with u not quadratic, inside another function or times a non-constant |
| 13 | parameter differentiation | c/Dᵏ, k ≥ 2, D with a parameter, and 1/D matched by rows 2–10 |
| 14 | Beta substitution | √(A − B·x^n) or its reciprocal with n symbolic |
| 15 | orthogonality | sin or cos(m·x) times sin or cos(n·x) with m, n symbolic |

**Normalisation first** (revision 8). The integrand is read after the
kernel's `ring` normal form, with each field divisor kept as a factor; a
square root's argument is read with any monomial denominator cleared
(√(a + b/r − c/r²) = √(a r² + b r − c)/|r|); f′/f tries each factor of the
denominator. Normalising here emits nothing.

**Revision 1** (while building, on the development set only, before the
held-out set was scored):

- Row 13, parameter differentiation, moves to fourth place, between log
  and chain-rule substitution, and "1/D matched by rows 2–10" becomes
  "1/D matched by any other row". In the table's order no rational D could
  reach row 13 (partial fractions, row 8, took it first), and R-P2.2's
  1/D is a Weierstrass integral, which rows 2–10 excluded.
- Row 1's second clause (`trig_norm` makes it constant or strictly
  simpler) is not built in this version; the trig-polynomial clause is.
- A constant integrand is on the card (row 2).
- The normal form reads a/b as a·b⁻¹, so (x + 1)² in a denominator stays
  the factor x + 1 twice rather than the expanded x² + 2x + 1: "each field
  divisor kept as a factor" needs it for c/(linear)ᵏ and row 13.

**Revision 2 (table version 2, 2026-09-25).** Version 1's held-out set
was scored once (strict 18/28, lenient 20/28; WHAT.md) and is now
development data, like the spike's sets before it; version 2 is scored
once on a fresh set, `heldout_2026_09_25_v2.json`, built from units 27–40
(and unused integrals of 11–26) by a separate agent from the course's text
alone and committed unread. The changes, each a general rule rather than a
fit to one integral:

- **Row 1, the product clause** (in place of the unbuilt `trig_norm`
  clause, which it covers for sin and cos): a numerator monomial holding
  sin or cos factors of linear arguments, any angles, of total degree ≥ 2,
  with no sin or cos in the denominator, whatever else multiplies it (a
  polynomial, an exponential, a power of x). Product to sum or power
  reduction turns each such monomial into single trig terms. The
  orthogonality pattern (row 15's shape: exactly two factors with
  symbolic frequencies and nothing else) is left to row 15.
- **Row 2, square roots of a linear argument** are on the card: √(ax + b)
  and 1/√(ax + b) are powers of a linear argument (the power rule), as
  c/(linear)ᵏ already is.
- **Row 9, the secant substitution**: √(x² − a²) (a quadratic with
  positive leading coefficient and negative completed constant) with x
  itself a further factor of the denominator is x = a sec θ, the arcsec
  form; without that factor it stays row 10's cosh.

Unchanged misses, recorded: a quadratic under a root whose leading
coefficient is a symbol of unknown sign (U09-P1, and 2·e2 in general) is
still read by the symbol's sign as written; a linear substitution into a
non-card function (ln sin 2x) is silent; cos u/√u by parts is read as a
root substitution, which also works.

Families with no row: guess and verify, reduction formula, other. An entry
labelled with one is scored "no row", apart from a wrong row.

## The ladder (§8.5, "The ladder, implemented")

```
GET /hint ?session&node&rung   rung 1, 2 or 3
  -> {rung, integral, row, text, cost}  |  refusal
```

The first `Int` in the node's goal (pre-order) is the one read. Rung 1 is
the row's category, rung 2 its technique, rung 3 its detail. Refusals:
`no-integral` (the goal holds none), `no-row` (nothing matched: said
plainly, never a guess), and `not-built` for rung 4, which would apply the
move. The page shows `?`, `??`, `???` beside the stepping buttons and puts
the answer in the response pane.

## Scoring (§17)

For each labelled integral: **strict** when the first row's family is the
label; **lenient** when it is the label or one of `also`; **silent** when no
row matched; **no row** when the label is a family without a row.

- **Development set**: the spike's 22-integral corpus and its 9 held-out
  integrals (units 00–10). Both were read to write revision 8, so they are
  development data now, and rows may be tuned on them.
- **Held-out set**: `heldout_2026_09_25.json`, integrals from units 11–29,
  labelled from the course's own text by a separate agent **before any row
  was written**, and committed unread by the row author. It is scored once
  per table version, the score is published as it comes out, and no row is
  changed because of it. The next table version is scored on a fresh set.

## Done when

1. `app/assist/score.py` prints both scores; `test_recognizer.py` pins them
   and checks each row on its own examples.
2. `GET /hint` answers rungs 1–3 and the refusals above (`test_api.py`), and
   the page's `?` buttons show them (`test_page.py`).
3. WHAT.md records the held-out score, whatever it is.
