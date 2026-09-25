# The factoriser and the partial-fraction solver — DESIGN.md §8.4

WHAT.md's next step. §8.4's rows: **factoring** — "you supply the field
(ℚ or ℝ); the tool proposes the factorisation; `ring` verifies";
**partial fractions** — "you supply the ansatz, or nothing; the tool solves
for the coefficients exactly; verifies by recombining". "Search whose
output is cheap to verify is free": both are search, and neither output is
shown until the kernel's own `ring` or `field` has decided it equal to what
it came from. Written before the code.

The course needs two cases this cut can serve, and they set the scope: readiness P1.2, ∫ 1/(1 + x³), where 1 + x³ = (1 + x)(x² − x +
1) over ℚ and 1/(1 + x³) = (1/3)/(1 + x) + (−x/3 + 2/3)/(x² − x + 1); and
readiness P5, ∫ 1/(1 + x⁴), which does not factor over ℚ and over ℝ is
(x² + √2·x + 1)(x² − √2·x + 1).

Untrusted (tier 2). Nothing here enters a proof: it tells the learner a
factorisation or a decomposition the kernel has already checked, and the
learner uses it to find F.

**Out of scope, said plainly.** §8.2 also names "unit 00's quadratic
drag" among the course's partial-fraction problems: its integrand
M/(M·g − c·w²) (U00-P4) has parameters, and splitting it over ℝ needs
√(Mg), a radical with parameters; U00-P1a and P3 are linear with
parameters. All three are refused `not-rational` here. §8.2's "every
time" holds for this tool only over numeric coefficients.

## Where it sits

```
app/assist/factor.py   polynomials over ℚ(√d), factor(), apart()
app/api.py             POST /factor, POST /apart
app/page/index.html    in the palette: Factor over ℚ, over ℝ; Partial fractions
```

## Input

A term t and a variable x (the first `Int`'s integrand and variable, on the
page). t must be a rational function of x with **rational numeric
coefficients**: `field`'s normal form of t (the recognizer's `shapes`
reading) has every atom equal to x. A parameter (`symbols k`), a
transcendental function of x, or `sqrt` anywhere in t is refused
`not-rational`, since the kernel's normal form gives no coefficient field
to factor over. Degree of the denominator at most 12.

## Arithmetic

Coefficients live in ℚ(√d) for one squarefree integer d ≥ 2, or in ℚ: a
number is a + b√d with a, b `Fraction`s, always printed rationalised as
a + b·sqrt d, so √d never appears in a divisor of a coefficient. One
radical at a time: a factor that would need a second d is left whole,
and the note says so (x⁴ − 5x² + 6 over ℝ splits x² − 3 and leaves
x² − 2). Polynomials are coefficient lists.
This is the only arithmetic here, and it is checked only by what the
kernel says of its results.

## factor(t or its denominator, x, field)

Of a polynomial p in x over ℚ:

1. The content (a rational), then x^k.
2. **Rational roots**, repeatedly, with multiplicity (the rational root
   test, as `kernel/tagger.py` does it, bounded the same way).
3. What is left, of degree ≥ 2, is factored further:
   - degree 2 over ℚ: irreducible over ℚ (no rational root). Over ℝ with a
     positive discriminant D: the two real linear factors, with √D' where
     D = r²·D' and D' squarefree.
   - degree 4 over ℚ: into two rational quadratics. The monic quartic is
     scaled to a monic integer one, L⁴·p(y/L) with L the lcm of the
     denominators, whose monic factors have integer coefficients (Gauss),
     and mapped back. For each integer divisor b of the constant term
     (bounded as in 2) and e its cofactor: if b ≠ e, a and c follow
     linearly; if b = e, a and c are the roots of z² − a₃z + (a₂ − 2b),
     rational only for a square discriminant. So the search is complete
     for quadratic splits (x⁴ + 4 = (x² + 2x + 2)(x² − 2x + 2) has
     b = e = 2; 4x⁴ + 1 = 4(x² + x + 1/2)(x² − x + 1/2)).
   - degree 4, over ℝ, when not split over ℚ: the biquadratic form
     x⁴ + px² + q with q > 0 a rational square s², s = +√q, and
     2s − p = m·r² with m squarefree, m ≥ 2: (x² + r√m·x + s)(x² − r√m·x +
     s) (P5: s = 1, p = 0, √2; x⁴ − x² + 1: √3). s is taken positive: the
     ℚ step runs first, and only s > 0 can give factors with a negative
     discriminant. Other quartics over ℝ are left whole.
   - anything else is left whole, and the answer says so ("no further
     factor found"), never that it is irreducible unless it is degree 2
     with a negative discriminant, or a quadratic over ℚ with no rational
     root.
4. The factors are ordered by degree, then by coefficients, and each is
   made monic (the content collects the leading coefficients).

**The check.** The product, as a term, against p: `ring` when every
coefficient is rational; `field` with the fact `sqrt_sq_val with a := d`
(as the pair of terms ((√d)², d)) when √d appears. `field`'s equality
holds only where its divisors are nonzero, and a divisor can be zero
modulo the fact (field accepts 1/(1+x⁴) = 2((√2)²−2)/(((√2)²−2)(1+x⁴))),
so every divisor `field` returns must itself be decided nonzero
(`field(divisor, 0, facts)` answering `NotEqual`), or the check fails.
The answer names the check. A
factorisation the kernel does not accept is not shown; the answer is then
`{"error": "unchecked"}` (a bug here, reported, never displayed as a
result).

Over ℝ, a factor is **irreducible** when it is linear, or quadratic with a
negative discriminant; the answer marks each factor irreducible, or not
known to be.

## apart(t, x, field)

1. t = N/Q from `field`'s normal form, reduced to lowest terms here by a
   polynomial gcd (the normal form computes none: (x² − 1)/(x − 1) keeps
   x − 1), and terms whose coefficients all come out 0 are dropped; if
   deg N ≥ deg Q,
   polynomial division gives the polynomial part S and N := remainder.
2. Q is factored over the field as above. Every factor must be known
   irreducible (linear, or quadratic with negative discriminant, or a
   quadratic over ℚ with no rational root when the field is ℚ); otherwise
   `not-split` naming the factor ("x^4 + 1 does not factor over ℚ; try
   over ℝ").
3. **The ansatz**: for a linear factor l of multiplicity k, A₁/l + … +
   A_k/l^k; for a quadratic q of multiplicity k, (B₁x + C₁)/q + … +
   (B_k x + C_k)/q^k. Clearing Q gives a linear system in the unknowns
   over the coefficient field, one equation per power of x, solved exactly
   by Gaussian elimination.
4. **Or the learner's ansatz**: a list of denominators (terms), each a
   power of a factor, and for each whether its numerator is a constant or
   linear; the system is the same, and an ansatz whose system has no
   solution is `no-solution` ("these denominators cannot express it: a
   factor or a power is missing").
5. **The check**, by recombining: `field(t, S + Σ terms)`, with
   `sqrt_sq_val with a := d` when √d appears. Not accepted, not shown.

## The API

```
POST /factor {term, var, field: "Q" | "R", functions?}
  -> {factors: [{term, power, irreducible: bool|null}], content, product,
      check: "ring" | "field using sqrt_sq_val with a := d", note: str|null}
POST /apart  {term, var, field: "Q" | "R", ansatz?: [{den, numerator:
              "constant" | "linear"}], functions?}
  -> {polynomial: str | null, terms: [str], sum: str, check}
```

`term` of `/factor` is a polynomial or a rational function (then its
denominator is factored, and the answer says so). Refusals (a 200 with a
`refusal`, like every other refusal): `not-rational`, `too-large`,
`not-split`, `no-solution`, `unchecked`, and the parser's codes for a term
that does not parse.

## The page

The palette gains, when the first `Int`'s integrand is a rational
function of its variable whose denominator involves the variable (a
polynomial integrand has nothing to split), three buttons: **Factor over ℚ**, **Factor over
ℝ**, **Partial fractions** (over ℝ when ℚ does not split, and it says
which). The result is drawn with KaTeX, with its check named ("checked by
field using sqrt_sq_val with a := 2"), and the plain text beside it for
copying. Nothing is inserted into the script: a decomposition is not a
move; it is what the learner integrates term by term to write F.

## Deliberately not in this cut

Parameters in coefficients (`symbols k`), more than one radical, general
quartics over ℝ and anything of degree ≥ 5 beyond rational roots
(Rothstein–Trager is stage 3, §8.2), the integration of the terms (the
integrator's), a rung-4 hint built on this.

## Done when

1. `app/assist/test_factor.py`: 1 + x³ over ℚ is (x + 1)(x² − x + 1),
   checked by `ring`; 1 + x⁴ over ℚ is left whole ("no further factor"),
   over ℝ is (x² + √2x + 1)(x² − √2x + 1), checked by `field` using
   `sqrt_sq_val with a := 2`; x² − 2 over ℝ is (x − √2)(x + √2); repeated
   and rational roots (x³ − x², 2x² − 2) and a rational quartic split
   (x⁴ + x² + 1 = (x² + x + 1)(x² − x + 1)) come out; apart(1/(1 + x³))
   is (1/3)/(x + 1) + (−x/3 + 2/3)/(x² − x + 1) (§8.2's A, B, C);
   apart(1/(1 + x⁴)) over ℝ is P5's decomposition; a repeated factor
   (1/(x²(x − 1))), a polynomial part ((x³ + 1)/(x − 1) … as far as it
   goes), a learner's ansatz that works and one missing a power
   (`no-solution`); `not-rational` for a parameter, `sin x`, `sqrt x`;
   every result shown is accepted by the kernel's check, and a planted
   wrong factor is refused `unchecked`.
2. `app/test_api.py`: `/factor` and `/apart` on P5's integrand.
3. `app/test_page.py`: on readiness P5 (improper.P5) the palette's
   Partial fractions shows the ℝ decomposition with its check.
4. Nothing under `kernel/` changes; the kernel suite still passes.

## Review (2026-09-25), folded in

An independent skeptic read this spec against DESIGN.md §8.2 and §8.4 and
the kernel (2 blocking findings, 6 minor). Folded above: a `field` check
is vacuous when a divisor is zero modulo the fact, so every divisor is
decided nonzero; the quadratic drag and the other parameter problems are
out of scope, said plainly; the quartic search's b = e case and rational
coefficients (scaling, Gauss); s = +√q; lowest terms by gcd, and zero
terms dropped; one radical at a time; the palette hides the tools for a
polynomial integrand. Recorded, not changed: readiness P1.2 is not a
problem file, so its decomposition is tested in the unit tests only.
