# Stage 0c — the `ring` spike

DESIGN.md §17 stage 0c: sparse polynomials over ℚ[atoms], `field` normalisation
*emitting its nonvanishing obligations*, run against §11.2's flagship residual.
Standard library only, Python 3.10+.

```
python3 -m unittest -v     # 28 tests, ~2 s
python3 bench.py           # timings — on an idle machine; --quick to smoke-test
```

**Status: closed 2026-09-23.** The code, its correctness and its timings are
done, and the findings below are folded into `DESIGN.md` as revision 7.

**What it does not measure.** §17 says the spike "converts the largest
estimate in this document from a guess into a measurement" — the 60–110 hours
for `ring`/`field`. It was written by Claude in one session, so it says nothing
about how long it takes you to write, for the same reason `STAGE0.md` stopped
pricing authoring by drafting rate. What it does settle is whether the design
works as written, which is below.

## Files

| File | Tier | What |
|---|---|---|
| `poly.py` | kernel | Sparse polynomials over ℚ: dicts of sparse monomials, `Fraction` coefficients, lex order, exact division |
| `field.py` | kernel | `ring` and `field`: normal forms, atoms, obligations, facts, residuals |
| `terms.py` | spike-only | §5.1's term tuples, a small parser and printer, exact evaluation for the tests |
| `deriv.py` | spike-only | §6.3's output forms applied literally, so `field` is timed on what it will really get |
| `test_field.py` | — | Worked cases from DESIGN.md, refusals, and property tests against exact evaluation |
| `bench.py` | — | §11 cases plus four scaling families, against §8.6's 100 ms budget |

The trusted part is `poly.py` + `field.py`: **~370 lines of code** (excluding
docstrings and comments), against §17's 600 for `ring`/`field`/`norm_num`.
Still missing from that count: `norm_num` as its own rule, §15.3's handles, and
§5.3's discharge. The comparison is lines only, not hours.

## How it decides

`lhs ≐ rhs` is decided by normalising `lhs − rhs` to a numerator polynomial
over a multiset of denominator factors, and asking whether the numerator is
zero. Factors are interned by their polynomial, scaled to leading coefficient 1,
so a sum over a shared denominator stays over it rather than squaring it.
Nothing needs a polynomial gcd, because N/F = 0 exactly when N = 0.

`Result.holds` means *lhs = rhs wherever every obligation holds*. It is **not**
`Proved`; that is `holds` with no obligation left open after §5.3 runs.

## The test that matters

`field` is the one component whose bug is a false `Proved`, so the property
tests check its verdicts against **exact rational evaluation**, which shares no
code with the normaliser: at random rational points where every emitted
obligation holds, both sides must be defined and equal. Opaque atoms are
modelled by a fixed rational function, which is an honest model of ℚ[atoms].
Four planted bugs all fail the suite: an unrecorded divisor, a negative power
charging the wrong divisor, an inverse dropping its content, and an LCM
ignoring the second denominator (11, 4, 5 and 9 failures respectively).

## Findings for DESIGN.md

All folded into revision 7 (§5.3, §6.2, §6.3, §11.2, §16.2, §17, §18 Q18).

1. **§11.2's `deriv; rewrite sqrt_sq_val; field` cannot work as a rewrite.**
   After `d_atan`, the √3 that needs squaring is inside `((2x − 1)/sqrt 3)^2`.
   `deriv`'s output contains no `(sqrt 3)^2` at all, and *s*² appears only
   once `field` has expanded the term
   (`test_rewriting_before_field_is_not_enough`). The fact has to reach
   `field`'s normal form. The spike does this with **`field` modulo facts**:
   proven equations `a^k ≐ r`, each a §6.8 rule instance, with the numerator
   reduced modulo them before the zero test. This is not the extension of the
   coefficient field to ℚ(√d) that §6.2 declines, since each fact is a named
   theorem. But it does add a parameter to a trusted rule. The soundness
   argument is in `_Normaliser.reduce`. Facts with a rational right-hand side
   work too (unit 00 P4's `V² = mg/k`) and carry their own obligations.

2. **`field` emits one obligation §11.2 never listed**:
   `1 + ((2x − 1)/sqrt 3)^2 # 0`, which is `d_atan`'s own denominator. It is
   true, but §5.3's sign certificate only sees that if it reads the goal *as
   written*. Ring-normalised, it is a quadratic in x with coefficients in the
   atom `1/sqrt 3`. *(A first run also showed `sqrt(3)^2 # 0`. That came from
   this spike's `deriv` running `d_inv` on a closed denominator, and is fixed
   in `deriv.py` rather than being a design finding.)*

3. **"Every denominator it cancels" is not an implementable specification.**
   A normaliser has no well-defined notion of which denominators it cancelled.
   The spike emits an obligation for **every divisor in its input**, including
   those inside atom arguments. That is the conservative reading, and it
   coincides with the obligations §5.1's `/` former already carries, so `field`
   never adds one the term did not already owe. §6.2 now says exactly that.

4. **§6.3 has no `d_neg`, no `d_div`, and `d_const` covers only a rational
   literal**, so `D[x] pi`, `D[x] sqrt 3`, `D[x](-u)` and `D[x](u/v)` have no
   rule. `deriv.py` bridges these in the obvious way: closed terms go to 0,
   `-u` becomes `(-1)*u`, and `u/v` becomes `u*(1/v)`. Revision 7 widens
   `d_const` to any term free of x, and routes `-u` and `u/v` through `ring`
   and `field` without adding entries.

5. **What `ring` does with division is now stated in §6.2.** In the spike,
   division by a nonzero literal is a coefficient, and division by anything
   else is an opaque atom. So `1/x^2` and `(1/x)^2` are different atoms to
   `ring`, and only `field` relates them.

6. **Atom identity is congruence on normalised arguments.** `sin(x + 1)` and
   `sin(1 + x)` are one atom. Arguments equal only as rational functions with
   different representations, such as `sin(x/x)` and `sin(1)`, are two atoms.
   That is incomplete, not unsound.

## Timings

`python3 bench.py`, 2026-09-23, Python 3.14.6, load 2.4 on 8 cores. That is
not idle, but the bench is single-threaded and at least one core was free. No
conclusion below moves at a factor of 2. (Measured just before the `deriv`
fix above, which only removes a `0 * …` subterm from §11.2's input.)

| Case | Size | ms | Largest numerator (terms) | Denominator factors |
|---|---|---:|---:|---:|
| §11.1 `deriv; ring` | | 0.12 | 1 | 0 |
| §11.2 `deriv; field` + fact | | 1.24 | 8 | 6 |
| Unit 00 P4 quadratic drag, `field` + fact | | 0.69 | 2 | 1 |
| ∫ 1/(x²+1)², `deriv; field` | | 0.49 | 2 | 2 |
| Partial fractions, `deriv; field` | n = 2 / 4 / 8 / 12 / 16 | 0.33 / 0.77 / 2.36 / 4.82 / 8.58 | 1 | n + 1 |
| Telescoping sum, `field` | n = 4 / 16 / 64 / 128 | 0.92 / 15.0 / **716** / **5,807** | up to 255 | up to 130 |
| Continued fraction, `field` | depth 4 / 8 / 16 / 32 | 0.32 / 0.65 / 1.62 / 4.37 | 2 | 1 |
| (x+y+z+1)^n, `ring` | n = 4 / 8 / 12 / 16 | 0.78 / 7.24 / 33.5 / **144** | up to 969 | 0 |

**Reading.** Every case shaped like the corpus is at least 10× inside §8.6's
100 ms, and §11.2 takes about a millisecond. Two shapes break the budget, and
both are synthetic:

- **Many distinct denominator factors.** The telescoping sum grows roughly
  with the cube of the factor count, 64 → 128 costing ×8. Each addition
  expands the product of the factors the other side lacks, with `Fraction`
  coefficients growing as it goes. The fix, if one is ever needed, is to
  combine sums pairwise rather than left to right, or to cache the expanded
  products.
- **Large multivariate expansion.** `ring` is roughly quadratic in the term
  count: a 969-term product takes 144 ms, which is plain dict multiplication
  in Python.

Neither is anywhere near §11–§12. So §18 Q18 is settled as *yes*, `gmpy2` and
a compiled normaliser stay unneeded, and §16.4's per-step timeout stays the
backstop.
