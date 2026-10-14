# Complex analysis: a design (proposal, revision 2, 2026-10-14)

**Status:** a proposal, not built and not yet a spec. It answers DESIGN.md
§18 Q8 ("complex numbers as a sort"), which revision 10 deferred until the
course reached unit 06. Nothing in this file changes the kernel.

**Revision 2** follows the owner's brief on revision 1: *implement it
once*. Revision 1 was sized to the course: a residue rule for rational
functions on a few standard contours, and principal branches only. The
owner asked instead for a design as general as is reasonable, so that
more power later never means redesigning the complex kernel, and was
willing to give things up for simplicity and computability. So:

- **The definitions and judgement forms are general from the start.**
  Later power arrives as new rules, entries or tactics, and never as a
  change to what a term or a judgement means (§2).
- **Course shapes are tactics, not kernel rules.** "Close the contour in
  the upper half plane" is an untrusted composition of general rules.
  This is DESIGN.md §7's architecture, applied.
- **What is given up is listed** (§2.3), each item with its reason.
  Generality stops where a judgement would stop being decidable by the
  machinery the kernel has.

The course is the **test set, not the specification**, as DESIGN.md §1
already says of `mechanics-to-relativity` and the tool. §1 is what it
asks. §10's acceptance criterion is that every problem it asks of a
built stage proves, without one rule written for it.

Decisions **Z1–Z9** are proposed with a recommendation. §11 lists the
ones that are the owner's. Once those are settled, each stage gets its
own spec in p1_expected before any code, as every stage so far has.

## 1. What the course asks (the test set)

A survey of all 41 units of `mechanics-to-relativity` (2026-10-14; every
hit read in context, since most grep hits for "pole", "Cauchy",
"conjugate", "residue" and "contour" mean something else) sorts each use
into five classes:

- **A, arithmetic:** `i`, conjugates, modulus and argument, roots of a
  polynomial.
- **B, the complex exponential as a device:** `e^{iωt}`, phasors, `Re` at
  the end, characteristic roots ±iω.
- **C, functions of a complex variable:** holomorphy, Cauchy–Riemann,
  branches.
- **D, contour integration:** Cauchy's theorem, residues, real integrals
  by contours, inversion of transforms.
- **E, complex linear algebra:** conjugate-symmetric forms, complex fields.

A and B carry problems in about seventeen units (02, 06–10, 15, 16,
18–21, 24, 25, 29, 32, 40). C and D carry problems in three: **unit
20**, which holds nearly all of them (P4–P10, P12), unit 34's P6, and
unit 24's P9. E carries problems in two (19, 29).

| Unit | Classes | The most demanding item |
|---|---|---|
| 06 driven oscillator | A, B | P2: (1+i)⁸ = 16, e^{iπ/3} = ½ + (√3/2)i, \|e^{2−3i}\| = e², Re and Im of a complex solution are in ker L. P12: ∫₀^∞ G e^{−iωτ} dτ = 1/p(iω) for Im ω < γ/2 |
| 07, 08, 16 | A, B | eigenvalues ±iω; ζ = ζ₀ e^{iΩt} |
| 09 Kepler | A, B | cos(π/2 + ix) = −i sinh x |
| 18 wave equation | A, B | P9: e^{iω·2L/c} = −1 gives the odd harmonics |
| 19 Fourier | A, B, E | P5: Gibbs via a geometric sum in e^{ix}; P6: a complex root of tan k = −ik |
| **20 Fourier transform** | A–D | P4: where z̄, \|z\|², Re z are complex-differentiable; a harmonic conjugate; ∮ around \|ω − 8\| = 1. P5: ∫ dω/D = π/(γω₀²) by closing up. P6: Fresnel by an octant, with an arc bound. P7: Kramers–Kronig by an indented contour. P8: a keyhole with arg ∈ (0, 2π). P9: Bromwich inversion, closing left for t > 0. P10: Rouché, Lagrange inversion, a radius of convergence. P12: steepest descent |
| 24 Maxwell | B, D | P9 and slides: the retarded Green's function by residues, closing up for t < 0 and down for t > 0 |
| 34 forms | C, D | P6: f dz closed ⇔ Cauchy–Riemann; ∮ dz/z = 2πi; ∮ z̄ dz = 2i·Area |

Two findings matter for the design. First, the bulk of the work (B, in
sixteen units) is complex-valued functions of a **real** variable,
handled componentwise, and elementary functions at complex arguments.
Second, the hardest problems need more than revision 1 offered. P8's
keyhole uses a **non-principal branch**, P6 and P7 need **arc estimates**
and an **indentation**, and P10 needs the **argument principle**. A
course-sized kernel would already have had to be redesigned for unit 20
alone. That is the owner's point, confirmed by the test set.

## 2. Principles

### 2.1 General definitions, partial computation

Every new kernel notion gets its **general definition**:
- the residue at any isolated singularity;
- the winding number of any closed piecewise-C¹ path;
- holomorphy on any open region the grammar can state;
- a path integral along any piecewise-C¹ path;
- a logarithm with its cut along any ray.

**Computing** with a notion is a separate set of rules, each with
decidable side conditions, and each one partial:
- a residue is computed at a pole whose order is certified, and not
  yet at an essential singularity;
- a winding number is computed by signed ray crossings, where
  discharge can decide each crossing.

**A later rule extends what is computable, and never changes what
anything means.** That is the test this design is held to, and §9
applies it to every extension in sight.

### 2.2 The kernel states theorems; tactics find their instances

**Theorems stay as general as the textbook states them.** The kernel's
new trusted rules are a small set of them: Cauchy's theorem and the
residue theorem in one statement, the estimation lemma, the limit laws,
and the argument principle. Each takes its hypotheses as obligations the
existing discharge can attempt.

**Course methods are tactics.** "∫_{−∞}^{∞} by a semicircle", "Bromwich",
"keyhole", "indent around a pole on the axis" and "Fresnel by an octant"
are untrusted tactics (DESIGN.md §7). Each builds the contour, applies
the theorems, and proposes the limits and bounds; the kernel checks
every step. A missing tactic costs a longer proof by hand, never a
false one, and adding one is never a kernel change.

### 2.3 What is given up, for simplicity and computability

**Z1: these are out, by design, and each has a reason.**

1. **Functions are single-valued.** A multivalued function is a family
   of branches, each with an explicit cut (Z6). There are no Riemann
   surfaces, and analytic continuation is not an operation: it is a
   different term with a different cut. *Why:* every term then denotes
   one function, and `split`, discharge and the rule table stay
   one-valued. Everything continuation is used for in computation, a
   branch with its cut placed where the contour needs it can do.
2. **Analysis in one complex variable at a time.** Real parameters and
   further complex parameters are fine (`exp(i*w*t)`, a complex ω in
   `1/p(i*w)`), but `D[z]` and `H(U)` are about one variable. *Why:*
   several complex variables is a different theory (Hartogs), and
   nothing in sight needs it.
3. **Regions are what discharge can decide.** A region is a conjunction
   of real polynomial conditions on `re z` and `im z` (Z5), and a
   **star-shaped** region for Cauchy's theorem comes with its centre as
   a certificate (Z8). There is no general open set and no homology
   condition. *Why:* the homology form asks for the winding number to
   vanish at every point outside U, an infinite condition. Star-shaped
   U with finitely many singular points removed has the same reach for
   every integral in sight, cut planes and keyholes included, and needs
   one decidable certificate.
4. **Paths are built from pieces**: segments, circular arcs, explicit
   C¹ parametrisations, joined and reversed. There are no arbitrary
   rectifiable curves. *Why:* winding numbers and "the path stays in U"
   are then decidable per piece.
5. **Singularities inside a bounded contour are isolated and finitely
   many,** listed and certified complete. *Why:* the residue theorem's
   sum must be finite and checked.
6. **Infinity is a limit, not a point.** There is no Riemann sphere and
   no residue at ∞. A contour "closed at infinity" is a family in R and
   a `lim[R -> oo]`, as `oo` is only an endpoint today (DESIGN.md §5.1).
   *Why:* `oo` inside arithmetic is what §5.1 keeps out to keep `field`
   total.
7. **The theorems are rules, not derivations.** The kernel cites Cauchy,
   the residue theorem and the argument principle; it does not prove
   them. That is §6.8's status for every entry, and §14's plan to
   machine-check the rule table covers them in time.

## 3. The objects

### 3.1 Sorts

**Z2: two sorts, Real ⊂ Complex, inferred.** A term is Complex when it
mentions `i`, a complex variable, or a complex-valued head, and Real
otherwise. The sort is syntactic and static, never semantic: `z + conj z`
is Complex, although its value is real, and `re(z + conj z)` is Real. A
learner who wants an order on it writes the `re`. The rules:
- order judgements (`<`, `<=`, `>`, `>=`) take only Real sides;
- `Int[x = a .. b]`'s variable and limits are Real;
- `oo` is a Real endpoint only.

So `z < 1` is refused `sort-order-on-complex` at the parser, where a
misreading is cheapest to stop.

**The sort table is data.** Each builtin and constructor declares its
argument and result sorts in one table. Matrices over ℝ or ℂ, or §18 Q4's
functions as objects, would add rows to it, not a second mechanism.

**Z3: complex variables are declared; undeclared letters are real.** A
goal names them in its header (`goal ... complex z, w.`, or a problem
file's `"complex": ["z", "w"]`). Every existing goal keeps its meaning.

### 3.2 Terms, from a small set of primitives

**Z4: `i` is reserved as the imaginary unit**, a constant like `pi`. D3
is the precedent: a name with two readings is refused, not guessed.
Nothing the checker reads uses `i` as a variable (unit 34's `e^{i₁}` is
an index in prose, and `Sum` is not built). `i_const` is the
alternative.

**The primitives** are the only complex heads `split` (§4) knows
directly:
- `i` and the field operations;
- `conj`, `re`, `im`;
- `exp`;
- **`log[θ]`** and **`arg[θ]`**, a logarithm and an argument with their
  cut along the ray at angle θ (Z6).

**Every other complex function is defined from these** by an entry the
kernel holds as a definition:
- `sin z == (exp(i*z) - exp(-(i*z)))/(2*i)`, and so for `cos`, `tan`,
  `sinh`, `cosh` and `tanh`;
- `pow[θ](z, w) == exp(w*log[θ] z)`;
- `sqrt[θ] z == pow[θ](z, 1/2)`;
- `asin`, `atan` and the rest, by their logarithmic forms.

`abs z` is `sqrt((re z)^2 + (im z)^2)`, which is the real `abs` when z is
real. So the trusted complex core is the field, `conj`, `exp` and one
family of logarithms. Adding a function means adding a definition, never
a case in `split` or in the derivative table.

**Z5: regions are conjunctions of real polynomial conditions** on `re z`
and `im z`, such as `@ im z > 0`, `@ abs(z - 1) < 2` or
`@ re z >= 0, z # 0`. Those are exactly the domains the kernel handles
now, two real variables wide. Named regions (`disk(c, r)`,
`halfplane(…)`, `annulus(c, r1, r2)`, `slit[θ]`) are sugar for them.

**Z6: branches carry their cut.** `log[θ] z` is
`ln(abs z) + i*arg[θ] z`, with `arg[θ] z` in (θ − 2π, θ].
- It owes `z` off the ray `{r*exp(i*θ) : r >= 0}`: as real conditions,
  either side of the ray, the step naming which (`by side`), so that
  every judgement stays conjunctive.
- The principal branch is θ = π, written `Log`, `Sqrt` and `z ^^ w`.
- Unit 20 P8's keyhole branch is θ = 2π, arg in (0, 2π].
- The real `ln`, `sqrt` and `^` keep their real meaning and domains,
  unchanged.

Making θ a parameter costs one argument, and it is the difference
between "principal branch only" and every cut a contour can need.

**θ is a closed real constant:** a literal, or a rational multiple of
`pi`, never a variable or an expression with one. Then the ray is fixed,
"is z on the cut" is a real condition on `re z` and `im z` with constant
coefficients (cos θ and sin θ evaluate by entries), and every cut
obligation stays one discharge can decide. A symbolic θ would buy no
contour the tactics build, and would make every cut obligation possibly
undecidable. It is refused `branch-not-constant` at the parser.

### 3.3 Paths, winding numbers, residues, limits

- **Paths** are a sort of their own, built by:
  - `seg(a, b)`;
  - `arc(c, r, t1, t2)`, the circle about c from angle t1 to t2;
  - `path(t -> phi(t), t = a .. b)`;
  - joining, `g1 ++ g2`, which owes that the end of g1 is the start
    of g2;
  - reversal, `rev g`.

  `circle(c, r)` is `arc(c, r, 0, 2*pi)`. A path is closed when its
  ends meet, which is a decided equation.
- **`CInt[g] f dz`** is a path integral. **Its definition is its
  parametrisation** (Z7): along `path(t -> phi(t), t = a .. b)` it is
  `Int[t = a .. b] f(phi(t)) * D[t] phi(t)`, owing `phi in C^1`, and it
  is additive over `++` and changes sign under `rev`. So every integral
  along an explicit path reduces to §5.1's integral of a complex-valued
  function of a real variable, with no new trusted rule.
- **`wind(g, a)`**, the winding number, is defined as
  `CInt[g] 1/(z - a) dz / (2*pi*i)` for a closed path that avoids a.
  It is **computed** by signed crossings of a ray from a: each crossing
  of a segment or an arc is a real sign decision on the path's data, so
  discharge decides it whenever it decides the obligations of those
  points, and the untrusted search proposes the integer.
- **`res(f, a)`** is the residue, defined for any isolated singularity
  as the coefficient of `1/(z - a)` in the Laurent expansion, or
  equivalently `CInt[circle(a, r)] f dz/(2*pi*i)` for small r.
  Computing it is §5.4's business, and it is partial.
- **`lim[z -> a] f`** for a complex `z` means `abs(f - L) -> 0` as
  `abs(z - a) -> 0`. That is a real limit of real quantities, which is
  how §5.3 computes it.

## 4. Arithmetic: `split`, and why obligations stay real

The learner writes complex terms. The kernel never reasons about a
complex number as such: every complex term has a real part and an
imaginary part, each an ordinary real term, and judgements are decided
through them.

- **An equation** `L == R` holds when `re L == re R` and `im L == im R`,
  each an ordinary real check by `ring` or `field`.
- **An obligation is always real.** `z # 0` is owed as
  `(re z)^2 + (im z)^2 > 0`, a disk `abs(z - c) < r` as a real
  polynomial inequality, and a cut as a condition on `re z`, `im z`.

So discharge, Fourier–Motzkin, `norm_num`, the regularity certificates
and the limit evaluator, most of the trusted base, **do not change**:
they never see a complex number. What the trusted base gains is
**`split`**, a structural map from a complex term to its pair:
- `i` is (0, 1), and a complex variable `z` is (`re z`, `im z`), two
  real atoms;
- sums and products are the textbook formulas;
- a quotient is `a*conj(b)/abs(b)^2`, owing `abs(b)^2 # 0`;
- `exp(a + i b)` is `exp a * (cos b + i sin b)`;
- `log[θ] w` is (`ln(abs w)`, `arg[θ] w`);
- every defined function goes through its definition;
- a declared complex function is an opaque atom, with opaque real parts.

The map is total and never guesses.

**It was checked on a prototype** (2026-10-14; 80 lines over the
existing `field`, not kept). Each row was decided by the current real
`field`, with nothing complex added to it:

| Equation | Decided | Needs |
|---|---|---|
| `(1 + i)^8 == 16` | yes | nothing |
| `(1 + i)/(1 - i) == i` | yes | nothing |
| `z*(1/z) == 1` | yes | owes `(re z)^2 + (im z)^2 # 0` |
| `(sin z)^2 + (cos z)^2 == 1` | yes | `pyth_cos` at `re z`, `cosh_sq` at `im z` |
| `exp(i*t)*exp(-(i*t)) == 1` | yes | parity and `pyth_cos` at t |
| `exp(i*pi) == -1` | yes | the entries `cos_pi`, `sin_pi` |
| `exp(z)*exp(w) == exp(z + w)` | not yet | `exp` of a sum, and the addition formulas |
| `(1 + i)^8 == 17` | refused | (false) |

**Splitting turns identities about the complex exponential into real
trig identities**, and the kernel already has the machinery: DESIGN.md
§8.9's trig normaliser proposes parity, addition and Pythagorean
instances, and `field` checks them. Under this design it runs inside
every complex check, not only as `ftc`'s fallback. `exp` of a sum needs
one more proposal of the same kind.

**E27 (fully evaluated) over ℂ.** A closed complex value has:
- no `i^k` with k ≥ 2;
- no `conj`, `re` or `im` of a closed value left;
- no `exp` of a closed complex argument whose parts would evaluate.

Canonical `a + b*i` is not required: DESIGN.md §9's principle stands, a
property and not a canonical form. `closed` admits `i`, `abs`, `arg[θ]`
and `log[θ]`. Auto-simpl (E162) applies the complex evaluation entries
as it applies the real ones.

## 5. Calculus

### 5.1 Complex-valued functions of a real variable

`t` is real, the value complex (`exp(i*w*t)`, a phasor, a complex
solution of a linear ODE). **Everything is componentwise**, so the real
rules apply to each part with their proofs:
- `deriv` gives `D[t]` of a complex term as the pair of real derivatives,
  and `conj`, `re` and `im` commute with `D[t]`;
- `ftc` over a real interval checks `F' == f` as a complex equation.
  F ∈ C¹ and f ∈ C⁰ are owed per component, by the regularity rules that
  exist. `1/(t - i)` owes `t^2 + 1 > 0`, which discharge proves;
- `verify` checks a complex candidate against a linear ODE, and `re`
  recovers the real solution;
- `int_improper` takes a complex limit as two real ones, or by
  `abs f -> 0` (§5.3).

This is the tier with the most reach for the least code, and it closes a
gap the real kernel has. WHAT.md lists "`int_improper` for trig
integrands (e^-x sin x needs a squeeze law)" as not built. Here
∫₀^∞ e^{−x} sin x is `im` of ∫₀^∞ e^{(−1+i)x}, whose antiderivative has
modulus e^{−x}/√2 → 0, so no squeeze law is needed.

### 5.2 Functions of a complex variable

- **`D[z]`** is the complex derivative. Its rule table is the field rules
  plus three primitives:
  - `exp`;
  - `log[θ]`, off its cut, with derivative `1/z`;
  - the composition rule.

  Every defined function differentiates through its definition, so there
  is no table to keep in step. `D[z]` of `conj`, `re`, `im`, `abs` or
  `arg[θ]` is refused `deriv-not-holomorphic`.
- **`f in H(U)`**, holomorphy on a region (Z5), is a judgement beside
  `C^k`, with closure rules:
  - sum, product, quotient owing `# 0`, and composition;
  - `exp` on ℂ;
  - `log[θ]` off its ray.

  **A declared complex function** is holomorphic only under an
  assumption (Γ, as E147 states assumptions).
- **Singular points.** `f in H(U \ S)`, with S a finite list, states that
  f is holomorphic on U except at the listed points. **Completeness of
  S** (that f has no other singularity in U) is an obligation, decided:
  - for a quotient `g/h` with g and h holomorphic, by the zeros of h;
  - for a polynomial h, the zeros are certified by a factorisation that
    `ring` checks;
  - for a builtin, by a **zero-set entry**: `exp` has no zeros, `sin`
    vanishes exactly at kπ. Inside a bounded region the kπ that qualify
    are a finite integer range, which is decided.
- **Order of a zero or a pole.** `ord(h, a) == m` is a judgement,
  certified by `h(a) == ... == D[z]^(m-1) h (a) == 0` and
  `D[z]^m h (a) # 0`. It makes pole orders checkable for any
  holomorphic denominator, not only polynomials (`1/sin z` at 0 is a
  simple pole).
- **Cauchy–Riemann needs nothing new:** with z = x + i y, `verify`
  checks `D[x] re f == D[y] im f` on real terms.

### 5.3 Limits and estimates

- **Limits in ℂ** are real limits of moduli (§3.3). The rules are:
  - the limit laws;
  - continuity of everything in H(U);
  - removable singularities: g/h with ord(h, a) ≤ ord(g, a);
  - l'Hôpital for holomorphic g and h, which in ℂ needs no one-sided
    conditions;
  - `abs f -> 0` gives `f -> 0`.
- **The estimation lemma**, the one general bound:
  `abs(CInt[g] f dz) <= L(g) * M` when `abs f <= M` on g. L(g) is
  computed for segments and arcs. `abs f <= M` on an arc is a real
  inequality in the arc's angle, discharged or admitted like any other.
  Jordan's lemma is an entry built on it, with its stated condition.

### 5.4 Contour integrals and residues

**Z8: one theorem, Cauchy and residue together.** Let U be star-shaped
about a centre c (the certificate), S a finite list, `f in H(U \ S)` with
S complete, and g a closed path in U that avoids S. Then

```
CInt[g] f dz == 2*pi*i * sum over a in S of wind(g, a) * res(f, a)
```

**The star-shaped certificate** is checked against Z5's grammar:
- a convex region (an intersection of half-planes and disks) is
  star-shaped about any of its points;
- a slit plane `slit[θ]` is star-shaped about any point on the opposite
  ray;
- ℂ is star-shaped about 0.

With S empty it is Cauchy's theorem. With U = `slit[θ]` it covers cuts
and keyholes. With the wind numbers computed, it covers contours that
wind twice or run clockwise. **No contour shape appears in the rule.**

**Residues are computed by rules, each one partial:**
- **simple pole**, g/h with ord(h, a) == 1: `res == g(a)/D[z] h (a)`;
- **pole of order m**, ord(h, a) == m:
  `res == lim[z -> a] D[z]^(m-1) ((z - a)^m * f) / (m-1)!`, with the
  limit by §5.3;
- **removable point:** `res == 0`;
- **essential singularity** (`exp(1/z)` at 0): through the Laurent
  coefficient, once `Sum` exists (§9). The definition (§3.3) already
  covers it, so this is a new computation rule, not a change.

**Z9: the argument principle as a rule:**
`CInt[g] D[z] h / h dz == 2*pi*i * (zeros − poles inside, with
multiplicity, weighted by winding)`, with the zeros and poles listed
and certified complete as for S. It is how a count of zeros is proved,
which is unit 20 P10's Rouché territory, and it costs one rule because
§5.2's completeness machinery is already there.

### 5.5 What the tactics do (untrusted)

Every course method is a composition, built by a tactic and checked
step by step:

| Tactic | It builds | It applies |
|---|---|---|
| `close_upper` / `close_lower` | `seg(-R, R) ++ arc(0, R, 0, pi)` (or the lower arc) | Z8; the estimation lemma or Jordan on the arc; `lim[R -> oo]`; the symmetric limit, related to the improper integral by absolute convergence or by Dirichlet's test, as a stated rule |
| `bromwich` | the line re s = σ, closed left or right by the sign of t | the same, turned a quarter |
| `keyhole` | two rays along `slit[2*pi]` and two arcs | Z8 on the slit plane, the arc limits, the jump of `arg[2*pi]` across the cut |
| `indent` | a small semicircle around a pole on the axis | the half-residue limit, and a principal value as an explicit symmetric limit |
| `sector` | an octant or another sector | Z8 with S empty; the arc bound; a ray integral by substitution |

Readiness P5, ∫₀^∞ dx/(1 + x⁴), is proved today by a hand-found
partial-fraction antiderivative (`kernel/problems/improper/P5.json`). By
`close_upper` it is half of ∫_{−∞}^{∞} (evenness, one small rule, `ring`
checking f(−x) == f(x)):
- q = 1 + z⁴ factors as `(z - a1)(z - a2)(z - a3)(z - a4)` with
  a = e^{±iπ/4}, e^{±3iπ/4}, checked by `ring` with `sqrt_sq_val` at 2;
- two of the roots lie inside the upper semicircle, each with winding
  number 1;
- each residue is a simple pole's, `1/(4 a^3)`, and their sum is
  `-i*sqrt 2/4`.

2πi times that is π/√2, and half of it is π/(2√2), P5.json's value.
The same theorem, by a second route the kernel checks, and the one the
readiness sheet itself names as the alternative to its real method.

## 6. What it costs in the trusted base

| Piece | Size (est.) | Like |
|---|---|---|
| sort table and checker, `i`, primitives, `log[θ]`/`arg[θ]`, regions, path syntax | 400 lines | GRAMMAR.md's D-decisions |
| `split` | 250 lines | `deriv.py`'s rule table |
| complex `ring`/`field` (split both sides) | 80 lines | `field.ring_equal` |
| definitions of the other functions | 60 lines | `entries.py` |
| `D[z]`, `H(U \ S)`, `ord`, zero-set entries, completeness | 350 lines | §6.9's `C^k` rules |
| paths, `CInt`'s definition, `wind` by crossings | 300 lines | `int_subst` |
| limits in ℂ, the estimation lemma | 200 lines | `limits.py` |
| Z8, the residue rules, Z9 | 300 lines | `int_parts` |

About 1,950 trusted lines, against revision 1's 1,300. The difference
buys every contour, every cut direction, and pole orders for any
holomorphic denominator. **Untrusted:** the tactics of §5.5, the pole and
zero finder (roots of polynomials over ℚ(i) and radicals, with SymPy
optional), winding-number proposals, the trig normaliser in every
complex check, and the page, TeX, untex and palette work. About 1,500
lines.

## 7. Soundness

**The claim keeps its form:** every result reported as proved carries a
derivation the kernel checked (DESIGN.md §15.1). The new trusted pieces
are:
- the sort table;
- `split`, whose identities the suite also checks numerically at
  random points, as the TeX printer's round trip is checked now;
- the definitions;
- the rules of §5.

Everything that finds something stays untrusted, and a bug in it costs a
refusal: roots, residues to propose, winding integers, which side of a
cut to owe, trig instances, and contours.

**The traps, and what refuses each one.** Each row is an identity a CAS
will apply that is false somewhere:

| Trap | Why false | Refused by |
|---|---|---|
| `log(z*w) == log z + log w` | off by 2πi across the cut | no such entry; `log[θ]` splits to `ln abs` and `arg[θ]`, and `arg` of a product is not a sum |
| `sqrt(z^2) == z` | false where the branch flips | no entry; `sqrt[θ](z)^2 == z` is the only one, and it is true |
| `pow(pow(z, a), b) == pow(z, a*b)` | branch | no entry |
| `log(exp z) == z` | im z outside the branch's range | `log_exp` owes `θ - 2*pi < im z <= θ` |
| `abs(z)^2 == z^2` | true only for real z | `split` makes them different reals |
| `z < w` on complex terms | ℂ has no order | `sort-order-on-complex` at parse |
| `D[z] conj z` | not holomorphic | `deriv-not-holomorphic` |
| Cauchy on a region with a hole | the hole can carry a singularity | Z8 needs star-shaped U, certified |
| a pole on the contour | the integral is not defined | `g` must avoid S: a decided `# 0` |
| a missed singularity | wrong value | completeness of S: factorisation or zero-set entry |
| a symmetric limit read as an improper integral | they agree only when the improper integral exists | the tactic must cite absolute convergence or Dirichlet's test |
| a path that is not C¹ | the definition needs `phi'` | `phi in C^1` owed piece by piece |

## 8. The order of work

**The build order is about effort, not about meaning.** Every stage
implements its part of the general design, so a later stage adds rules
and never revisits an earlier one. Each stage is spec-first, built, and
attacked by a skeptic, and ends with course problems that prove.

| Stage | Builds | Proves from the test set |
|---|---|---|
| **K1** arithmetic | sort table, `i`, primitives, definitions, regions, `split`, complex `ring`/`field`, E27 over ℂ | 06 P2's algebra; 09's cos(π/2 + ix) |
| **K2** a real variable | componentwise `deriv`, `ftc`, `verify`, regularity, complex limits in t | 06 P2's ker L, 06 P12, 18 P9, ∫₀^∞ e^{−x} sin x |
| **K3** a complex variable | `D[z]`, `H(U \ S)`, `ord`, zero sets, limits in ℂ | 20 P4's differentiability and harmonic conjugate, 34 P6's Cauchy–Riemann |
| **K4** contours | paths, `CInt`, `wind`, the estimation lemma, Z8, residues, Z9 | 34 P6's ∮ dz/z and ∮ z̄ dz, 20 P4's circles, and with tactics 20 P5, P6, P7, P8, P9, 24 P9, readiness P5 |
| **T** tactics | §5.5's five, then whatever the course or a learner asks for | the same, shorter |

K1 and K2 cover classes A and B, most of the course. K3 and K4 are unit
20's core, and with K4 all of unit 20 but P10's Rouché part, P11, P12 and
the numerical roots is reachable. What stays unreachable is in §9, each
item with what would bring it in.

**Against the gate:** none of it touches the gate's seventeen problems,
which are real. The recognizer and hint ladder get new rows at K4, not
changed ones.

## 9. Extensions, and why each one is additive

The design's claim is that none of these needs a redesign. Each row says
what it would add.

| Extension | Adds | Changes a definition? |
|---|---|---|
| Laurent series, essential singularities, residues by series | `Sum` (stage 2, which must be sort-polymorphic, Real or Complex), and one residue rule | no: `res` is already the Laurent coefficient |
| Power series, radius of convergence, analytic functions defined by series | `Sum`, and the ratio and root rules over ℂ | no |
| Rouché's theorem | one rule on top of Z9 and the estimation lemma | no |
| Conformal maps, Möbius transformations | entries, and a tactic for change of variable in `CInt` | no |
| Other cut placements, other branches | a θ | no: Z6 has it |
| Multiply connected regions | cut into star-shaped pieces, by a tactic (the course's own method) | no |
| Certified numerics (19 P6's root of tan k = −ik) | stage 2's interval kernel, run on `split`'s two parts | no |
| Asymptotics (stationary phase, steepest descent) | stage 2's `big_O` | no |
| Complex matrices, Hermitian forms | rows in the sort table (§18 Q4's question) | no |
| Several complex variables | a new theory | **yes**: given up by Z1, item 2 |
| The Riemann sphere, residue at ∞ | a point at infinity in arithmetic | **yes**: given up by Z1, item 6, and a change of variable w = 1/z does the same work |

**One constraint this places on work outside it:** stage 2's `Sum` must
be designed sort-polymorphic from the start, so that a complex series is
the same construct. That is cheap if decided before `Sum` is built and a
redesign if decided after.

**Out of scope as computation:** theorems about complex analysis that
the course states rather than computes with (Liouville, Morera,
causality as a principle). The tool checks the computations that use
them.

## 10. Acceptance

A stage is done when its problems from the test set (§8) prove from
their own statements, **with no rule, entry or tactic written for one
problem**. If a problem needs one, that is a finding: either the general
rule it instantiates was missed (add the rule), or the design gave it up
(§2.3), and the problem stays out with that reason written next to it.

## 11. Decisions for the owner, with recommendations

None of these is decided. Each is recommended here (2026-10-14); the
owner's decisions will be recorded as p1_expected E-entries when made.

1. **Z1, the seven give-ups of §2.3: accept all seven.** Only two cannot
   be added back later. Several complex variables is needed by nothing in
   the course, nor in physics calculus generally. A residue at ∞ is
   reached by the substitution w = 1/z. The one to watch is
   "star-shaped, not homology": it is the most likely to pinch, and its
   upgrade path is stated below.
2. **Z4: reserve `i`.** The survey found no checker-facing use of `i` as
   a variable, and `i_const` would be miserable to type. Names are
   case-sensitive, so a current `I` is unaffected.
3. **Z3: complex variables declared in the header.** A convention would
   silently change any existing goal that uses `z`, and the grammar's
   rule throughout is to refuse rather than guess (D3, D5).
4. **Z6: `log[θ]` with `Log`, `Sqrt` and `^^` as principal-branch
   shorthand, and θ a closed real constant** (§3.2), so that every cut
   obligation is decidable.
5. **Z8: yes.** Without it no real integral is evaluated by a contour,
   which is most of what complex analysis is for here. The theorem is
   textbook, its hypotheses are decidable obligations, and §14 covers
   machine-checking it later. **Z9: yes, built last in K4**: only unit 20
   P10 needs it, and it reuses K4's machinery.
6. **`Sum` sort-polymorphic (§9): agree now.** It costs nothing before
   `Sum` is built and a redesign after.
7. **When: after the gate.** The gate is the project's falsifier
   (DESIGN.md §17), its seventeen problems are real, and nothing here
   helps answer it. This work is about 3,500 lines, worth doing if the
   tool survives the gate. If it is not to wait, K1 and K2 are where to
   start: small, most of the course's complex use, and they close the
   e^{−x} sin x gap.

Within the build, the order is K1 → K2 → K3 → K4, each spec-first in
p1_expected, each ending with its test-set problems proving.

**What would change this design.** A soundness finding in `split`, the
one piece every complex check relies on, would be the reason to prove
its identities in §14's rule-table prover before K2. A need for
several complex variables or a point at infinity would reopen Z1. And if
K4's star-shaped Z8 meets an integral it cannot reach by cutting the
region into pieces, the homology form is the next step: Z8 with a
decided "winding number zero outside U" in place of the certificate.
