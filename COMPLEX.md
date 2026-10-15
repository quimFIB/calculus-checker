# Complex analysis: the design, as built (2026-10-14/15)

**Status:** built, 2026-10-14 and 2026-10-15 (p1_expected E165–E280,
GRAMMAR.md §11, ARCHITECTURE.md §16). This file began as a proposal,
revision 2 of 2026-10-14. The owner took its recommendations and chose to
build before the gate (E165, §11). It is now the record of what was
built. The design reasoning is kept where it still holds, and where the
build departed from the proposal the section says so and cites the
decision. The stages, in the order built:

- **K1**, arithmetic (E165–E175);
- **K2**, complex values of a real variable (E176–E182);
- **K3**, a complex variable: `D[z]` (E183–E189);
- **K4a**, paths, `CInt` and `cint_param` (E190–E199);
- **K4b**, residues on closed contours (Z8), with convex regions given by
  `in` (E200–E211);
- **K4c-i**, Z10: `residues upper|lower` on a line integral, and
  `int_even` (E212–E221);
- **marked ends**, `Int[x = a+ .. b]` and `Int[x = a .. b-]`
  (E222–E231);
- **K4c-ii**, the keyhole, Z11 (E232–E241);
- **the sector**, Z12, and unit 20 P9 (E242–E249);
- **the tracker upgrade**: a later discharge replaces an earlier
  admission (E250–E252);
- **two strict sine bounds** (E253–E256);
- **`int_re` and `int_im`**, and parity in `int_even` (E257–E264), which
  bring 20 P7's two exact checks (E263);
- **principal values and indentation**: the term `PV`, and Z13
  (E265–E272);
- **symbolic coefficients** in a divisor's quadratic factors (E273–E280),
  which bring 20 P5.

The largest departure is E212's. The goal language has no limit term, so
"close the contour" cannot be composed from the estimation lemma and
`lim[R -> oo]`, as §5.3 and §5.5 first proposed. Each course method is
instead one trusted theorem with general hypotheses and a decidable
decay certificate (Z10–Z13). The estimation lemma waits for limit terms.

This answers DESIGN.md §18 Q8 ("complex numbers as a sort"), which
revision 10 deferred until the course reached unit 06.

**Revision 2** followed the owner's brief on revision 1: *implement it
once*. Revision 1 was sized to the course: a residue rule for rational
functions on a few standard contours, and principal branches only. The
owner asked instead for a design as general as is reasonable, so that
more power later never means redesigning the complex kernel, and was
willing to give things up for simplicity and computability. So:

- **The definitions and judgement forms are general from the start.**
  Later power arrives as new rules, entries or certificates, and never
  as a change to what a term or a judgement means (§2).
- **Course shapes were to be tactics, not kernel rules.** As built they
  are trusted rules, each one composed theorem (Z10–Z13), because the
  composition needs a limit term (E212). Each rule's certificate is
  partial, so a later certificate widens a rule without changing what
  it means (§2.2).
- **What is given up is listed** (§2.3), each item with its reason.
  Generality stops where a judgement would stop being decidable by the
  machinery the kernel has.

The course is the **test set, not the specification**, as DESIGN.md §1
already says of `mechanics-to-relativity` and the tool. §1 is what it
asks. §10's acceptance criterion is that every problem it asks of a
built stage proves, without one rule written for it, and §10 says which
do.

Decisions **Z1–Z9** were proposed with a recommendation, and the owner
took them (E165, §11). Z10–Z13 were added during the build (E213, E233,
E243, E267). Each stage got its own spec in p1_expected before any code,
as every stage before it had.

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
  yet at an essential singularity (E207);
- a winding number is computed by signed ray crossings, where
  discharge can decide each crossing (E205).

As built, a winding number and a residue are computed into the result
of `residues` and are not terms (E200). Their general definitions are
the ones the rule's statement uses, so adding `wind` and `res` as terms
later changes no rule's meaning.

**A later rule extends what is computable, and never changes what
anything means.** That is the test this design is held to, and §9
applies it to every extension in sight.

### 2.2 The kernel states theorems; untrusted code finds their instances

**Theorems stay as general as the textbook states them**, and each
takes its hypotheses as obligations the existing discharge can attempt.

The proposal named a small set of trusted rules: Cauchy's theorem and
the residue theorem in one statement, the estimation lemma, the limit
laws, and the argument principle. Course methods ("∫_{−∞}^{∞} by a
semicircle", Bromwich, the keyhole, indentation, Fresnel by an octant)
were to be untrusted tactics composing them, as DESIGN.md §7 has it.

**That is not what was built** (E212). The goal language has no limit
term, so "the residue theorem on a contour of size R, a bound on the
arc, then R → ∞" cannot be stated. As built:
- **Z8** is Cauchy's theorem and the residue theorem in one statement,
  on closed contours (E200).
- **The course methods are trusted composed theorems:** Z10, closing a
  line integral in a half-plane, Bromwich included (E213); Z11, the
  keyhole (E233); Z12, the sector (E243); Z13, indentation (E267). Each
  states its theorem once, with general hypotheses. Its decay
  certificate is a decidable computation, and partial (§2.1).
- **There is no estimation lemma and no limit term.** Both wait for
  limit terms, and are additive (E212).
- **Z9, the argument principle, is not a rule.** While h is a
  polynomial, `residues` proves CInt of h'/h directly (E232).

What finds an instance stays untrusted, as the proposal intended: the
root finder, the side of the line a root lies on, a winding number's
branch, a non-integer bracket for α (E204, E205, E215, E240). A bug
there costs a refusal, never a false proof.

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
   `1/p(i*w)`), but `D[z]` and holomorphy are about one variable. *Why:*
   several complex variables is a different theory (Hartogs), and
   nothing in sight needs it.
3. **Regions are what discharge can decide.** As built, the region of
   Z8 is a conjunction of open half-planes (affine in `re z` and `im z`)
   and open disks, given by `residues in C, ...` (E201). Their
   intersection is convex, so it is star-shaped about each of its
   points, and the region's form is the certificate, with no centre to
   give. Anything else is refused `region-not-convex`. There is no
   general open set and no homology condition. *Why:* the homology form
   asks for the winding number to vanish at every point outside U, an
   infinite condition. The proposal had star-shaped regions with a
   centre as the certificate, slit planes among them; neither was built.
   The keyhole is its own rule, Z11 (E233), not Z8 on a slit plane.
4. **Paths are built from pieces**: segments, circular arcs, explicit
   C¹ parametrisations, joined and reversed. There are no arbitrary
   rectifiable curves. *Why:* winding numbers and "the path stays in U"
   are then decidable per piece. As built, winding is computed for
   segments and for arcs at rational multiples of π; a `path[t]` piece
   refuses `wind-not-computable` (E205).
5. **Singularities inside a bounded contour are isolated and finitely
   many,** listed and certified complete. *Why:* the residue theorem's
   sum must be finite and checked.
6. **Infinity is a limit, not a point.** There is no Riemann sphere and
   no residue at ∞, and `oo` is only an endpoint (DESIGN.md §5.1). The
   proposal wrote a contour "closed at infinity" as a family in R and a
   `lim[R -> oo]`. As built there is no limit term: Z10 states the limit
   theorem itself, that the line integral converges and equals the
   residue sum (E212, E213), and Z11–Z13 do likewise. *Why:* `oo` inside
   arithmetic is what §5.1 keeps out to keep `field` total.
7. **The theorems are rules, not derivations.** The kernel cites Cauchy
   and the residue theorem (Z8), Z10–Z13, and inside Z12 the Gaussian
   integral (E243); it does not prove them. That is §6.8's status for
   every entry, and §14's plan to machine-check the rule table covers
   them in time.

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

**The primitives** were to be the only complex heads `split` (§4) knows
directly:
- `i` and the field operations;
- `conj`, `re`, `im`;
- `exp`;
- **`log[θ]`** and **`arg[θ]`**, a logarithm and an argument with their
  cut along the ray at angle θ (Z6).

The proposal defined every other complex function from these by an
entry. **As built, `split` reads more heads directly** (E167): `sin`,
`cos`, `sinh` and `cosh` by their addition formulas over a + ib, and
`tan` and `tanh` as quotients of those. The branch forms are read as
definitions:
- `pow[θ](z, w)` is parsed as `exp(w*log[θ] z)`;
- `sqrt[θ] w` splits as `exp(log[θ](w)/2)`;
- a real power `RPow(b, e)` with e Complex splits as `exp(e*ln b)`.

The inverse trigonometric and inverse hyperbolic functions, `ln` and
the real `sqrt` take a Real argument only: `asin z` or `atan z` is
refused `sort-real-only` (D20). Complex inverses by their logarithmic
forms are not built.

`abs z` is `sqrt((re z)^2 + (im z)^2)`, which is the real `abs` when z is
real. So the trusted complex core is the field, `conj`, `exp`, the
trigonometric and hyperbolic heads by formula, and one family of
logarithms. Adding a function means a case in `split` and, if it is
holomorphic, a rule in `deriv`'s table (E184).

**Z5: regions are conjunctions of real conditions** on `re z` and
`im z`, such as `@ im z > 0`, `@ abs(z - 1) < 2` or `@ re z >= 0, z # 0`.
A goal's domain is realified before discharge sees it (E168), so these
are the domains the kernel already handled, two real variables wide.
The region `residues in` takes is narrower: open half-planes and open
disks (E201, §2.3). The named regions the proposal listed (`disk(c, r)`,
`halfplane(…)`, `annulus(c, r1, r2)`, `slit[θ]`) are not built.

**Z6: branches carry their cut.** `log[θ] z` is
`ln(abs z) + i*arg[θ] z`, with `arg[θ] z` in (θ − 2π, θ].
- It owes `z` off the ray `{r*exp(i*θ) : r >= 0}`. The proposal owed
  this as one side of the ray or the other, the step naming which.
  As built it is one real judgement, `abs w - re(w*exp(-(i*θ))) > 0`,
  since `abs w >= re(w e^{-iθ})` with equality only on the ray (E185).
  No disjunction is needed, and for the principal branch it reads
  `sqrt((re w)^2 + (im w)^2) + re w > 0` (E188).
- The principal branch is θ = π, written `Log`, `Arg` and `Sqrt`. The
  proposal's `z ^^ w` is not built; `pow[pi](z, w)` is the principal
  power.
- Unit 20 P8's keyhole branch is θ = 2π, arg in (0, 2π] (E233).
- The real `ln`, `sqrt` and `^` keep their real meaning and domains,
  unchanged.

Making θ a parameter costs one argument, and it is the difference
between "principal branch only" and every cut a contour can need.

**θ is a closed real constant:** a literal, or a rational multiple of
`pi`, never a variable or an expression with one. Then the ray is fixed,
"is z on the cut" is a real condition on `re z` and `im z` with constant
coefficients (cos θ and sin θ evaluate by entries), and every cut
obligation stays one discharge can decide. A symbolic θ would buy no
contour the rules build, and would make every cut obligation possibly
undecidable. It is refused `branch-not-constant` at the parser (D19).

### 3.3 Paths, contour integrals, principal values

- **Paths** are a sort of their own (E190), built by:
  - `seg(a, b)`;
  - `arc(c, r, t1, t2)`, the circle about c from angle t1 to t2;
  - `path[t = a .. b] phi`, an explicit parametrisation;
  - joining, `g1 ++ g2` (left-associative), which owes that the end of
    g1 is the start of g2 (E191, E203);
  - reversal, `rev g`.

  `circle(c, r)` is `arc(c, r, 0, 2*pi)`. seg's ends and arc's centre
  take either sort; arc's r, t1, t2 and path's t, a, b are Real. A path
  is closed when its ends meet, which `residues` owes (E202), with every
  join's meeting (E211).
- **`CInt[z on g] f`** is a path integral, z bound in f and Complex
  (E190). **Its definition is its parametrisation** (Z7): the move
  `cint_param` replaces it, piece by piece, by
  `Int[t = a .. b] f[z := phi(t)] * D[t] phi(t)`, owing `phi in C^1` for
  a `path[t]` piece; it is additive over `++` and negated under `rev`
  (E191). The path's own data are charged as formers (E199). So every
  integral along an explicit path reduces to §5.1's integral of a
  complex-valued function of a real variable, with no new trusted rule.
  Until it is parametrised or evaluated by `residues`, a CInt is opaque:
  `field`, `split` and the limit evaluator refuse it (E192).
- **The winding number** of a closed path about a is **computed** by
  signed crossings of the ray to the right of a, by Sunday's half-open
  rule (E205). Each crossing of a segment or an arc part is a real sign
  decision on the path's data. The untrusted finder names a branch, a
  conjunction of real conditions, and the kernel owes it; when none
  settles, `wind-undecided` is the refusal.
- **The residue** at a pole of certified order is computed as in §5.4
  (E207).
- **`wind`, `res` and `lim[z -> a]` are not terms** (E200, E212). The
  winding numbers and residues are computed into the result of
  `residues`, and a complex limit appears only inside the limit
  evaluator (§5.3). A later stage may add them as terms without changing
  what any rule means.
- **`PV[x = a .. b] f`** is a principal value, a term written like an
  Int (E265): the limit as ε → 0+ of the integral over [a, b] with
  (p − ε, p + ε) removed round each of the finitely many points p where
  f is not defined. It is not an Int, so no Int move reads it as one,
  and it is opaque until a move evaluates it (E266). The move that does
  charges its body's formers on the range, exempting a divisor that is a
  polynomial over ℚ(i) (E272).

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
they never see a complex number (E168). Two additions were made beside
them: the limit evaluator's modulus law (E179) and an exact decision for
closed surds (E206). What the trusted base gains is **`split`**
(`kernel/complexes.py`, E167), a structural map from a complex term to
its pair:
- `i` is (0, 1), and a complex variable `z` is (`re z`, `im z`), two
  real atoms;
- sums and products are the textbook formulas;
- a quotient is `a*conj(b)/((re b)^2 + (im b)^2)`, owing that divisor
  `# 0`, built multiplicatively (E188), with an `exp` factor read as a
  negated exponent (E196);
- `exp(a + i b)` is `exp a * (cos b + i sin b)`;
- `sin`, `cos`, `sinh`, `cosh` by their addition formulas, `tan` and
  `tanh` as quotients;
- `log[θ] w` is (`ln(a^2 + b^2)/2`, `arg[θ] w`), with `arg[θ] w` an
  opaque real atom;
- an Int and a `D[x]` componentwise (E176), and a `D[z]` as the opaque
  atoms `re(D[z] e)` and `im(D[z] e)` (E189).

A declared function (a `Call`) is Real and takes only Real arguments
(D20), so `f(z)` is refused `sort-real-only`. The proposal's declared
complex function, an opaque atom with opaque parts, is not built.

The map is total on the terms it accepts and never guesses.

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
instances, and `field` checks them. The proposal ran it inside every
complex check. As built, the complex check takes `trig_norm`'s fallback
on each part in `ftc`'s check only, exactly as the real check does
(E197).

**E27 (fully evaluated) over ℂ** (E173). A closed subterm holding
complex structure (`i`, `re`, `im`, `conj`, `abs` of a Complex term,
`log[θ]`, `sqrt[θ]`) that is not in rectangular form counts as
unevaluated, and auto-simpl names `parts`. Rectangular is a Real term,
an imaginary term (`i`, `r*i`, `i/r`, …), or `r + m`, `r - m` with r
real and m imaginary. That is a property and not a canonical form, as
DESIGN.md §9's principle has it. `arg[θ]` of a closed value is left to
its entries and exact values (E172, E239). The closed whitelist admits
`i`, a complex variable, a branch and the new builtins. Auto-simpl
(E162) applies the complex evaluation entries as it applies the real
ones (E174).

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
- `verify` checks a complex candidate against a first-order linear ODE,
  and `re` recovers the real solution (verify refuses a D inside a D,
  `verify-nested-D`, E180);
- `int_improper` takes a complex limit as two real ones, or by
  `abs f -> 0` (§5.3, E179).

This is the tier with the most reach for the least code, and it closes a
gap the real kernel had: "`int_improper` for trig integrands (e^-x sin x
needs a squeeze law)". Here ∫₀^∞ e^{−x} sin x is `im` of
∫₀^∞ e^{(−1+i)x}, whose antiderivative has modulus e^{−x}/√2 → 0, so no
squeeze law is needed, and it proves (E180).

Two later moves belong to this tier. **Marked ends** (E222–E231) make
an integrand singular at a finite end statable: `Int[x = a+ .. b] f` is
the limit from inside, evaluated by `int_improper`, and the keyhole's
power integrands need it. **`int_re F` and `int_im F`** (E257) replace
`Int f` by `re(Int F)` or `im(Int F)` when `re F == f` (or `im F == f`)
checks by `field`, so a real integrand with `cos` or `sin` reaches the
exponential rules; they accept a PV as well (E268).

### 5.2 Functions of a complex variable

- **`D[z]`** is the complex derivative (E183). Its rules are `deriv`'s
  own (E184): constants, the variable, sums, negation, products,
  inverses, quotients and integer powers, and the App rules for `exp`,
  `sin`, `cos`, `sinh`, `cosh` and `tanh`, true over ℂ by the same
  algebra. Two are new: `d_log_branch`, `D log[θ] u == D u / u`, and
  `d_sqrt_branch`, each owing u off its cut (E185). `D[z]` of `conj`,
  `re`, `im`, `abs`, `arg[θ]` or a real-only head is refused
  `deriv-not-holomorphic`. The proposal had every defined function
  differentiate through its definition; as built each holomorphic head
  has its rule.
- **Holomorphy is not a stated judgement.** The proposal's `f in H(U)`,
  with closure rules, was not built (E183). It is owed inside
  `residues` instead (E202 (3)): `D[z] f` is derived by the holomorphic
  rules, each divisor it owes is nonzero on U minus S (E204), and each
  other side condition (a cut) holds on all of U.
- **Singular points, and completeness of S** (E204). Each divisor f
  owes, with its `exp` factors dropped (E196), is read factor by factor
  (E273). A factor must be a polynomial in z over ℚ(i), or of degree at
  most 2 with z-free coefficients, parameters included, whose
  discriminant's sign settles at the goal's domain (E274). An untrusted
  finder proposes the factorisation, and the kernel checks it by `field`
  on split parts, with `sqrt(E)^2 == E` facts for surd roots. Each root
  is then a point of S, owed in U, or owed outside U. There are no
  zero-set entries: `1/sin z` is refused `residue-divisor-not-polynomial`
  (E204).
- **Pole orders** come from the certified factorisation (E204, E207):
  a root's multiplicity in the divisor bounds the order. The proposal's
  `ord(h, a)` judgement is not built.
- **Cauchy–Riemann needs nothing new:** with z = x + i y, `verify`
  checks `D[x] re f == D[y] im f` on real terms.

### 5.3 Limits and estimates

**Only the modulus law is built** (E179). In a real variable, `re`,
`im` and `conj` commute with the limit; a complex term's limit is the
pair of its parts' limits when both are finite; otherwise, if
`(re G)^2 + (im G)^2 -> 0` then `G -> 0`. Finite limits combine as over
ℝ. A part with an infinite limit refuses `int-improper-diverges` (E182).

The proposal also had limits in a complex variable as terms,
continuity of holomorphic functions, removable singularities by order,
l'Hôpital in ℂ, the estimation lemma, and Jordan's lemma as an entry.
**None of these is built** (E212). The arc bounds are inside the
statements of Z10–Z13 (E213, E243, E267), and a removable point
contributes nothing to a residue sum by its order bound (E207).

### 5.4 Contour integrals and residues

**Z8: one theorem, Cauchy and residue together** (E200). Let U be open
and convex (§2.3 (3)), S a finite set of points of U, f holomorphic on
U minus S, and g a closed piecewise C¹ path in U that avoids S. Then

```
CInt[z on g] f == 2*pi*i * sum over a in S of wind(g, a) * res(f, a)
```

The move is `residues [in C, ...] [occurrence N]`. Without `in`, U is
ℂ. Every hypothesis is owed (E202): g closed, g in U piece by piece, f
holomorphic on U minus S, S complete (E204), its points distinct, in U
and avoided by g (E205). The CInt becomes the sum, each winding number
and residue computed (E208).

**The region's form is the certificate** (E201): an intersection of
open half-planes and open disks is convex, so star-shaped about each of
its points. The proposal's slit plane, star-shaped about any point of
the opposite ray, is not built.

With S empty it is Cauchy's theorem. With the winding numbers computed,
it covers contours that wind twice or run clockwise (K4B_CASES). A cut
in f is allowed when U avoids it: `CInt[w on circle(2, 1)] Log w` is 0
by `residues in re w > 0`. Keyholes are Z11 (§5.5). **No contour shape
appears in the rule.**

**Residues are computed by one rule, partial** (E207). At a point a of
S, the pole order bound m of f is computed by structure from the
certified multiplicities: 0 for a term with no divisor vanishing at a, a
sum's largest, a product's sum, x/d's x's plus a's multiplicity in d,
and n times u's for u^n. Then:
- **m = 0:** a is removable and contributes nothing;
- **m ≥ 1:** φ = (z − a)^m f is built by structure, equal to it off S
  by the factorisation, and
  `res(f, a) == (D[z]^(m-1) φ at z := a) / (m - 1)!`, by `deriv`'s rules
  and substitution. This is the Laurent coefficient of 1/(z − a), since
  φ is holomorphic at a;
- **an application whose argument has a pole** (`exp(1/z)` at 0, an
  essential singularity) is refused `residue-not-a-pole`. A residue by
  the Laurent coefficient waits for `Sum` (§9).

A repeated derivative past 15000 nodes is refused `residues-too-large`
(E221).

**Z9, the argument principle as a rule, is not built** (E232). While h
is a polynomial, `residues` proves `CInt[z on g] D[z] h / h` directly,
so the rule would add nothing until h is not one. Rouché's count of
zeros (unit 20 P10) is not reached.

### 5.5 The course methods (trusted rules)

The proposal had five untrusted tactics composing Z8, the estimation
lemma and `lim[R -> oo]`. As built, each is a trusted theorem stated
once, with its hypotheses owed and a decay certificate checked (E212):

| Rule | Move | Its theorem | Its certificate |
|---|---|---|---|
| **Z10**, closing in a half-plane | `residues upper` / `residues lower` on `Int[x = -oo .. oo] f` | the integral converges and equals 2πi (upper) or −2πi (lower) times the residues in that half-plane (E213) | f[x := z] = exp(u)·P/Q with u affine; (R) deg Q ≥ deg P + 2, or (J) re α = 0, a = im α of the half-plane's sign, deg Q ≥ deg P + 1 (E214); Q's roots off the line (E215) |
| Bromwich | the same, in y with s = σ + iy | Z10, where exp(s t) is (J) with a = t (E213) | Z10's |
| **Z11**, the keyhole | `residues keyhole` on an Int from 0 or 0+ to oo | the power form, x^α R(x) for α not an integer, and the log form for an integer α (E233) | x^α·P/Q by structure, α's conditions and the degree test owed, every root off [0, oo) (E234, E235) |
| **Z12**, the sector | `residues sector` on `Int[x = 0 .. oo]` | exp(i a x²), its conjugate, cos(a x²), sin(a x²), and the Gaussian (E243) | the quadratic phase only: h is exp, cos or sin of k x², with k's sign owed (E244) |
| **Z13**, indentation | `residues upper` / `residues lower` on `PV[x = -oo .. oo] f` | Z10's sum plus πi (upper) or −πi (lower) times the residues at the simple real poles (E267) | Z10's, with real roots allowed if simple (`pv-pole-not-simple` otherwise) |

Three moves feed them. `int_even` takes an even integrand between
[0, oo) and the whole line, both ways, checked by `field` with parity
facts for `sin` and `cos` (E217, E245, E258). `int_re` and `int_im` take
a real integrand to re or im of a complex one (E257, E268). And Z10 and
Z11 split a z-free factor off by structure before the certificate
(E242).

**Readiness P5**, ∫₀^∞ dx/(1 + x⁴), is proved by a hand-found
partial-fraction antiderivative (`kernel/problems/improper/P5.json`).
By residues it proves as `int_even.` then `residues upper.`, closing to
π/(2√2) (K4C_CASES):
- `int_even` makes it half of ∫_{−∞}^{∞}, checking f(−x) == f(x);
- q = 1 + z⁴ factors as `(z - a1)(z - a2)(z - a3)(z - a4)` with
  a = e^{±iπ/4}, e^{±3iπ/4}, biquadratic surds the kernel checks with
  `sqrt_sq_val` at 2 (E204);
- two of the roots lie in the upper half-plane;
- each residue is a simple pole's, 1/(4a³), and their sum is
  `-i*sqrt 2/4`.

2πi times that is π/√2, and half of it is π/(2√2), P5.json's value.
The same theorem by a second route the kernel checks, and the one the
readiness sheet itself names as the alternative to its real method.

## 6. What it added to the trusted base

The proposal sized each piece in advance. As built, the trusted pieces
are these; ARCHITECTURE.md §16 says what each file gained.

| Piece | Decisions |
|---|---|
| the sort table and checker, `i`, complex variables, the branches | E166, E175 (D19, D20) |
| `split`, and obligations kept real | E167, E168, E176, E188, E189, E196 |
| complex equality by `ring` and `field` on both parts | E169, E197 |
| `deriv` over ℂ: a real variable, then `D[z]` | E177, E184, E185 |
| regularity over ℂ | E178, E188 |
| the modulus law in the limit evaluator | E179 |
| entries: `arg` values, `arg_branch`, periodicity, the trig table, `atan` values, two sine bounds | E172, E181, E239, E253 |
| `cint_param` | E191, E199 |
| Z8 and the residue rule | E200–E208, E211 |
| closed surds decided exactly | E206 |
| Z10, `int_even` | E213–E217, E245, E258 |
| marked ends in `int_improper` | E222–E226 |
| Z11 | E233–E236, E240 |
| Z12 | E243, E244 |
| the tracker's upgrade of an admission | E250, E251 |
| `int_re`, `int_im` | E257, E268 |
| `PV` and Z13 | E265–E267, E272 |
| symbolic quadratic factors | E273–E275 |

**Untrusted:** the root finder (`roots.py`: roots over ℚ(i), surds and
biquadratics, denesting, E204, E263), the winding branch and side
proposals, the non-integer bracket for α (E240), `parts`' simplifier
(E170), E27 over ℂ (E173), auto-simpl, and the page, TeX, untex and
palette work.

## 7. Soundness

**The claim keeps its form:** every result reported as proved carries a
derivation the kernel checked (DESIGN.md §15.1). The new trusted pieces
are:
- the sort table;
- `split`, whose identities the suite also checks numerically, at 200
  random points per term (K1_CASES), as the TeX printer's round trip is
  checked;
- the entries;
- the rules of §5.

Everything that finds something stays untrusted, and a bug in it costs a
refusal: roots, winding branches, which side of a cut or a line to owe,
trig instances, and the parts `parts` proposes. The kernel suite also
checks each `residues` value against Simpson's rule on its path (E210).

**Each stage ended with a skeptic's review**, recorded in its last
decision (E175, E182, E189, E199, E211, E221, E231, E241, E249, E256,
E264, E272, E280). Blocking findings were found and fixed in K1 (a
minted fact's conclusion was not sort-checked, E175), K2 (`split`
dropped an unstatable Int, E182), K4a (an opaque CInt could be erased,
and a path's data owed nothing, E199), K4b (three false theorems about
arcs, joins and `path[s]` pieces, E211), marked ends (an empty range,
E231) and principal values (a PV owed nothing about its body, E272).
The other reviews found no false theorem.

**The traps, and what refuses each one.** Each row is an identity a CAS
will apply that is false somewhere:

| Trap | Why false | Refused by |
|---|---|---|
| `log(z*w) == log z + log w` | off by 2πi across the cut | no such entry; `log[θ]` splits to `ln abs` and `arg[θ]`, and `arg` of a product is not a sum |
| `sqrt(z^2) == z` | false where the branch flips | no entry; `sqrt[θ] w` splits as `exp(log[θ](w)/2)` (E167) |
| `pow(pow(z, a), b) == pow(z, a*b)` | branch | no entry |
| `log(exp z) == z` | im z outside the branch's range | no entry |
| `abs(z)^2 == z^2` | true only for real z | `split` makes them different reals |
| `z < w` on complex terms | ℂ has no order | `sort-order-on-complex` at parse |
| `exp_pos` at `i*pi`, giving `exp(i*pi) > 0` | an order entry read at a complex point | a minted fact's conclusion is sort-checked (E175) |
| `D[z] conj z` | not holomorphic | `deriv-not-holomorphic` |
| Cauchy on a region with a hole | the hole can carry a singularity | the region's form: only open half-planes and disks, else `region-not-convex` (E201) |
| a pole on the contour | the integral is not defined | g must avoid S, owed: `residue-pole-on-path` (E205); on the line, `residue-pole-on-line` (E215); on the keyhole's cut, `residue-pole-on-cut` (E234) |
| a missed singularity | wrong value | completeness of S: a factorisation `field` checks (E204); a divisor that is not a polynomial refuses |
| a symmetric limit read as an improper integral | they agree only when the improper integral exists | convergence is part of Z10's theorem, absolute under (R) and by Dirichlet's test under (J) (E213); a principal value is its own term, `PV`, which no Int move reads (E265) |
| a path that is not C¹ | the definition needs `phi'` | `phi in C^1` owed piece by piece (E191, E211) |

## 8. The order of work

**The build order is about effort, not about meaning.** Every stage
implements its part of the general design, so a later stage adds rules
and never revisits an earlier one. Each stage is spec-first, built, and
attacked by a skeptic, and ends with course problems that prove.

The proposal's plan was K1 → K2 → K3 → K4, then a stage T of tactics.
K4 was built in parts, and T was replaced by trusted rules (E212). As
built, with what each stage's cases prove from the test set:

| Stage | Built | Decisions | Proves from the test set |
|---|---|---|---|
| **K1** arithmetic | sort table, `i`, branches, `split`, complex `ring`/`field`, `parts`, E27 over ℂ | E165–E175 | 06 P2's (1 + i)⁸ = 16; e^{iπ} = −1 and Log(−1) = iπ |
| **K2** a real variable | componentwise `deriv`, `ftc`, `verify`, regularity, the modulus law, periodicity | E176–E182 | ∫₀^∞ e^{−x} sin x = 1/2 |
| **K3** a complex variable | `D[z]`, branches off their cut | E183–E189 | Cauchy–Riemann by `verify` |
| **K4a** paths | `seg`, `arc`, `circle`, `path[t]`, `++`, `rev`, `CInt`, `cint_param` | E190–E199 | 34 P6's ∮ dz/z = 2πi and ∮ z̄ dz = 2πi on the unit circle |
| **K4b** residues | Z8 with `in`, factorisation, winding by crossings, E207's residues | E200–E211 | 20 P4's circles: \|ω − 8\| = 1 gives −5πi/√1599, \|ω\| = 10 gives 0 |
| **K4c-i** a line | Z10, `int_even` | E212–E221 | readiness P5 by residues, π/(2√2) |
| marked ends | `a+`, `b-` in `int_improper` | E222–E231 | unit 00 P7's B(1, 1/2) |
| **K4c-ii** keyhole | Z11 | E232–E241 | 20 P8 at a = 1/3; symbolically, modulo one admission (E240) |
| sector | Z12, and E242's factor split | E242–E249 | 20 P6's Fresnel integrals, √(π/8) each; 20 P9's inversion for t > 0 and t < 0, modulo one admission (E246) |
| tracker upgrade | a later discharge replaces an admission | E250–E252 | 20 P9 with nothing admitted |
| sine bounds | `sin_pos_on`, `sin_pos_pi` | E253–E256 | 20 P8 in full: π/sin(πa) for 0 < a < 1, nothing admitted (E255) |
| re and im | `int_re`, `int_im`, parity in `int_even`, denesting | E257–E264 | 20 P7's two exact checks: χ′(0) = 1/64 and the sum rule's π/2 (E263) |
| principal values | `PV`, Z13 | E265–E272 | PV ∫ sin x/x = π |
| symbolic coefficients | quadratic factors with parameters | E273–E280 | 20 P5's two integrals, with D written as the course factors it (E276) |

Each claim is a case in p1_expected, and as of E280 each reads
`Proved.` with nothing admitted. 20 P6's convergence argument is prose
and is not checked (E247), and 20 P9's first maximum is numerical,
outside the kernel (E246). 20 P5 states 4ω₀² − γ² > 0 in its domain,
since discharge does not derive it from γ < 2ω₀ (E279).

**What does not prove**, from the test set: 20 P10 (Rouché, Lagrange
inversion, a radius of convergence), P11, and P12 (steepest descent);
Kramers–Kronig for an abstract χ, 20 P7's first part, which is a theorem
about a class of functions, not a computation (E270); and 20 P5 with D
written as one expanded quartic (E277). 24 P9, the retarded Green's
function by residues, has no case in p1_expected and is not claimed.
What stays unreachable is in §9, each item with what would bring it in.

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
| Rouché's theorem | one rule on top of the argument principle and an estimate, neither built | no |
| Conformal maps, Möbius transformations | entries, and a move for change of variable in `CInt` | no |
| Other cut placements, other branches | a θ | no: Z6 has it |
| Multiply connected regions | cut into convex pieces (the course's own method) | no |
| Limit terms and the estimation lemma | `lim` as a term, then the lemma as a rule (E212) | no |
| Zero-set entries (1/sin z) | an entry per head, read by E204's completeness check | no: E204 is additive by design |
| Z9, the argument principle, as a rule | one rule, needed once h is not a polynomial (E232) | no |
| Kramers–Kronig for an abstract χ | a theorem about a class of functions, not a computation (E270) | out of scope as computation, below |
| A PV over a finite range, or with a double pole | a finite-range indentation; a double pole has no principal value in general (E270) | no |
| Symbolic factors of degree > 2 (the expanded quartic D) | a symbolic factoriser beyond the quadratic formula (E277) | no |
| Symbolic roots in Z11 and Z12 | their certificates taking E274's roots (E277) | no |
| Phases xⁿ with n > 2 in the sector | Γ(1/n) in the term language (E243, E247) | no |
| A sector with complex k, re k < 0 and im k ≠ 0 | a wider Z12 certificate (E247) | no |
| Interior singularities in an Int | a split at the point (E228) | no |
| The `diverges` judgement at a marked end | DESIGN.md's `diverges` (E228) | no |
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

**Status (2026-10-15, E280).** The test-set problems listed as proving
in §8 prove as p1_expected cases, with nothing admitted: 06 P2's
(1 + i)⁸, 34 P6's two contour integrals, 20 P4's circles, 20 P5 (with D
as the course factors it), 20 P6's Fresnel values, 20 P7's two exact
checks, 20 P8 in full, 20 P9's inversion (written in y, s = 1 + iy),
unit 00 P7's B(1, 1/2) and readiness P5 by residues. Where a problem
needed more than the stage had, the addition was general: `int_re` for
E218's cos x/(1 + x²) (E257), marked ends for singular ends (E222), the
quadratic formula for symbolic factors (E273). 20 P10–P12,
Kramers–Kronig for an abstract χ and 24 P9 stay out, with their reasons
in §8 and §9.

## 11. Decisions for the owner, with recommendations

**These are decided.** Each was recommended here on 2026-10-14. The
owner took the recommendations for Z1–Z9 and chose to build now, before
the gate, which waits (E165). Item 7 is the one decided otherwise than
recommended. The items are kept as they were written, so the reasons
stay on record, with a note where the build changed one.

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
   obligation is decidable. *(As built: `Log`, `Arg`, `Sqrt` and
   `pow[θ]`; `^^` is not built, §3.2.)*
5. **Z8: yes.** Without it no real integral is evaluated by a contour,
   which is most of what complex analysis is for here. The theorem is
   textbook, its hypotheses are decidable obligations, and §14 covers
   machine-checking it later. **Z9: yes, built last in K4**: only unit 20
   P10 needs it, and it reuses K4's machinery. *(As built: Z8 with convex
   regions only, E201. Z9 is not a rule, since `residues` proves
   CInt of h'/h for a polynomial h, E232.)*
6. **`Sum` sort-polymorphic (§9): agree now.** It costs nothing before
   `Sum` is built and a redesign after.
7. **When: after the gate.** The gate is the project's falsifier
   (DESIGN.md §17), its seventeen problems are real, and nothing here
   helps answer it. This work is about 3,500 lines, worth doing if the
   tool survives the gate. If it is not to wait, K1 and K2 are where to
   start: small, most of the course's complex use, and they close the
   e^{−x} sin x gap. *(Decided otherwise: the owner chose to build now,
   and the gate, app/GATE.md, waits, E165.)*

Within the build, the order was K1 → K2 → K3 → K4, each spec-first in
p1_expected, each ending with its test-set problems proving. K4 was
built in the parts the Status lists.

**What would change this design.** A soundness finding in `split`, the
one piece every complex check relies on, would be the reason to prove
its identities in §14's rule-table prover. A need for several complex
variables or a point at infinity would reopen Z1. If Z8's convex
regions meet an integral they cannot reach by cutting the region into
pieces, the homology form is the next step: Z8 with a decided "winding
number zero outside U" in place of the region's form. And limit terms
would let the estimation lemma in, beside Z10–Z13 (E212).
