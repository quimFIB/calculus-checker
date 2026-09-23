"""The recognizer corpus (DESIGN.md §17): integrals, and the technique the
course's own worked solution uses for each.

Source: `courses/published-courses/mechanics-to-relativity/units/`, the
readiness sheet (P1, P2, P5 — the integral problems; P3–P4 are series) and
unit 00 (P1, P3, P4, P7, P8, P9 — the problems that integrate). Each entry
quotes the hint or solution line its label comes from. Intermediate integrals
are included when the solution reaches them, because the recognizer runs on
every goal after every move, not only on the first (§8.5, the progress
signal).

`technique` is the family the course's solution uses. `also` lists families
that are also a correct first move, which the lenient score accepts; the
strict score does not, because §17's test is whether the recognizer names
*the technique the course's own worked solution uses*.

Families are the `family` field of rows.py. The course sometimes uses a
technique no row in a given table covers; that is scored as a table gap,
separately from a wrong row.
"""

CORPUS = [
    # ---- readiness P1
    dict(id="R-P1.1", x="x", integrand="sin(sqrt x)",
         technique="root substitution",
         source="readiness P1(1), rung 2: 'Remove the root with a substitution.'"),
    dict(id="R-P1.1b", x="t", integrand="t * sin t",
         technique="parts",
         source="readiness P1(1), rung 2: 'a polynomial times a sine, which is a job for parts'"),
    dict(id="R-P1.2", x="x", integrand="1/(1 + x^3)",
         technique="partial fractions",
         source="readiness P1(2), rung 2: 'Factor 1+x^3 … and split into partial fractions.'"),
    dict(id="R-P1.2b", x="x", integrand="(x - 2)/(x^2 - x + 1)",
         technique="split numerator",
         source="readiness P1(2), rung 2: 'split the quadratic's numerator into a multiple "
                "of the denominator's derivative plus a constant'"),
    dict(id="R-P1.2c", x="x", integrand="1/((x - 1/2)^2 + 3/4)",
         technique="standard",
         source="readiness P1(2), solution: '∫ dx/((x−½)²+¾) = (2/√3) arctan((2x−1)/√3)'"),
    # ---- readiness P2
    dict(id="R-P2.1", x="theta", integrand="1/(1 + e*cos theta)",
         technique="Weierstrass",
         source="readiness P2, rung 2: 'Part 1: substitute t = tan(θ/2).'"),
    dict(id="R-P2.2", x="theta", integrand="1/(1 + e*cos theta)^2",
         technique="parameter differentiation", also=["Weierstrass"],
         source="readiness P2, rung 2: 'Part 2: add a parameter … and differentiate in a.'"),
    dict(id="R-P2.1b", x="t", integrand="2/((a + e) + (a - e)*t^2)",
         technique="standard",
         source="readiness P2, solution: '= 2/√((a+e)(a−e)) [arctan(√((a−e)/(a+e)) t)]'"),
    # ---- readiness P5
    dict(id="R-P5", x="x", integrand="1/(1 + x^4)",
         technique="partial fractions",
         source="readiness P5: 'Evaluate … exactly by partial fractions'"),
    dict(id="R-P5b", x="x", integrand="(x + sqrt 2)/(x^2 + sqrt(2)*x + 1)",
         technique="split numerator",
         source="readiness P5, solution: 'Write x ± √2 = ½(2x ± √2) ± √2/2' — log plus arctan"),
    # ---- unit 00 P1
    dict(id="U00-P1a", x="w", integrand="m/(-m*g - b*w)",
         technique="log",
         source="unit 00 P1(a): 't = ∫ m dw/(−mg − bw)' — a logarithm, per P3's rung 4"),
    dict(id="U00-P1c", x="t", integrand="F0 * exp(-t/tau)",
         technique="standard",
         source="unit 00 P1(c): 'integrate once, ẋ(t) = v0 + (F0τ/m)(1 − e^{−t/τ})'"),
    # ---- unit 00 P3
    dict(id="U00-P3", x="w", integrand="1/(w + vinf)",
         technique="log",
         source="unit 00 P3, rung 4: 'Separating gives a logarithm'"),
    dict(id="U00-P3b", x="t", integrand="-vinf + (v0 + vinf)*exp(-t/tau)",
         technique="standard",
         source="unit 00 P3(a): '∫₀ᵗ v = −v∞t + τ(v0+v∞)(1 − e^{−t/τ})'"),
    # ---- unit 00 P4
    dict(id="U00-P4", x="w", integrand="M/(M*g - c*w^2)",
         technique="standard", also=["partial fractions"],
         source="unit 00 P4, rung 3: 'an inverse hyperbolic tangent — or partial fractions "
                "and two logarithms, if you prefer'"),
    dict(id="U00-P4b", x="s", integrand="tanh(g*s/vinf)",
         technique="log",
         source="unit 00 P4, rung 4: 'what function differentiates to tanh' — ln cosh"),
    # ---- unit 00 P7
    dict(id="U00-P7", x="x", integrand="1/sqrt(E - k*x^n)",
         technique="Beta substitution",
         source="unit 00 P7, rung 3: 'Scale out the turning point first: x = aσ', then "
                "rung 4: 'substitute u = σⁿ' — a Beta function"),
    dict(id="U00-P7b", x="sigma", integrand="1/sqrt(1 - sigma^n)",
         technique="Beta substitution",
         source="unit 00 P7, rung 4: 'substitute u = σⁿ and be careful with dσ'"),
    dict(id="U00-P7c", x="u", integrand="1/sqrt(u*(1 - u))",
         technique="trig substitution",
         source="unit 00 P7(b): 'B(½,½) = ∫ du/√(u(1−u)) = π (substitute u = sin²φ)'"),
    # ---- unit 00 P8
    dict(id="U00-P8", x="s", integrand="1/sqrt(s^2 - st^2)",
         technique="hyperbolic substitution",
         source="unit 00 P8, rung 4: '∫ ds/√(s² − s_t²) is an inverse hyperbolic cosine'"),
    dict(id="U00-P8b", x="s", integrand="s^(-1/2)",
         technique="standard",
         source="unit 00 P8(a): '∫₀^δ s^{−1/2} ds' — the comparison integral"),
    # ---- unit 00 P9
    dict(id="U00-P9", x="s", integrand="-kappa*s + alpha*s^3",
         technique="standard",
         source="unit 00 P9, rung 5: 'V(x) = −∫₀ˣ(−κs + αs³) ds'"),
]


# Held out: taken from units 01–10 after V2 was written, and not used to
# change it. V2's score here is the only evidence that its extra rows
# generalise rather than memorise.
HELD_OUT = [
    dict(id="U01-P2", x="u", integrand="1/(u*ln(1/u))",
         technique="log",
         source="unit 01 P2, rung 5: 'For the integral, substitute w = ln(1/u)' — "
                "which gives ∫ dw/w"),
    dict(id="U01-P9", x="w", integrand="w/sqrt(1 - w^2)",
         technique="chain-rule substitution", also=["trig substitution"],
         source="unit 01 P9, rung 4: 'the integrand becomes w/√(1−w²)' and is "
                "elementary. The course names no technique; this label is the "
                "textbook move (u = 1 − w²), not the course's"),
    dict(id="U02-P1", x="x", integrand="1/x^2",
         technique="standard",
         source="unit 02 P1: '∫ dx/x² = ∫ dt ⟹ −1/x = t + C'"),
    dict(id="U04-P3", x="t", integrand="sin t*(-sin t) + (-cos t)*cos t",
         technique="identity first",
         source="unit 04 P3: '∮ = ∫[sin t(−sin t) + (−cos t)(cos t)] dt = −∫ 1 dt' — pyth"),
    dict(id="U04-P4", x="t", integrand="-2*(1 - t)^2",
         technique="standard",
         source="unit 04 P4: 'Contribution ∫₀¹ −2(1−t)² dt = −2/3'"),
    dict(id="U06-P7", x="u", integrand="exp(-gamma*u/2) * sin(omegad*u) / omegad",
         technique="guess and verify", also=["parts"],
         source="unit 06 P7, rung 2: 'compute H(t) = ∫₀ᵗ G … Guess the antiderivative "
                "and verify by differentiating'"),
    dict(id="U08-P12", x="theta", integrand="1/(1 + cos theta)^2",
         technique="Weierstrass",
         source="unit 08 P12, rung 2: 'Use 1 + cos θ = 2cos²(θ/2), then substitute "
                "τ = tan(θ/2)'"),
    dict(id="U09-P1", x="r", integrand="1/sqrt(2*eps + 2*G*M/r - h^2/r^2)",
         technique="trig substitution",
         source="unit 09 P1, rung 2: 'complete the square in r′', then r′ = a(1 − e cos E′)"),
    dict(id="U10-P3", x="x", integrand="(1 - x^2)^n",
         technique="parts",
         source="unit 10 P3: 'For I_n, integrate by parts with u = (1−x²)ⁿ, dv = dx'"),
]
