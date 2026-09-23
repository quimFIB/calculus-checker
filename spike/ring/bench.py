"""Timings for the stage 0c spike — §16.2's one named speed risk, and §18 Q18.

    python3 bench.py            the full ladder of sizes
    python3 bench.py --quick    the small end only, as a smoke test

Run it on an idle machine: it reports the load average first and says so if
something else is competing, because a timing taken under load measures the
load. The budget column is §8.6's tenth of a second — the latency a move can
spend before §1's loop stops feeling instant.

Each case is a check the kernel would actually run: `deriv` then `ring` or
`field` on a derivative as §6.3 states it, untidied, or a scaling family
chosen to stress one part of the normaliser.
"""

import os
import statistics
import sys
import time
from fractions import Fraction
from math import prod

from deriv import deriv
from field import field, ring
from terms import parse

BUDGET_MS = 100


def timed(fn, min_total=0.3, max_runs=25):
    times = []
    start = time.perf_counter()
    while len(times) < max_runs:
        t0 = time.perf_counter()
        result = fn()
        times.append(time.perf_counter() - t0)
        if time.perf_counter() - start > min_total and len(times) >= 3:
            break
    return statistics.median(times) * 1000, result


# ---------------------------------------------------------------- cases

def readiness_p1_1():
    """§11.1: deriv; ring on F = 2 sin t − 2t cos t."""
    dF = deriv(parse("2*sin t - 2*t*cos t"), "t")
    goal = parse("sin t * (2*t)")
    return lambda: ring(dF, goal)


def readiness_p1_2():
    """§11.2: deriv; field with (sqrt 3)^2 ≐ 3 — the flagship."""
    F = parse("(1/3)*ln(1+x) - (1/6)*ln(x^2 - x + 1)"
              " + (1/sqrt 3)*atan((2*x - 1)/sqrt 3)")
    goal = parse("1/(1 + x^3)")
    return lambda: field(deriv(F, "x"), goal, facts=[("(sqrt 3)^2", "3")])


def quadratic_drag():
    """Unit 00 P4: m v' = m g − k v², v = V tanh(g t / V), V² = m g / k."""
    v = parse("sqrt(m*g/k) * tanh(g*t/sqrt(m*g/k))")
    lhs = ("mul", parse("m"), deriv(v, "t"))
    rhs = ("add", parse("m*g"), ("neg", ("mul", parse("k"), ("pow", v, 2))))
    return lambda: field(lhs, rhs, facts=[("sqrt(m*g/k)^2", "m*g/k")])


def repeated_quadratic():
    """∫ dx/(x²+1)² — F = x/(2(x²+1)) + atan(x)/2, a repeated factor."""
    F = parse("x/(2*(x^2 + 1)) + atan(x)/2")
    goal = parse("1/(x^2 + 1)^2")
    return lambda: field(deriv(F, "x"), goal)


def partial_fractions(n):
    """deriv; field on Σ A_k ln(x − k) against 1/∏(x − k), n linear factors."""
    coeffs = [Fraction(1, prod(k - j for j in range(1, n + 1) if j != k))
              for k in range(1, n + 1)]
    F = " + ".join(f"({a.numerator}/{a.denominator})*ln(x - {k})"
                   for k, a in zip(range(1, n + 1), coeffs))
    goal = "1/(" + "*".join(f"(x - {k})" for k in range(1, n + 1)) + ")"
    dF, g = deriv(parse(F), "x"), parse(goal)
    return lambda: field(dF, g)


def telescoping(n):
    """Σ 1/((x+k)(x+k+1)) ≐ 1/(x+1) − 1/(x+n+1): n shared factors."""
    lhs = parse(" + ".join(f"1/((x + {k})*(x + {k + 1}))" for k in range(1, n + 1)))
    rhs = parse(f"1/(x + 1) - 1/(x + {n + 1})")
    return lambda: field(lhs, rhs)


def continued_fraction(n):
    """1/(1 + 1/(1 + … x)), n deep, against its Möbius closed form."""
    t = parse("x")
    for _ in range(n):
        t = ("div", ("num", Fraction(1)), ("add", ("num", Fraction(1)), t))
    a, b, c, d = 1, 0, 0, 1  # x ↦ (a x + b)/(c x + d)
    for _ in range(n):
        a, b, c, d = c, d, a + c, b + d
    closed = parse(f"({a}*x + {b})/({c}*x + {d})")
    return lambda: field(t, closed)


def expansion(n):
    """(x + y + z + 1)^n ≐ ((x + y) + (z + 1))^n, by ring: pure expansion."""
    lhs = parse(f"(x + y + z + 1)^{n}")
    rhs = parse(f"((z + 1) + (y + x))^{n}")
    return lambda: ring(lhs, rhs)


def cases(quick):
    yield "§11.1  deriv; ring", "", readiness_p1_1()
    yield "§11.2  deriv; field + fact", "", readiness_p1_2()
    yield "P4 quadratic drag, field + fact", "", quadratic_drag()
    yield "∫ 1/(x²+1)², deriv; field", "", repeated_quadratic()
    for n in ([2, 4] if quick else [2, 4, 8, 12, 16]):
        yield "partial fractions, deriv; field", f"n={n}", partial_fractions(n)
    for n in ([4, 16] if quick else [4, 16, 64, 128]):
        yield "telescoping sum, field", f"n={n}", telescoping(n)
    for n in ([4, 8] if quick else [4, 8, 16, 32]):
        yield "continued fraction, field", f"depth={n}", continued_fraction(n)
    for n in ([4, 8] if quick else [4, 8, 12, 16]):
        yield "(x+y+z+1)^n, ring", f"n={n}", expansion(n)


def main():
    quick = "--quick" in sys.argv
    load = os.getloadavg()[0]
    cpus = os.cpu_count() or 1
    print(f"python {sys.version.split()[0]}   load {load:.2f} on {cpus} cpus")
    if load > 0.5:
        print("!! the machine is not idle: these timings measure the load too")
    print()
    head = f"{'case':<34} {'size':<9} {'ms':>9}  {'num terms':>9} {'den':>4}  holds"
    print(head)
    print("-" * len(head))
    for name, size, fn in cases(quick):
        ms, r = timed(fn)
        flag = "  > budget" if ms > BUDGET_MS else ""
        print(f"{name:<34} {size:<9} {ms:9.2f}  {r.numerator_terms:>9} "
              f"{r.denominator_factors:>4}  {r.holds}{flag}")


if __name__ == "__main__":
    main()
