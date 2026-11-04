"""Replay the rational inequalities in the 31/20 comparison and its lower example."""

from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "toolkit"))
from threshold_toolkit.rare_event_functional import (
    FiniteGapLaw,
    evaluate_selection,
    quantile_split,
)


def taylor(x):
    """Degree-eight lower bound on exp(x) for x >= 0."""
    return sum(x**j / factorial(j) for j in range(9))


def check_upper():
    c = F(16, 9)
    # The weights at offsets 0,1,2 have lower gap ratios 1,1,2.
    # The rest are bounded by a geometric series beginning at ratio 4.
    mass_bound = (
        2 / taylor(c - 1)
        + 1 / taylor(2 * c - 1)
        + 1 / taylor(4 * c - 1) / (1 - 1 / taylor(4 * c))
    )
    assert mass_bound < 1
    assert taylor(F(111, 160)) > 2
    k, a, b = F(31, 20), F(37, 40), F(77, 80)
    assert F(4, 3) * F(111, 160) == a and a * a + b * b >= c
    # Coefficients in ascending powers of y at x=1 of the homogeneous quartic.
    u, v, w = 4 * k + a * a, 2 * a * b, 4 * k + b * b
    p = [
        16 * k**4 - u * u - 16 * k * k,
        -2 * u * v,
        32 * k**4 - v * v - 2 * u * w - 16 * k * k,
        -2 * v * w,
        16 * k**4 - w * w,
    ]
    e, d, c2, b3, a4 = [
        sum(p[i] * comb(i, j) * F(1, 3) ** (i - j) for i in range(j, 5))
        for j in range(5)
    ]
    assert a4 > 0 and 24 * a4 > b3 * b3
    assert c2 > 6 and 4 * (c2 - 6) * e > d * d


def check_lower():
    t, step, rho = F(1, 2**20), 1 + F(1, 2**20), F(1, 8)
    atoms = [(t, rho * (1 + F(7, 12)))]
    for multiple, cost in [(1, F(1, 10)), (2, F(1, 192)), (4, F(1, 65536))]:
        ratio = multiple * step
        atoms.append((t * ratio, rho * cost * ratio**2))
    atoms.append((F(1, 2), 1 - sum(mass for _, mass in atoms)))
    law = FiniteGapLaw(atoms)
    budget = (16 / t) ** 2
    core, threshold = quantile_split(law, rho)
    assert threshold == t and core == (F(7, 19), 1, 1, 1, 1)
    q = evaluate_selection(law, core, rho=rho, budget=budget)
    witness = evaluate_selection(law, [1, 0, 0, 0, 1], rho=rho, budget=budget)
    assert 0 < witness.upper < rho and q.lower > F(146255, 100000) * witness.upper


if __name__ == "__main__":
    check_upper()
    check_lower()
    print("Verified all rational bounds for 1.46255 < sup(Q/K) <= 31/20.")
