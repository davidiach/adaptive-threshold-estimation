"""Certify a trillionth-wide bracket on the sharp universal Q/K factor."""

from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "toolkit"))
from threshold_toolkit.rare_event_functional import (
    FiniteGapLaw,
    Precision,
    evaluate_selection,
    quantile_split,
)

LOWER = F("1.462554551279")
UPPER = F("1.462554551280")
GRID = 1 << 100


def round_up(x):
    return F(-(-x.numerator * GRID // x.denominator), GRID)


def exp_negative_upper(x):
    """Enclose exp(-x) from above using alternating terms and directed squaring."""
    assert x >= 0
    squares = 0
    while x > 1:
        x /= 2
        squares += 1
    term = value = F(1)
    for j in range(1, 23):
        term *= -x / j
        value += term
    # Ending at the even term 22 gives an upper bound for 0 <= x <= 1.
    value = round_up(value)
    for _ in range(squares):
        value = round_up(value * value)
    return value


@lru_cache(maxsize=None)
def criterion_upper(u):
    k = UPPER
    slope = 2 * k * k * (u + 1 / u) - 4 * k
    assert slope >= 2
    value = exp_negative_upper(slope / (2 * u) - 1)
    for m in (1, 2, 4, 8, 16):
        value += exp_negative_upper(slope * m - 1)
    # Bound the omitted dyadic weights by all integer weights m >= 32, using e > 2.
    return value + F(4, 3 * 2**63)


def certify_upper():
    assert UPPER**2 >= 2 and UPPER <= F(31, 20)
    cells = [(F(1), F(31, 20), 0)]
    count = depth = 0
    while cells:
        left, right, level = cells.pop()
        # F'' >= -25, so the chord plus 25*(right-left)^2/8 bounds the entire cell.
        bound = (
            max(criterion_upper(left), criterion_upper(right))
            + 25 * (right - left) ** 2 / 8
        )
        if bound < 1:
            count += 1
            depth = max(depth, level)
        else:
            if level == 30:
                raise ArithmeticError("Cell did not separate from one")
            mid = (left + right) / 2
            cells.extend([(left, mid, level + 1), (mid, right, level + 1)])
    return count, depth


def certify_lower():
    rho, t = F(1, 8), F(1, 2**40)
    step, budget = 1 + t, (16 / t) ** 2
    costs = [
        F(x)
        for x in (
            "0.5853452",
            "0.09980536",
            "0.005307215",
            "0.00001500696",
            "0.00000000012033",
        )
    ]
    atoms = [(t, rho * (1 + costs[0]))]
    for j, cost in enumerate(costs[1:]):
        multiple = 2**j * step
        atoms.append((t * multiple, rho * cost * multiple**2))
    atoms.append((F(1, 2), 1 - sum(w for _, w in atoms)))
    law = FiniteGapLaw(atoms)
    core, cut = quantile_split(law, rho)
    assert cut == t
    p = Precision(bits=160, log_terms=64)
    q = evaluate_selection(law, core, rho=rho, budget=budget, precision=p)
    candidate = evaluate_selection(
        law, [1, 0, 0, 0, 0, 1], rho=rho, budget=budget, precision=p
    )
    assert 0 < candidate.upper and q.lower > LOWER * candidate.upper


if __name__ == "__main__":
    certify_lower()
    cells, depth = certify_upper()
    print(
        f"1.462554551279 < sup(Q/K) < 1.462554551280. {cells} certified cells, depth {depth}."
    )
