"""Replay the two-reference cap bound on finite laws with exact Bellman arithmetic."""

from fractions import Fraction as F
from itertools import product
from pathlib import Path
from runpy import run_path


def main():
    audit_path = Path(__file__).resolve().parents[1] / "paper/rare-event/audit/original/finite_program_adversarial_audit.py"
    audit = run_path(str(audit_path))
    coefficients = audit["coefficients"]
    ratio = audit["exact_ratio"]
    priors = [(F(0), F(0)), (F(1, 2), F(0)), (F(0), F(1, 2)), (F(1, 4), F(1, 4))]
    mu = [(F(1, 16), F(1, 2)), (F(1, 2), F(1, 2))]
    checked = 0
    singular_latent = 0
    for low, high, variance, work in product(priors, repeat=4):
        if audit["expectation"](mu, high) <= audit["expectation"](mu, low):
            continue
        mid = [(a + b) / 2 for a, b in zip(low, high)]
        for cap in (1, 2, 4, 7):
            rewards, costs, original_genie = coefficients(mu, (low, high, variance, work), cap)
            ordinary = ratio(rewards, costs, cap)
            if ordinary is None:
                raise ArithmeticError("fixture must have finite ordinary information")
            if original_genie[cap, 0] is None:
                singular_latent += 1
            for e in (F(1, 4), F(1, 2), F(3, 4)):
                v = [(1 - e) * a + e * b for a, b in zip(variance, mid)]
                w = [(1 - e) * a + e * b for a, b in zip(work, mid)]
                r, c, g = coefficients(mu, (low, high, v, w), cap)
                genie = ratio(r, c, cap, g)
                bound = max(ordinary / (1 - e)**2, 4 / (e**2 * cap))
                if genie is None or genie > bound:
                    raise ArithmeticError((low, high, variance, work, cap, e, genie, bound))
                k = 1 / (1 - e)
                budget = e**2 * (k**2 - 1) * cap
                if 4 + budget * genie > k**2 * (4 + budget * ordinary):
                    raise ArithmeticError("dual denominator bound failed")
                checked += 1
    if not singular_latent:
        raise ArithmeticError("fixtures did not exercise a singular variance reference")
    print(f"Verified {checked} exact comparisons, including {singular_latent} singular quartet/cap inputs.")


if __name__ == "__main__":
    main()
