"""Exact rational checks supporting BIAS_AUDIT.md, not a Lean proof.

No randomness or held-out data. Uses an all-tails event; it does not enumerate
the enormous cap or change the frozen evaluator.
"""
from fractions import Fraction as F
import json
from math import factorial
from pathlib import Path

q = F(7, 10)
exp_lower = sum(q**k / factorial(k) for k in range(5))
assert exp_lower > 2  # exp(7/10) > 2, hence log 2 < 7/10.
n, L = 128, 97
k1, k2, d = F(1, 4), F(1, 2), F(1, 10)
threshold_numerator_upper = k1 + k2 * (L - 7) * q
assert threshold_numerator_upper < n / F(4)
event_probability = (F(1, 2) - d)**n
bias_bound = 1 / ((2**L) * d**2)**2
assert event_probability > bias_bound
report = {
    "status": "exact rational checks of paper counterexample",
    "config": {"k1": float(k1), "k2": float(k2)},
    "positive_sign": True, "d": str(d), "cap": f"2^{L}", "all_tails_prefix": n,
    "exp_point7_series_lower": str(exp_lower),
    "threshold_squared_upper": str(threshold_numerator_upper / n),
    "error_probability_lower_bound": str(event_probability),
    "claimed_bias_bound": str(bias_bound),
    "exact_ratio": str(event_probability / bias_bound),
    "ratio_approx": float(event_probability / bias_bound),
    "all_checks_passed": True,
}
root = Path(__file__).resolve().parents[2]
(root / "results/constants_bias_counterexample.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
