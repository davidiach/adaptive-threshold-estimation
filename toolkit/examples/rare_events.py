"""Evaluate a known weighted finite law; no coin flips or simulations are run.

    python toolkit/examples/rare_events.py
"""

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from threshold_toolkit import FiniteGapLaw, RareEventProfile


law = FiniteGapLaw(gaps=[0.01, 0.1, 0.4], weights=[1, 2, 7])
profile = RareEventProfile(law, rho=0.05)

print("Known gap law:", list(zip(law.gaps, law.weights)))
print("Quantile-tail weights:", profile.tail_weights)
print("Core weights:", profile.core_weights)
print("\n      Budget          Q(B)       Lower K       Upper K")
for budget in (10_000, 100_000, 1_000_000):
    result = profile.evaluate(budget)
    print(f"{budget:12,d}  {result.value:12.6g}  "
          f"{result.selection_lower:12.6g}  {result.selection_upper:12.6g}")

inverse = profile.budget_for_rate(0.01)
print(f"\nQ reaches 0.01 at approximately B = {inverse.budget:,.3f}.")
print("These are floating-point values of a paper-proof rate functional.")
print("They are not an achieved RMS error or a certified estimator budget.")
