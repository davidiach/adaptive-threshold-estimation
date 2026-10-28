"""Estimate the share of items whose success rate is above 50/50, and plan the budget.

- `plan_budget` and `plan_target` say how accurate a budget can be for a guess
  at the items' success rates. They compare a simple fixed plan (a set
  number of flips per item, then a majority vote) with the paper's proven
  no-tuning estimator, and give the proven limits.
- `majority_vote_estimate` runs the simple plan on real items.
- `estimate_fraction` runs the paper's distribution-blind estimator on real items.
- `two_success_average` is that estimator's cost calibration on its own, for
  any procedure with a random but bounded cost.
"""

from .estimator import Estimate, estimate_fraction, majority_vote_estimate, two_success_average
from .planner import (BudgetPlan, EvenlySpread, GuessedRates, MajorityPlan, Population,
                      Simulation, TargetPlan, floor_budget, majority_plan_for_budget,
                      majority_plan_for_target, plan_budget, plan_target, simulate)

__all__ = [
    "BudgetPlan", "Estimate", "EvenlySpread", "GuessedRates", "MajorityPlan", "Population",
    "Simulation", "TargetPlan", "estimate_fraction", "floor_budget",
    "majority_plan_for_budget", "majority_plan_for_target", "majority_vote_estimate",
    "plan_budget", "plan_target", "simulate", "two_success_average",
]
