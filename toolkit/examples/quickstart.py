"""Plan a budget, then run both estimators on simulated items.

Here each item is a question with a hidden chance that a model answers it
correctly. In real use, `new_question` would pick a question at random and
return a function that asks the model once and grades the answer.

    python toolkit/examples/quickstart.py
"""

import math
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from threshold_toolkit import (GuessedRates, estimate_fraction, majority_plan_for_target,
                               majority_vote_estimate)

world = random.Random(7)
hidden_rates = [world.betavariate(2, 1.5) for _ in range(500)]
truth = sum(rate > 0.5 for rate in hidden_rates) / len(hidden_rates)


def new_question():
    rate = world.choice(hidden_rates)
    return lambda: world.random() < rate  # one graded attempt


# 1. Plan from a rough guess: here, each rate rounded to the middle of its 5-point band.
guess = GuessedRates([0.05 * math.floor(rate / 0.05) + 0.025 for rate in hidden_rates])
plan = majority_plan_for_target(guess, target=0.03)
print(f"Plan: {plan.items} questions x {plan.flips_per_item} attempts = {plan.flips:,} attempts,")
print(f"      typical error at most {plan.worst_case_error:.3f} if the guess is right.\n")

# 2. Run the simple plan and the proven no-tuning method on the same budget.
simple = majority_vote_estimate(new_question, plan.items, plan.flips_per_item)
proven = estimate_fraction(new_question, plan.flips, seed=1)
print(f"True share answered correctly more often than not: {truth:.3f}")
print(f"Simple plan estimate:  {simple:.3f}  ({plan.flips:,} attempts)")
print(f"Proven method estimate: {proven.estimate:.3f}  ({proven.flips:,} attempts this run)")
