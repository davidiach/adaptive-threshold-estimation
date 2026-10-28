"""Command-line planning calculator.

    python -m threshold_toolkit --rates 0.9,0.6,0.52,0.3 --budget 20000
    python -m threshold_toolkit --rates-file rates.txt --target-error 0.03
    python -m threshold_toolkit --evenly-spread --budget 100000
"""

import argparse
import math
import re
import sys
from typing import List, Optional

from .planner import (FLOOR_FACTOR, SEARCH_FACTOR, EvenlySpread, GuessedRates, MajorityPlan,
                      Population, Simulation, majority_plan_for_target, plan_budget, plan_target)


def read_rates(text: str) -> List[float]:
    numbers = []
    for line in text.splitlines():
        line = line.split("#", 1)[0]
        numbers += [float(token) for token in re.split(r"[\s,;]+", line) if token]
    return numbers


def _flips(x: float) -> str:
    return f"{x:,.0f}"


def _error(x: float) -> str:
    return f"{x:.3g} (about {100 * x:.2g} percentage points)"


def _usage(sim: Simulation) -> str:
    return (f"{_flips(sim.mean_flips)} on average; 90% of runs used at most "
            f"{_flips(sim.flips_p90)}, 99% at most {_flips(sim.flips_p99)}")


def _simple_plan(plan: MajorityPlan, total: bool = False) -> str:
    flips = f" ({_flips(plan.flips)} flips)" if total else ""
    return (f"{plan.items:,} items x {plan.flips_per_item:,} flips each{flips}, "
            "then a majority vote per item")


def _budget_report(population: Population, budget: float, runs: int, seed: int) -> str:
    plan = plan_budget(population, budget, runs, seed)
    simple, sim = plan.majority, plan.simulation
    lines = [f"At an average budget of {_flips(budget)} flips:", "",
             f"  Hard to call: {100 * plan.share_unresolved:.3g}% of items are within "
             f"{100 * plan.resolution:.3g} points of 50/50."]
    if plan.share_unresolved > 0:
        lines.append("    Even the whole budget spent on one of them would leave about a 2% or larger\n"
                     "    chance of placing it on the wrong side.")
    lines += [
        "",
        f"  Simple plan: {_simple_plan(simple)}",
        f"    typical error on your guess: {_error(simple.error_on_guess)}",
        f"    at most {simple.worst_case_error:.3g} however these items fall on either side of 50/50",
        "",
        f"  Proven no-tuning method, simulated {runs} times on your guess:",
        f"    typical error: {_error(sim.rms_error)}, give or take {sim.rms_error_se:.2g}",
        f"    flips used: {_usage(sim)}",
        ""]
    if simple.error_on_guess <= sim.rms_error:
        ratio = sim.rms_error / simple.error_on_guess if simple.error_on_guess > 0 else math.inf
        lines.append(f"  On your guess, the simple plan's typical error is {ratio:.2g}x smaller.")
    else:
        lines.append(f"  On your guess, the proven method's typical error is "
                     f"{simple.error_on_guess / sim.rms_error:.2g}x smaller.")
    ceiling = (f"{plan.proven_ceiling:.3g} (difficulty x 512)"
               + (", too loose to be useful here" if plan.proven_ceiling >= 1 else ""))
    lines += [
        "",
        "  Proven limits, for every way items this close to 50/50 could fall:",
        f"    difficulty score: {plan.difficulty:.3g}",
        f"    no method can promise a typical error below {plan.proven_floor:.3g} (difficulty / 64)",
        f"    the no-tuning method is proven to stay within {ceiling}",
        "",
        f"  Returns on more flips: 4x the budget would cut the difficulty score to "
        f"{100 * plan.quadruple_ratio:.0f}% of today's.",
        "    (50% is the best case, when every item is far from 50/50.)"]
    return "\n".join(lines)


def _target_report(population: Population, target: float, runs: int, seed: int,
                   max_budget: float) -> None:
    print(f"Target typical error: {_error(target)}\n")
    simple = majority_plan_for_target(population, target)
    if simple is None:
        print("Simple plan: no number of flips per item reaches this target.\n")
    else:
        print(f"Simple plan: {_simple_plan(simple, total=True)}\n"
              "  meets the target however these items fall on either side of 50/50\n"
              f"  (at most {simple.worst_case_error:.3g}; {simple.error_on_guess:.3g} on your guess)\n")
    print(f"Proven no-tuning method, simulated at doubling budgets ({runs} runs each):")
    print(f"  {'budget':>12}  {'typical error':>13}  {'avg flips':>11}  {'99% of runs at most':>19}")

    def row(sim: Simulation) -> None:
        print(f"  {_flips(sim.budget):>12}  {sim.rms_error:>13.3g}  "
              f"{_flips(sim.mean_flips):>11}  {_flips(sim.flips_p99):>19}", flush=True)

    plan = plan_target(population, target, runs, seed, max_budget, progress=row)
    found = plan.recommended
    if found is not None:
        versus = f", {found.budget / simple.flips:.2g}x the simple plan" if simple else ""
        print(f"  -> meets the target at a budget of {_flips(found.budget)} flips{versus}.")
    elif simple is not None and plan.search_limit < max_budget:
        print(f"  -> did not meet the target within {SEARCH_FACTOR}x the simple plan's flips.")
    else:
        print(f"  -> did not meet the target within {_flips(plan.search_limit)} flips; "
              "raise --max-budget to search further.")
    print()
    if math.isinf(plan.floor_budget):
        print("Proven floor: no budget lets any method promise this accuracy for "
              "populations this close to 50/50.")
    elif target >= FLOOR_FACTOR:
        print(f"Proven floor: too loose to rule out any budget for targets above {FLOOR_FACTOR:.3g}.")
    else:
        print(f"Proven floor: below {_flips(plan.floor_budget)} flips, no method can promise this "
              "accuracy for every way items this close to 50/50 could fall.")


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        prog="python -m threshold_toolkit",
        description="Plan a flip budget for estimating the share of items above 50/50.")
    guess = parser.add_mutually_exclusive_group(required=True)
    guess.add_argument("--rates", help="guessed success probabilities, comma separated")
    guess.add_argument("--rates-file", help="file of guessed success probabilities")
    guess.add_argument("--evenly-spread", action="store_true",
                       help="assume success rates are spread evenly from 0 to 1")
    goal = parser.add_mutually_exclusive_group(required=True)
    goal.add_argument("--budget", type=float, help="average number of flips you can spend")
    goal.add_argument("--target-error", type=float, help="typical error you need, e.g. 0.03")
    parser.add_argument("--runs", type=int, default=200, help="simulated runs (default 200)")
    parser.add_argument("--seed", type=int, default=0, help="simulation seed (default 0)")
    parser.add_argument("--max-budget", type=float, default=4 * 2 ** 22,
                        help="largest budget to simulate with --target-error")
    args = parser.parse_args(argv)

    try:
        if args.evenly_spread:
            population: Population = EvenlySpread()
        elif args.rates is not None:
            population = GuessedRates(read_rates(args.rates))
        else:
            with open(args.rates_file) as f:
                population = GuessedRates(read_rates(f.read()))
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    print(f"Your guess: {population.describe()}, "
          f"{100 * population.true_fraction():.3g}% of them above 50/50.\n")
    tied = population.share_within(0)
    if tied > 0:
        print(f"Note: {100 * tied:.3g}% of your guessed items sit exactly at 50/50. No amount of\n"
              "flipping settles which side those are on, so errors below about half that share\n"
              "are out of reach. If they are only roughly even, guess 0.49 or 0.51 instead.\n")
    try:
        if args.budget is not None:
            print(_budget_report(population, args.budget, args.runs, args.seed))
        else:
            _target_report(population, args.target_error, args.runs, args.seed, args.max_budget)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
