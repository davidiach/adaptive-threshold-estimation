"""The distribution-blind estimator, ready to run on real items.

This follows the algorithm whose guarantee is machine-checked in
lean/ThresholdHC/BlindUpper/Full.lean (`distribution_blind_upper`):
capped dyadic classifiers, one random geometric level per call, and
two-success cost calibration. It needs only the flip budget. It never
needs to know how close the items are to 50/50.

For iid populations with nonzero gaps almost surely, the checked theorem gives expected flips at most the
budget and root-mean-square error at most 512 * omega(1/sqrt(budget)) for
the raw output; see planner.py for omega. Clipping to [0, 1] can only reduce
the error. The budget is an average: a single run can use more.
"""

import math
import random
from dataclasses import dataclass
from typing import Callable, Optional, Tuple

# Level law P(J = l) = (1 - r) r^l with r = 1/sqrt(2) (paper eq. p-level).
R_LEVEL = 2 ** -0.5


def level_probability(level: int) -> float:
    return (1 - R_LEVEL) * R_LEVEL ** level


def threshold(n: int, cap: int) -> float:
    """Early-stop margin at prefix length n for a classifier with cap N."""
    return math.sqrt((1 + math.log(cap / n)) / n)


def budget_level(budget: float) -> int:
    """Largest L with 4 * 2**L <= budget, as in BlindUpper/BudgetChoice.lean."""
    if not math.isfinite(budget) or budget < 4:
        raise ValueError("budget must be finite and at least 4 flips")
    level = 0
    while 4 * 2 ** (level + 1) <= budget:
        level += 1
    return level


def sample_level(rng: random.Random) -> int:
    """Draw J with P(J >= l) = r^l."""
    return int(math.floor(math.log1p(-rng.random()) / math.log(R_LEVEL)))


def block_flipper(flip: Callable, batched: bool) -> Callable[[int], int]:
    """Turn a user's flip function into one returning successes in k flips, with checks."""
    def checked(got, k: int) -> int:
        try:
            count = int(got)
        except (TypeError, ValueError, OverflowError):
            count = -1
        if count != got or not 0 <= count <= k:
            raise ValueError(f"an item returned {got!r} successes for {k} flips")
        return count

    if batched:
        return lambda k: checked(flip(k), k)
    return lambda k: sum(checked(flip(), 1) for _ in range(k))


def coupled_call(flips: Callable[[int], int], level: int) -> Tuple[float, int]:
    """Run the cap-2^level classifier and the cap-2^(level-1) one on one item.

    `flips(k)` returns the number of successes in the item's next k flips.
    Both classifiers look only at prefixes of length 1, 2, 4, ..., so flips
    are requested in those blocks. The coarser classifier always stops no
    later than the finer one, so the call uses the finer one's flips.
    Returns (Z_level - Z_(level-1)) / p_level, with Z_(-1) = 0, and the flips used.
    """
    cap = 2 ** level
    coarse_cap = cap // 2
    coarse = 0 if level == 0 else None
    successes = 0
    n = 0
    while True:
        block = 1 if n == 0 else n
        successes += flips(block)
        n += block
        mean = successes / n
        dev = abs(mean - 0.5)
        if coarse is None and (n >= coarse_cap or dev > threshold(n, coarse_cap)):
            coarse = int(mean > 0.5)
        if n >= cap or dev > threshold(n, cap):
            fine = int(mean > 0.5)
            return (fine - coarse) / level_probability(level), n


def two_success_average(run_once: Callable[[], Tuple[float, float]], cap: float,
                        rng: random.Random) -> Tuple[float, float, int, int]:
    """Average fresh runs of a random-cost procedure without knowing its mean cost.

    `run_once()` returns a finite (value, cost) with 0 < cost <= cap.
    Calls must be iid and independent of `rng`. Two pilot streams run until each marks a run, marking with
    probability cost / cap; one more than the number of unmarked pilots sets
    how many fresh production runs to average. Pilot values are discarded.
    The average is unbiased, has variance Var(value) * c / cap, and expected
    total cost exactly 4 * cap - c, where c is the mean cost (paper Lemma
    "Two-success cost calibration").

    Returns (average, total cost, production runs, pilot runs).
    """
    if not math.isfinite(cap) or cap <= 0:
        raise ValueError("cap must be finite and positive")

    def checked_run() -> Tuple[float, float]:
        value, cost = run_once()
        if not math.isfinite(cost) or not 0 < cost <= cap:
            raise ValueError(f"run cost {cost!r} is outside (0, {cap}]")
        if not math.isfinite(value):
            raise ValueError("run value must be finite")
        return value, cost

    production = 1
    pilots = 0
    total_cost = 0
    for _ in range(2):
        while True:
            _, cost = checked_run()
            pilots += 1
            total_cost += cost
            if rng.random() < cost / cap:
                break
            production += 1
    total = 0.0
    for _ in range(production):
        value, cost = checked_run()
        total += value
        total_cost += cost
    return total / production, total_cost, production, pilots


@dataclass(frozen=True)
class Estimate:
    estimate: float
    """Estimated share of items above 50/50, clipped to [0, 1]."""
    raw_estimate: float
    """Unclipped output; it can fall outside [0, 1]."""
    flips: int
    """Flips actually used in this run."""
    items: int
    """Fresh items drawn in this run."""
    budget: float
    cap: int
    """Most flips any single item can receive."""


def majority_vote_estimate(new_item: Callable[[], Callable], items: int,
                           flips_per_item: int, *, batched: bool = False) -> float:
    """The simple plan: flip each fresh item a fixed odd number of times.

    Returns the share of items with more successes than failures. Use
    `planner.majority_plan_for_budget` or `majority_plan_for_target` to pick
    `items` and `flips_per_item` from a guess at the success rates; that
    choice is where this plan's accuracy comes from.
    """
    if not isinstance(items, int) or items < 1:
        raise ValueError("use at least one item")
    if not isinstance(flips_per_item, int) or flips_per_item < 1 or flips_per_item % 2 == 0:
        raise ValueError("flips_per_item must be odd, so every item has a majority")
    above = sum(2 * block_flipper(new_item(), batched)(flips_per_item) > flips_per_item
                for _ in range(items))
    return above / items


def estimate_fraction(new_item: Callable[[], Callable], budget: float, *,
                      batched: bool = False, seed: Optional[int] = None,
                      rng: Optional[random.Random] = None) -> Estimate:
    """Estimate the share of items whose success probability is above 1/2.

    `new_item()` draws a fresh random item from the population and returns a
    function that flips it. With `batched=False` that function takes no
    arguments and returns True/False (or 1/0) for one flip. With
    `batched=True` it takes k and returns the number of successes in k
    flips, which lets you run the flips of one item in parallel.

    `budget` is the average number of flips to spend. Items must be drawn
    independently, and flips of one item must be independent given the item.
    `seed` or `rng` fixes the estimator's own randomness, not the items'.
    """
    if rng is None:
        rng = random.Random(seed)
    level_cap = budget_level(budget)
    cap = 2 ** level_cap
    items = 0

    def item_flips() -> Callable[[int], int]:
        nonlocal items
        items += 1
        return block_flipper(new_item(), batched)

    def one_call() -> Tuple[float, int]:
        level = sample_level(rng)
        if level > level_cap:
            # The checked algorithm takes one unused flip here (BlindUpper/PaddedCall.lean).
            item_flips()(1)
            return 0.0, 1
        return coupled_call(item_flips(), level)

    raw, flips, _, _ = two_success_average(one_call, cap, rng)
    return Estimate(min(1.0, max(0.0, raw)), raw, int(flips), items, budget, cap)
