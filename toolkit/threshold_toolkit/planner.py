"""Planning calculator: how accurate can an estimate be at a given flip budget?

Everything here starts from a guess at the items' success probabilities.
It compares two ways to spend the flips:

- the simple plan: flip each of n fresh items m times and count majority
  successes. Its error has an exact formula, given the guess.
- the proven no-tuning estimator in estimator.py, simulated on the guess.
  Simulation is numerical evidence for that guess, not a guarantee.

The proven limits use only how close the items are to 50/50:

    difficulty(B) = omega(1/sqrt(B)),  omega(h) = average of min(1, h / |p - 1/2|).

For any method with average budget B, some way of placing these items on
either side of 50/50 forces root-mean-square error at least difficulty / 64
(Tier6/Full.lean, `minimax_lower_bound`). The no-tuning estimator has error
at most 512 * difficulty for every placement (BlindUpper/Full.lean).
"""

import math
import sys
from dataclasses import dataclass
from typing import Callable, List, Optional, Sequence, Tuple

import numpy as np
from scipy.special import betainc, betaln

from .estimator import R_LEVEL, budget_level, level_probability, threshold

FLOOR_FACTOR = 1 / 64
CEILING_FACTOR = 512


class Population:
    """A guess at the success probabilities of the items you will draw."""

    def describe(self) -> str:
        raise NotImplementedError

    def share_within(self, h: float) -> float:
        """Share of items with |p - 1/2| <= h."""
        raise NotImplementedError

    def modulus(self, h: float) -> float:
        """omega(h) = average of min(1, h / |p - 1/2|)."""
        raise NotImplementedError

    def true_fraction(self) -> float:
        """Share of items with p > 1/2."""
        raise NotImplementedError

    def sample(self, rng: np.random.Generator, size: int) -> np.ndarray:
        """Success probabilities of `size` freshly drawn items."""
        raise NotImplementedError

    def points(self) -> Tuple[np.ndarray, np.ndarray]:
        """Exact discrete support and weights; continuous laws must override majority_terms."""
        raise NotImplementedError

    def majority_terms(self, m: int) -> Tuple[float, float]:
        """Mean majority decision and misclassification probability for odd m."""
        rates, weights = self.points()
        wrong = binomial_tail(m, (m + 1) // 2, np.minimum(rates, 1 - rates))
        above = np.where(rates > 0.5, 1 - wrong, wrong)
        return float(weights @ above), float(weights @ wrong)


class GuessedRates(Population):
    """Items drawn at random, with replacement, from a list of success probabilities."""

    def __init__(self, rates: Sequence[float]):
        rates = np.asarray(rates, dtype=float)
        if rates.ndim != 1 or rates.size == 0:
            raise ValueError("give at least one success probability")
        if not np.all((rates >= 0) & (rates <= 1)):
            raise ValueError("success probabilities must lie between 0 and 1")
        if np.any(rates == 0.5):
            raise ValueError("rates of exactly 0.5 are outside the positive-gap theorem's scope")
        self.rates = rates.copy()
        self.rates.flags.writeable = False
        self.gaps = np.abs(rates - 0.5)

    def describe(self) -> str:
        return f"{self.rates.size:,} guessed items"

    def share_within(self, h: float) -> float:
        return float(np.mean(self.gaps <= h))

    def modulus(self, h: float) -> float:
        safe = np.where(self.gaps > 0, self.gaps, 1.0)
        return float(np.mean(np.where(self.gaps <= h, 1.0, h / safe)))

    def true_fraction(self) -> float:
        return float(np.mean(self.rates > 0.5))

    def sample(self, rng: np.random.Generator, size: int) -> np.ndarray:
        return rng.choice(self.rates, size=size)

    def points(self) -> Tuple[np.ndarray, np.ndarray]:
        rates, counts = np.unique(self.rates, return_counts=True)
        return rates, counts / counts.sum()


class EvenlySpread(Population):
    """Success probabilities spread evenly between 0 and 1."""

    def describe(self) -> str:
        return "items with success rates spread evenly from 0% to 100%"

    def share_within(self, h: float) -> float:
        return min(1.0, max(0.0, 2 * h))

    def modulus(self, h: float) -> float:
        if h <= 0:
            return 0.0
        if h >= 0.5:
            return 1.0
        return 2 * h * (1 + math.log(1 / (2 * h)))

    def true_fraction(self) -> float:
        return 0.5

    def sample(self, rng: np.random.Generator, size: int) -> np.ndarray:
        return rng.random(size)

    def majority_terms(self, m: int) -> Tuple[float, float]:
        # With a=(m+1)/2, integration by parts gives
        # 2 integral_0^(1/2) I_p(a,a) dp = C(2a,a)/2^(2a+1)
        # = 1/(2a Beta(a,1/2)). This avoids a grid missing the peak near 1/2.
        a = (m + 1) / 2
        wrong = 0.5 * math.exp(-math.log(a) - float(betaln(a, 0.5)))
        return 0.5, wrong


def _validate_target(target: float) -> None:
    if not math.isfinite(target) or not 0 < target <= 1:
        raise ValueError("target error must be finite and in (0, 1]")
    if target * target == 0:
        raise ValueError("target error is too small for floating-point planning")


def difficulty(population: Population, budget: float) -> float:
    if not math.isfinite(budget) or budget < 1:
        raise ValueError("budget must be finite and at least 1 flip")
    if population.share_within(0) != 0:
        raise ValueError("the proven limits require zero mass at rate 0.5")
    return population.modulus(1 / math.sqrt(budget))


def floor_budget(population: Population, target: float) -> float:
    """Invert the proven floor numerically; inf means beyond float range, not impossible."""
    _validate_target(target)
    def floor(budget: float) -> float:
        return FLOOR_FACTOR * difficulty(population, budget)

    if floor(1) <= target:
        return 1.0
    high = 1.0
    while floor(high) > target:
        if high == sys.float_info.max:
            return math.inf
        high = min(sys.float_info.max, high * 1024)
    low = 1.0
    for _ in range(200):
        mid = math.exp((math.log(low) + math.log(high)) / 2)
        if floor(mid) <= target:
            high = mid
        else:
            low = mid
    return high


def binomial_tail(m: int, k: int, p: np.ndarray) -> np.ndarray:
    """P(Binomial(m, p) >= k) for 1 <= k <= m, via the regularized incomplete beta."""
    p = np.asarray(p, dtype=float)
    if not isinstance(m, int) or not isinstance(k, int) or not 1 <= k <= m:
        raise ValueError("binomial counts must be integers with 1 <= k <= m")
    if not np.all((0 <= p) & (p <= 1)):
        raise ValueError("binomial probabilities must be in [0, 1]")
    return betainc(k, m - k + 1, p)


@dataclass(frozen=True)
class MajorityPlan:
    """Flip each of `items` fresh items `flips_per_item` times; count majority successes."""
    items: int
    flips_per_item: int
    error_on_guess: float
    """Analytic root-mean-square error on the guessed law, evaluated in floating point."""
    worst_case_error: float
    """Bound on the error for every way items this close to 50/50 could fall either side."""

    @property
    def flips(self) -> int:
        return self.items * self.flips_per_item


def _odd_flip_counts(limit: float) -> List[int]:
    if not math.isfinite(limit) or limit < 1:
        raise ValueError("flip-count search limit must be finite and at least 1")
    counts, x = [], 1.0
    while math.isfinite(x):
        m = 2 * int(round(x) // 2) + 1
        if m > limit:
            return counts
        if not counts or m > counts[-1]:
            counts.append(m)
        x *= 1.25
    return counts


def _majority_terms(population: Population, m: int) -> Tuple[float, float]:
    """(share called above 50/50, average chance an item is called on the wrong side)."""
    return population.majority_terms(m)


def _majority_plan(population: Population, m: int, items: int) -> MajorityPlan:
    above, wrong = _majority_terms(population, m)
    truth = population.true_fraction()
    # Indicators are independent Bernoulli(above); bias is at most the mean
    # misclassification chance, whichever side each item is on.
    on_guess = math.sqrt((above - truth) ** 2 + above * (1 - above) / items)
    worst = math.sqrt(wrong ** 2 + 1 / (4 * items))
    return MajorityPlan(items, m, on_guess, worst)


def majority_plan_for_budget(population: Population, budget: float) -> MajorityPlan:
    """Best bound on the 1.25x grid of odd flip counts, not a global optimum."""
    if not math.isfinite(budget) or budget < 1:
        raise ValueError("budget must be finite and at least 1 flip")
    best = None
    for m in _odd_flip_counts(budget):
        items = int(budget // m)
        if best is not None and math.sqrt(1 / (4 * items)) >= best.worst_case_error:
            break  # the sampling term alone rules out every larger m
        plan = _majority_plan(population, m, items)
        if best is None or plan.worst_case_error < best.worst_case_error:
            best = plan
    return best


def majority_plan_for_target(population: Population, target: float,
                             max_flips_per_item: float = 2 ** 24) -> Optional[MajorityPlan]:
    """Cheapest qualifying plan on the bounded 1.25x grid, or None if not found."""
    _validate_target(target)
    best = None
    for m in _odd_flip_counts(max_flips_per_item):
        if best is not None and m / (4 * target ** 2) >= best.flips:
            break  # every later plan needs at least this many flips
        _, wrong = _majority_terms(population, m)
        if wrong >= target:
            continue
        remainder = (target - wrong) * (target + wrong)
        if remainder == 0:
            continue
        count = 1 / (4 * remainder)
        if not math.isfinite(count):
            raise ValueError("required item count exceeds floating-point planning range")
        plan = _majority_plan(population, m, max(1, math.ceil(count)))
        while plan.worst_case_error > target:  # floating-point rounding only
            plan = _majority_plan(population, m, plan.items + 1)
        if best is None or plan.flips < best.flips:
            best = plan
    return best


def _forced_stop_margins(level: int) -> np.ndarray:
    """Margins at prefixes 1, 2, ..., 2^level; -1 forces the stop at the cap."""
    cap = 2 ** level
    return np.array([threshold(2 ** k, cap) for k in range(level)] + [-1.0])


def _block_sizes(level: int) -> np.ndarray:
    """Flips needed to grow the prefix 0 -> 1 -> 2 -> 4 -> ... -> 2^level."""
    return np.array([1] + [2 ** (k - 1) for k in range(1, level + 1)], dtype=np.int64)


def score_blocks(counts: np.ndarray, level: int) -> Tuple[np.ndarray, np.ndarray]:
    """Vectorized `coupled_call`: rows of block success counts -> (values, flips).

    Simulated flips are free, so every block is drawn up front; only the
    flips before the finer classifier stops are charged.
    """
    rows = np.arange(counts.shape[0])
    successes = np.cumsum(counts, axis=1)
    prefix = 2 ** np.arange(level + 1)
    means = successes / prefix
    dev = np.abs(means - 0.5)
    fine_stop = np.argmax(dev > _forced_stop_margins(level), axis=1)
    fine = (means[rows, fine_stop] > 0.5).astype(float)
    if level == 0:
        coarse = 0.0
    else:
        coarse_stop = np.argmax(dev[:, :level] > _forced_stop_margins(level - 1), axis=1)
        coarse = (means[rows, coarse_stop] > 0.5).astype(float)
    return (fine - coarse) / level_probability(level), prefix[fine_stop]


def _calls(population: Population, level_cap: int, count: int,
           rng: np.random.Generator) -> Tuple[np.ndarray, np.ndarray]:
    """`count` independent estimator calls on fresh simulated items."""
    levels = rng.geometric(1 - R_LEVEL, size=count) - 1
    values = np.zeros(count)
    flips = np.ones(count, dtype=np.int64)  # one unused flip above the cap
    for level in np.unique(levels[levels <= level_cap]):
        level = int(level)
        idx = np.flatnonzero(levels == level)
        rates = population.sample(rng, idx.size)
        counts = rng.binomial(_block_sizes(level)[None, :], rates[:, None])
        values[idx], flips[idx] = score_blocks(counts, level)
    return values, flips


def _simulate_run(population: Population, level_cap: int,
                  rng: np.random.Generator) -> Tuple[float, int, int]:
    """One run of `estimate_fraction`, with pilots simulated in chunks."""
    cap = 2 ** level_cap
    production = 1
    flips = 0
    items = 0
    for _ in range(2):
        chunk = 64
        while True:
            _, costs = _calls(population, level_cap, chunk, rng)
            marks = rng.random(chunk) < costs / cap
            if marks.any():
                first = int(np.argmax(marks))
                flips += int(costs[:first + 1].sum())
                items += first + 1
                production += first
                break
            flips += int(costs.sum())
            items += chunk
            production += chunk
            chunk *= 2
    values, costs = _calls(population, level_cap, production, rng)
    return float(values.mean()), flips + int(costs.sum()), items + production


@dataclass(frozen=True)
class Simulation:
    budget: float
    runs: int
    truth: float
    rms_error: float
    """Root-mean-square error of the clipped estimates."""
    rms_error_se: float
    """Rough standard error of `rms_error` from the finite number of runs."""
    raw_rms_error: float
    bias: float
    mean_flips: float
    flips_p90: float
    flips_p99: float
    mean_items: float


def simulate(population: Population, budget: float, runs: int = 200,
             seed: Optional[int] = None,
             rng: Optional[np.random.Generator] = None) -> Simulation:
    """Run the estimator `runs` times on simulated items drawn from the guess."""
    if not isinstance(runs, int) or runs < 2:
        raise ValueError("use at least 2 runs")
    if rng is None:
        rng = np.random.default_rng(seed)
    level_cap = budget_level(budget)
    results = np.array([_simulate_run(population, level_cap, rng) for _ in range(runs)])
    raw, flips, items = results[:, 0], results[:, 1], results[:, 2]
    truth = population.true_fraction()
    clipped = np.clip(raw, 0.0, 1.0)
    squared = (clipped - truth) ** 2
    rms = math.sqrt(squared.mean())
    se = float(squared.std(ddof=1) / math.sqrt(runs) / (2 * rms)) if rms > 0 else 0.0
    return Simulation(
        budget=budget, runs=runs, truth=truth, rms_error=rms, rms_error_se=se,
        raw_rms_error=math.sqrt(np.mean((raw - truth) ** 2)),
        bias=float(clipped.mean() - truth), mean_flips=float(flips.mean()),
        flips_p90=float(np.quantile(flips, 0.9)), flips_p99=float(np.quantile(flips, 0.99)),
        mean_items=float(items.mean()))


@dataclass(frozen=True)
class BudgetPlan:
    budget: float
    resolution: float
    """1/sqrt(budget), the gap scale used in the modulus; not an error probability."""
    share_unresolved: float
    majority: MajorityPlan
    simulation: Simulation
    """The proven no-tuning estimator, simulated on the guess."""
    difficulty: float
    proven_floor: float
    proven_ceiling: float
    quadruple_ratio: float
    """difficulty at 4x the budget divided by difficulty now (0.5 is the best case)."""


def plan_budget(population: Population, budget: float, runs: int = 200,
                seed: Optional[int] = 0) -> BudgetPlan:
    budget_level(budget)
    h = 1 / math.sqrt(budget)
    score = population.modulus(h)
    return BudgetPlan(
        budget=budget, resolution=h, share_unresolved=population.share_within(h),
        majority=majority_plan_for_budget(population, budget),
        simulation=simulate(population, budget, runs, seed),
        difficulty=score, proven_floor=FLOOR_FACTOR * score,
        proven_ceiling=CEILING_FACTOR * score,
        quadruple_ratio=population.modulus(h / 2) / score if score > 0 else 0.0)


# The proven estimator's search stops once it would need this many times the
# simple plan's flips.
SEARCH_FACTOR = 64


@dataclass(frozen=True)
class TargetPlan:
    target: float
    majority: Optional[MajorityPlan]
    """Cheapest qualifying plan found on the bounded grid, or None."""
    trials: List[Simulation]
    recommended: Optional[Simulation]
    """First simulated budget at which the proven estimator meets the target, or None."""
    search_limit: float
    floor_budget: float


def plan_target(population: Population, target: float, runs: int = 200,
                seed: Optional[int] = 0, max_budget: float = 4 * 2 ** 22,
                progress: Optional[Callable[[Simulation], None]] = None,
                planned: Optional[Callable[[Optional[MajorityPlan]], None]] = None) -> TargetPlan:
    """Find the flips needed for typical error `target`, for both methods.

    The proven estimator is simulated at doubling budgets 4, 8, 16, ...: it
    only changes at these budgets, since every budget from 4N up to just
    below 8N runs the same algorithm. The search stops at `max_budget` or at
    SEARCH_FACTOR times the simple plan's flips. `progress` sees each trial.
    """
    _validate_target(target)
    budget_level(max_budget)
    if not isinstance(runs, int) or runs < 2:
        raise ValueError("use at least 2 runs")
    majority = majority_plan_for_target(population, target)
    if planned is not None:
        planned(majority)
    limit = max_budget if majority is None else min(max_budget, SEARCH_FACTOR * majority.flips)
    rng = np.random.default_rng(seed)
    trials = []
    recommended = None
    level = 0
    while recommended is None and 4 * 2 ** level <= limit:
        trial = simulate(population, 4 * 2 ** level, runs, rng=rng)
        trials.append(trial)
        if progress is not None:
            progress(trial)
        if trial.rms_error <= target:
            recommended = trial
        level += 1
    return TargetPlan(target, majority, trials, recommended, limit,
                      floor_budget(population, target))
