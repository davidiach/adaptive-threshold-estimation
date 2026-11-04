"""Observable finite-level rare-event estimator for a known magnitude law (v6 Appendix D).

The budget is a uniform expected flip count. Each fresh item supplies successive
conditionally independent flips on that same item. Oracle integrals and private
randomness are independent of the sampled items. The plan reports its own
finite-level MSE bound; Python execution itself is not a checked Lean program.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from random import Random
from typing import Callable

from .estimator import block_flipper
from .known_law_oracle import KnownGapOracle
from .rare_event_functional import (
    Interval,
    Precision,
    Rational,
    _log_unit_interval,
    _parameters,
    cost_entropy,
    sqrt_interval,
)


@dataclass(frozen=True)
class Level:
    cap: int
    error: F
    mark_work: F
    mean_count: F


@dataclass(frozen=True)
class RarePlan:
    law: KnownGapOracle
    rho: F
    budget: F
    weights: tuple[tuple[int, F], ...]
    levels: tuple[Level, ...]
    mse_bound: F


def _bound(value: F, name: str) -> F:
    if not isinstance(value, (int, F)) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a nonnegative rational upper bound")
    return F(value)


def plan_known_rare(
    law: KnownGapOracle,
    *,
    rho: Rational,
    budget: Rational,
    precision: Precision = Precision(),
) -> RarePlan:
    """Plan the quantile-core classifier bank and independent telescoping marks.

    The plan may return the constant rho/2 when its squared-error certificate
    wins. A plan with nonconstant output schedules rational mean counts whose
    total certified expected work equals the supplied budget.
    """
    rho, budget = _parameters(rho, budget)
    constant = RarePlan(law, rho, budget, (), (), (rho / 2) ** 2)
    design = law.split(rho, budget, precision)
    z = min(rho, _bound(design.unresolved_mass, "unresolved mass"))
    # Leave one finer paper level available when a cap integral is enclosed.
    if 2048 * z > rho:
        return constant
    H = _bound(design.tail_inverse, "resolved tail inverse cost")
    costs = {}
    for j, bound in design.band_costs.items():
        if type(j) is not int or j < 0:
            raise ValueError("core band indices must be nonnegative integers")
        a = _bound(bound, "band inverse-square cost")
        if a:
            costs[j] = a
    total = sum(costs.values(), F(0))
    if total < 4 * (1 - rho):
        raise ValueError("core costs cannot cover the retained probability mass")
    weights = tuple((j, a / total) for j, a in sorted(costs.items()))
    # For pi_j = upper_a_j/total, this also bounds the true cross entropy
    # sum a_j(1+log(1/pi_j)). Zero-mass bands may receive positive weight.
    entropy = cost_entropy(costs.values(), precision).upper
    target = max(
        128 * z, rho / (16 * (1 + sqrt_interval(budget, precision.bits).upper))
    )
    caps, errors, work, allocation = [], [], [], []
    cap = 4
    delta = rho / 16
    previous = F(0)
    while True:
        while _bound(design.resolved_error(cap), "resolved error") > delta / 8:
            cap *= 4
        ordinary = _bound(design.tail_work(cap), "ordinary work")
        # Positive crossings use a certified upper null likelihood. Their time
        # is dominated by the exact bank with half the internal allowance.
        level_work = min(
            2 * cap,
            80 * (len(caps) + 2) * entropy
            + 4 * H * H / rho
            + 2 * ordinary
            + 2 * z * cap,
        )
        mark_work = previous + level_work
        caps.append(cap)
        errors.append(delta)
        work.append(mark_work)
        allocation.append(sqrt_interval(17 * delta / mark_work, precision.bits).upper)
        if delta / 16 < target:
            break
        previous, delta = level_work, delta / 16
    normalizer = sum(k * a for k, a in zip(work, allocation))
    levels = tuple(
        Level(m, e, k, budget * a / normalizer)
        for m, e, k, a in zip(caps, errors, work, allocation)
    )
    bound = errors[-1] ** 2 + sum(
        17 * level.error / level.mean_count for level in levels
    )
    if bound >= constant.mse_bound:
        return constant
    return RarePlan(law, rho, budget, weights, levels, bound)


@lru_cache(maxsize=16)
def _log_two(terms: int):
    return _log_unit_interval(F(2), terms)


def _ordinary_stop(heads: int, n: int, cap: int) -> bool:
    """Strict early crossing at a dyadic prefix n < cap, without a float tie."""
    excess = F((2 * heads - n) ** 2, 4 * n) - 1
    if excess <= 0:
        return False
    power = cap.bit_length() - n.bit_length()
    terms = 8
    while True:
        interval = _log_two(terms)
        if excess <= power * interval.lower:
            return False
        if excess > power * interval.upper:
            return True
        # power > 0 and log(2) is irrational, whereas excess is rational.
        terms *= 2


def _classify(
    plan: RarePlan, level: Level, draw: Callable[[int], int]
) -> tuple[int, int]:
    """Race the likelihood bank with the ordinary classifier on alternating flips."""
    refs = [(w, F(1, 2 ** (j + 2)), F(1, 2 ** (j + 3))) for j, w in plan.weights]
    negative = [F(1)] * len(refs)
    positive = [w for w, _, _ in refs]
    u = level.error / 4
    bank_heads = ordinary_heads = 0
    for n in range(1, level.cap + 1):
        bit = draw(1)
        bank_heads += bit
        ordinary_heads += draw(1)
        for j, (weight, minus, plus) in enumerate(refs):
            negative[j] *= 1 - 2 * minus if bit else 1 + 2 * minus
            if negative[j] * u * weight >= plan.rho:
                return 0, 2 * n
            positive[j] *= F(1, 2) + plus if bit else F(1, 2) - plus
        threshold = u * sum(positive)
        null = plan.law.null_prefix(bank_heads, n - bank_heads, threshold / 2)
        if (
            not isinstance(null, Interval)
            or null.lower < 0
            or null.upper > 1
            or null.width > threshold / 2
        ):
            raise ValueError(
                "null-prefix oracle failed its probability enclosure contract"
            )
        if null.upper <= threshold:
            return 1, 2 * n
        if n == level.cap or (
            n & (n - 1) == 0 and _ordinary_stop(ordinary_heads, n, level.cap)
        ):
            return int(2 * ordinary_heads > n), 2 * n
    raise AssertionError("terminal cap was not reached")


@dataclass(frozen=True)
class RareEstimate:
    value: F
    flips: int
    items: int


def estimate_known_rare(
    new_item: Callable[[], Callable], plan: RarePlan, *, rng: Random | None = None
) -> RareEstimate:
    """Execute on observable flips and project the telescoping estimate onto [0,rho].

    Independent randomized rounding of each replication count has its specified
    mean and variance at most that mean, which suffices for the Poisson-mark
    second-moment bound. Adjacent classifiers use fresh flips on the same item.
    """
    if not plan.levels:
        return RareEstimate(plan.rho / 2, 0, 0)
    if rng is None:
        rng = Random()
    value = F(0)
    flips = items = 0
    for index, level in enumerate(plan.levels):
        mean = level.mean_count
        count, rem = divmod(mean.numerator, mean.denominator)
        if rem and rng.randrange(mean.denominator) < rem:
            count += 1
        marks = 0
        for _ in range(count):
            draw = block_flipper(new_item(), False)
            fine, used = _classify(plan, level, draw)
            flips += used
            coarse = 0
            if index:
                coarse, used = _classify(plan, plan.levels[index - 1], draw)
                flips += used
            marks += fine - coarse
        items += count
        value += marks / mean
    return RareEstimate(min(plan.rho, max(F(0), value)), flips, items)
