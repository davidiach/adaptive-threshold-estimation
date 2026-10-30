"""Evaluate the finite-law rare-event rate functional, without subset search.

This implements the *deterministic* quantile formula in the finite-gap paper,
Section 1.2, and the strengthened comparison with the entropy-tail selection
functional in ``docs/RARE_EVENT_COMPUTATION.md``.  ``Q(B)`` is a rate functional, not the minimax risk or
the measured error of an implemented estimator.  The statistical comparison
is a paper proof; neither it nor this Python implementation is Lean-checked.

Inputs describe a known distribution of positive gaps, not observed signs.
Rarity is the global constraint integral(q dmu) <= rho, not q(d) <= rho at
each gap.  Budgets count expected physical observations.  Calculations use
floating point, not certified intervals.  Logarithmic costs keep tiny gaps
usable even when their inverse-square costs overflow an ordinary float.
"""

import bisect
import math
import sys
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, Optional, Tuple


# docs/RARE_EVENT_COMPUTATION.md, strengthened deterministic comparison.
# Keep the deterministic comparison distinct
# from the much looser constants in the statistical minimax theorem.
QUANTILE_SELECTION_FACTOR = 5 / 3


def _logadd(left: float, right: float) -> float:
    if left == -math.inf:
        return right
    if right == -math.inf:
        return left
    large, small = max(left, right), min(left, right)
    return large + math.log1p(math.exp(small - large))


def _logsum(values: Iterable[float]) -> float:
    values = tuple(values)
    if not values:
        return -math.inf
    largest = max(values)
    return largest + math.log(math.fsum(math.exp(value - largest) for value in values))


def _exp(value: float) -> float:
    """Expose overflow as infinity while retaining logarithmic diagnostics."""
    try:
        return math.exp(value)
    except OverflowError:
        return math.inf


def _positive_float(value, name: str) -> float:
    try:
        value = float(value)
    except (TypeError, ValueError, OverflowError) as error:
        raise ValueError(f"{name} must be finite and positive") from error
    if not math.isfinite(value) or value <= 0:
        raise ValueError(f"{name} must be finite and positive")
    return value


def _band_index(gap: float) -> int:
    """Index j of (2**(-j-2), 2**(-j-1)], including dyadic endpoints exactly."""
    mantissa, exponent = math.frexp(gap)
    return -exponent if mantissa == 0.5 else -exponent - 1


@dataclass(frozen=True, init=False)
class FiniteGapLaw:
    """A finite positive-gap law, sorted and normalized from supplied weights.

    Gaps must be finite and in (0, 1/2].  Weights must be finite and nonnegative;
    an omitted weight sequence gives equal weights.  Zero weights are removed
    and equal gaps are merged.  Weights need not sum to one: normalization is
    explicit and automatic.  Positive weights that would underflow during
    normalization are rejected rather than silently discarded.

    Construction costs O(n log n); the stored tuples cannot be mutated.
    """

    gaps: Tuple[float, ...]
    weights: Tuple[float, ...]

    def __init__(self, gaps: Iterable[float], weights: Optional[Iterable[float]] = None):
        try:
            gaps = tuple(float(gap) for gap in gaps)
            weights = (tuple(1.0 for _ in gaps) if weights is None
                       else tuple(float(weight) for weight in weights))
        except (TypeError, ValueError, OverflowError) as error:
            raise ValueError("gaps and weights must be finite numeric sequences") from error
        if not gaps or len(gaps) != len(weights):
            raise ValueError("give nonempty gaps and equally many weights")
        if any(not math.isfinite(gap) or not 0 < gap <= 0.5 for gap in gaps):
            raise ValueError("gaps must be finite and in (0, 1/2]")
        if any(not math.isfinite(weight) or weight < 0 for weight in weights):
            raise ValueError("weights must be finite and nonnegative")
        largest = max(weights)
        if largest == 0:
            raise ValueError("at least one weight must be positive")
        scaled = tuple(weight / largest for weight in weights)
        if any(weight > 0 and value == 0 for weight, value in zip(weights, scaled)):
            raise ValueError("positive weights underflow during normalization")
        total = math.fsum(scaled)
        normalized = tuple(value / total for value in scaled)
        if any(weight > 0 and value == 0 for weight, value in zip(weights, normalized)):
            raise ValueError("positive weights underflow during normalization")
        grouped = {}
        for gap, weight in zip(gaps, normalized):
            if weight:
                grouped.setdefault(gap, []).append(weight)
        ordered = tuple(sorted(grouped))
        object.__setattr__(self, "gaps", ordered)
        object.__setattr__(self, "weights", tuple(math.fsum(grouped[gap]) for gap in ordered))

    def profile(self, rho: float) -> "RareEventProfile":
        """Precompute the smallest-gap mass rho and the remaining core."""
        return RareEventProfile(self, rho)


@dataclass(frozen=True)
class EntropyBand:
    """One occupied canonical band of the remaining core.

    ``cost`` is sum(core_weight / gap**2), possibly infinity from float
    overflow.  ``log_cost`` remains finite for every accepted finite law.
    """

    index: int
    cost: float
    log_cost: float


@dataclass(frozen=True)
class RareEventEvaluation:
    """Floating-point values of Q and its two uncapped components.

    ``selection_lower = max(tail, 3 * value / 5) <= K <= selection_upper``
    combines two deterministic comparisons, subject to floating-point error;
    it is not a bound on minimax risk.
    ``entropy_term`` can be infinity when the uncapped term exceeds float
    range; ``value`` is still finite because Q is capped by rho.
    """

    budget: float
    resolution: float
    tail: float
    entropy_term: float
    value: float
    selection_lower: float
    selection_upper: float


@dataclass(frozen=True)
class RateBudget:
    """Numerical inversion of Q(B) <= target; this is not an estimator plan.

    ``status == 'saturated'`` means every positive budget meets the rate
    target; zero is the infimum, not an allowed positive-budget experiment.
    ``status == 'overflow'`` means the required budget exceeds float range;
    ``log_budget`` still describes its natural logarithm.  Infinity is a
    representation limit, not a statistical impossibility statement.
    """

    target: float
    budget: float
    log_budget: float
    status: str


@dataclass(frozen=True, init=False)
class RareEventProfile:
    """Precompute the quantile split and dyadic cost entropy for a known law.

    Exactly the smallest-gap mass rho is assigned to the tail, splitting a
    boundary atom when necessary.  The remaining mass is the core.  ``rho``
    must be finite and in (0, 1/4], the domain of the cited rare-event result.
    Fractions are used only for splitting the *stored float weights*, avoiding
    accumulation/cancellation errors at an almost-exact quantile boundary.

    The profile costs O(n) after the law's sort.  Repeated evaluations and
    inversion use prefix masses and inverse-gap suffix costs in O(log n).
    The entropy diagnostic can overflow; its logarithm and Q remain usable.
    """

    law: FiniteGapLaw
    rho: float
    quantile_gap: float
    tail_weights: Tuple[float, ...]
    core_weights: Tuple[float, ...]
    bands: Tuple[EntropyBand, ...]
    core_cost: float
    log_core_cost: float
    scale_entropy: float
    core_entropy: float
    log_core_entropy: float
    _tail_gaps: Tuple[float, ...]
    _prefix_mass: Tuple[float, ...]
    _exact_prefix_mass: Tuple[Fraction, ...]
    _log_inverse_suffix: Tuple[float, ...]
    _log_slope: Tuple[float, ...]
    _log_core_coefficient: float

    def __init__(self, law: FiniteGapLaw, rho: float):
        if not isinstance(law, FiniteGapLaw):
            raise ValueError("law must be a FiniteGapLaw")
        rho = _positive_float(rho, "rho")
        if rho > 0.25:
            raise ValueError("rho must lie in (0, 1/4]")
        remaining = Fraction(rho)
        tail, core = [], []
        boundary = None
        for gap, weight in zip(law.gaps, law.weights):
            exact_weight = Fraction(weight)
            take = min(exact_weight, remaining)
            tail.append(float(take))
            core.append(float(exact_weight - take))
            if take:
                boundary = gap
            remaining -= take
        # Normalized input has total mass approximately one, so rho <= 1/4
        # always leaves substantial core mass.
        if remaining or boundary is None:
            raise ValueError("normalized weights do not contain the requested tail mass")
        grouped = {}
        for gap, weight in zip(law.gaps, core):
            if weight:
                grouped.setdefault(_band_index(gap), []).append(math.log(weight) - 2 * math.log(gap))
        log_costs = tuple((index, _logsum(grouped[index])) for index in sorted(grouped))
        log_total = _logsum(cost for _, cost in log_costs)
        entropy = math.fsum(math.exp(cost - log_total) * max(0.0, log_total - cost)
                            for _, cost in log_costs)
        log_gamma = log_total + math.log1p(entropy)
        log_coefficient = 0.5 * (math.log(rho) + log_gamma)
        tail_pairs = tuple((gap, weight) for gap, weight in zip(law.gaps, tail) if weight)
        prefix = [0.0]
        exact_prefixes = [Fraction(0)]
        exact_prefix = Fraction(0)
        for _, weight in tail_pairs:
            exact_prefix += Fraction(weight)
            prefix.append(float(exact_prefix))
            exact_prefixes.append(exact_prefix)
        suffix = [-math.inf] * (len(tail_pairs) + 1)
        for index in range(len(tail_pairs) - 1, -1, -1):
            gap, weight = tail_pairs[index]
            suffix[index] = _logadd(math.log(weight) - math.log(gap), suffix[index + 1])
        fields = {
            "law": law, "rho": rho, "quantile_gap": boundary,
            "tail_weights": tuple(tail), "core_weights": tuple(core),
            "bands": tuple(EntropyBand(index, _exp(cost), cost) for index, cost in log_costs),
            "core_cost": _exp(log_total), "log_core_cost": log_total,
            "scale_entropy": entropy, "core_entropy": _exp(log_gamma),
            "log_core_entropy": log_gamma,
            "_tail_gaps": tuple(gap for gap, _ in tail_pairs),
            "_prefix_mass": tuple(prefix), "_exact_prefix_mass": tuple(exact_prefixes),
            "_log_inverse_suffix": tuple(suffix),
            "_log_slope": tuple(_logadd(log_coefficient, cost) for cost in suffix),
            "_log_core_coefficient": log_coefficient,
        }
        for name, value in fields.items():
            object.__setattr__(self, name, value)

    def evaluate(self, budget: float) -> RareEventEvaluation:
        """Compute Q(B) and the tail/entropy contributions at positive finite B."""
        budget = _positive_float(budget, "budget")
        resolution = 1 / math.sqrt(budget)
        log_resolution = -0.5 * math.log(budget)
        index = bisect.bisect_right(self._tail_gaps, resolution)
        tail = (self.rho if index == len(self._tail_gaps)
                else min(self.rho, self._prefix_mass[index]
                         + _exp(log_resolution + self._log_inverse_suffix[index])))
        entropy_term = _exp(log_resolution + self._log_core_coefficient)
        value = min(self.rho, tail + entropy_term)
        return RareEventEvaluation(budget, resolution, tail, entropy_term, value,
                                   max(tail, value / QUANTILE_SELECTION_FACTOR), value)

    def rate(self, budget: float) -> float:
        """Return only Q(B), a rate functional rather than a risk estimate."""
        return self.evaluate(budget).value

    def budget_for_rate(self, target: float) -> RateBudget:
        """Invert the piecewise-linear formula in h = B**(-1/2).

        The returned finite budget is a floating-point approximation to the
        threshold, not a certified sufficient budget for any estimator.
        No simulation, subset enumeration, or iterative budget search is used.
        """
        target = _positive_float(target, "target")
        if target >= self.rho:
            return RateBudget(target, 0.0, -math.inf, "saturated")
        # On a segment with k tail gaps <= h, the uncapped expression is
        # prefix_mass[k] + h * (sqrt(rho Gamma) + inverse_suffix[k]).
        # Find its segment by binary search over the gap breakpoints.
        exact_target = Fraction(target)
        # Prefixes can round to target across several tiny atoms.  Invert
        # against their exact stored-float sums, not those rounded prefixes.
        # Any feasible segment has prefix_mass < target since its slope > 0.
        low = 0
        high = min(len(self._tail_gaps), bisect.bisect_left(self._exact_prefix_mass, exact_target) - 1)
        while low < high:
            middle = (low + high) // 2
            available = float(exact_target - self._exact_prefix_mass[middle])
            if math.log(self._tail_gaps[middle]) + self._log_slope[middle] <= math.log(available):
                low = middle + 1
            else:
                high = middle
        remainder = float(exact_target - self._exact_prefix_mass[low])
        log_budget = 2 * (self._log_slope[low] - math.log(remainder))
        if log_budget > math.log(sys.float_info.max):
            return RateBudget(target, math.inf, log_budget, "overflow")
        budget = _exp(log_budget)
        return RateBudget(target, budget, log_budget, "finite")
