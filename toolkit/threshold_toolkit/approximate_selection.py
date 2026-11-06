"""Rational state trimming for a (1+epsilon) finite-law selection witness.

The guarantee is conditional on the paper proof in
research/2026-11-06-selection-approximation/NOTE.md and the existing suffix
theorem. This Python implementation is not formally verified. The enclosed
quantity is the deterministic rate functional K, not statistical risk.
"""

from dataclasses import dataclass
from fractions import Fraction as F

from .band_cost_selection import _saves_more
from .rare_event_functional import (
    FiniteGapLaw,
    Interval,
    Precision,
    Rational,
    _floor_log2,
    _parameters,
    band_index,
    evaluate_selection,
    log_interval,
    rational,
)


@dataclass(frozen=True)
class ApproximateSelectionResult:
    """Global enclosure and an actual witness, under the paper theorem.

    value.lower <= K <= witness objective <= value.upper, and
    value.upper <= (1+epsilon)*value.lower. This does not assert exact
    optimality. Limits cause an exception, never a partial result.
    """

    value: Interval
    witness_value: Interval
    selected: tuple[bool, ...]
    epsilon: F
    suffix_count: int
    final_states: int
    peak_states: int
    transitions: int
    subdivisions: int
    entropy_bound: int
    precision: Precision


@dataclass(frozen=True)
class _Option:
    cost: F
    fixed: F
    scaled: F
    mask: int


@dataclass(frozen=True)
class _State:
    mass: F
    surrogate: F
    fixed: F
    scaled: F
    mask: int


def _ceil(x: F) -> int:
    return -(-x.numerator // x.denominator)


def _bin(x: F, unit: F, subdivisions: int) -> tuple[int, int]:
    """Exact bins whose positive endpoints have ratio <= 1+1/subdivisions.

    Subdivide each dyadic interval linearly. This avoids huge rational
    powers of 1+1/subdivisions while retaining the multiplicative guarantee.
    """
    if x == 0:
        return (-1, -1)
    if x < unit:
        raise ValueError("Positive trimming coordinate is below its unit")
    ratio = x / unit
    exponent = _floor_log2(ratio)
    mantissa = ratio / (1 << exponent)
    offset = (mantissa - 1) * subdivisions
    return exponent, offset.numerator // offset.denominator


def _upper_log(x: F, epsilon: F) -> F:
    """Return ln(x) <= u <= ln(x)+epsilon/8 for rational x>=1.

    All returned values share a small rational denominator. Keeping the
    series denominators in every DP coordinate would waste arithmetic work.
    """
    denominator = _ceil(16 / epsilon)
    terms = 4
    while True:
        enclosure = log_interval(x, terms)
        if enclosure.width <= epsilon / 16:
            return F(_ceil(enclosure.upper * denominator), denominator)
        if terms == 256:
            raise ValueError("Logarithm accuracy exceeds supported precision")
        terms = min(256, 2 * terms)


def select_approximately(
    law: FiniteGapLaw,
    *,
    rho: Rational,
    budget: Rational,
    epsilon: Rational = "1/10",
    precision: Precision = Precision(),
    max_transitions: int = 200_000,
) -> ApproximateSelectionResult:
    """Return a paper-certified (1+epsilon) selection and enclosure for K.

    Repeated band costs are not required. Exact rational comparisons govern
    trimming and saved ordinary costs. Log/sqrt intervals govern final
    evaluation; they are refined until the error budget is certified.
    The practical transition/precision limits can raise ValueError. The
    mathematical FPTAS permits these resources to grow polynomially.
    """
    r, b = _parameters(rho, budget)
    eps = rational(epsilon)
    if not 0 < eps <= 1:
        raise ValueError("epsilon must lie in (0,1]")
    if type(max_transitions) is not int or max_transitions < 1:
        raise ValueError("max_transitions must be a positive integer")
    if not isinstance(precision, Precision):
        raise TypeError("precision must be a Precision")

    by_band: dict[int, list[int]] = {}
    for i, atom in enumerate(law.atoms):
        by_band.setdefault(band_index(atom.gap), []).append(i)
    menus = []
    suffix_count = 1
    for group in by_band.values():
        options = [_Option(F(0), F(0), F(0), 0)]
        cost = fixed = scaled = F(0)
        mask = 0
        for i in reversed(group):
            atom = law.atoms[i]
            cost += atom.mass / atom.gap**2
            if b * atom.gap**2 <= 1:
                fixed += atom.mass
            else:
                scaled += atom.mass / atom.gap
            mask |= 1 << i
            options.append(_Option(cost, fixed, scaled, mask))
        menus.append(options)
        suffix_count *= len(options)

    positive = {option.cost for menu in menus for option in menu if option.cost}
    unit = min(positive)
    maximum = sum((menu[-1].cost for menu in menus), F(0))
    # L >= 4+log(maximum/unit), using log(x) <= log2(x) for x>=1.
    log2_floor = _floor_log2(maximum / unit)
    ceil_log2 = log2_floor + (maximum / unit != 1 << log2_floor)
    bound = 4 + ceil_log2
    subdivisions = _ceil(16 * len(menus) * bound / eps)
    surrogates = {a: a * (1 + _upper_log(a / unit, eps)) for a in positive}
    surrogates[F(0)] = F(0)

    zero = _State(F(0), F(0), F(0), F(0), 0)
    frontier = {((-1, -1), (-1, -1)): zero}
    transitions = 0
    peak_states = 1
    for menu in menus:
        next_transitions = transitions + len(frontier) * len(menu)
        if next_transitions > max_transitions:
            raise ValueError("Selection search exceeds max_transitions")
        following = {}
        for state in frontier.values():
            for option in menu:
                mass = state.mass + option.cost
                surrogate = state.surrogate + surrogates[option.cost]
                fixed = state.fixed + option.fixed
                scaled = state.scaled + option.scaled
                key = (_bin(mass, unit, subdivisions),
                       _bin(surrogate, unit, subdivisions))
                old = following.get(key)
                if old is None or _saves_more(fixed - old.fixed, scaled - old.scaled, b):
                    following[key] = _State(
                        mass, surrogate, fixed, scaled, state.mask | option.mask
                    )
        frontier = following
        transitions = next_transitions
        peak_states = max(peak_states, len(frontier))

    beta = 1 + eps / 4
    current = precision
    while True:
        values = []
        for state in frontier.values():
            selected = tuple(bool(state.mask & (1 << i)) for i in range(len(law.atoms)))
            value = evaluate_selection(law, tuple(map(int, selected)),
                                       rho=r, budget=b, precision=current)
            values.append((value, selected))
        witness, selected = min(values, key=lambda pair: pair[0].upper)
        retained_lower = min(value.lower for value, _ in values)
        if witness.upper <= beta * retained_lower:
            enclosure = Interval(retained_lower / beta, witness.upper)
            if not enclosure.upper <= (1 + eps) * enclosure.lower:
                raise AssertionError("Internal approximation budget failed")
            return ApproximateSelectionResult(
                enclosure, witness, selected, eps, suffix_count, len(frontier),
                peak_states, transitions, subdivisions, bound, current,
            )
        if current.bits == 512 and current.log_terms == 256:
            raise ValueError("Final comparison exceeds supported precision")
        current = Precision(bits=min(512, 2 * current.bits),
                            log_terms=min(256, 2 * current.log_terms))
