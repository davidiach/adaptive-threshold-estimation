"""An observable confidence sequence for positive gaps of unknown distribution."""

from collections.abc import Generator
from fractions import Fraction
from math import isqrt
from random import Random

from .budget_ladders import CoinFactory, Exact
from .confidence_ladders import ClosedInterval, ConfidenceLadder


def _hoeffding_count(trials: int, failure: Fraction) -> int:
    """Smallest integer h with 2h² >= trials * ceil(log2(1/failure))."""
    inverse_ceiling = -(-failure.denominator // failure.numerator)
    exponent = (inverse_ceiling - 1).bit_length()
    squared = (trials * exponent + 1) // 2
    return 1 + isqrt(squared - 1) if squared else 0


def _stage(
    cap: int, failure: Fraction, rng: Random
) -> Generator[int, int, ClosedInterval]:
    items = isqrt(cap)
    flips = cap // items
    tolerance = Fraction(1, items)
    threshold = _hoeffding_count(flips, tolerance)
    positive = negative = 0
    for item in range(items):
        heads = 0
        for _ in range(flips):
            heads += yield item
        excess = 2 * heads - flips
        if excess > 2 * threshold:
            positive += 1
        elif excess < -2 * threshold:
            negative += 1
    sampling = Fraction(_hoeffding_count(items, failure / 3), items)
    pad = sampling + tolerance
    return ClosedInterval(
        max(Fraction(0), Fraction(positive, items) - pad),
        min(Fraction(1), 1 - Fraction(negative, items) + pad),
    )


def unknown_law_confidence(
    coin_factory: CoinFactory, *, delta: Exact, upper: Exact = 1, seed: int = 0
) -> ConfidenceLadder:
    """Return a hard-budget ladder using flips alone.

    Fresh items draw independent copies of the population's joint sign-gap law.
    The sign and gap within one item may be dependent.
    Repeated flips are iid conditional on that item. The positive fraction
    must be at most upper. No magnitude-law integrals or margin bounds enter.
    """
    return ConfidenceLadder(_stage, coin_factory, delta=delta, upper=upper, seed=seed)
