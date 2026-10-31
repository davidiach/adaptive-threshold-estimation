"""Nested confidence sets on a strict observation-budget schedule.

Coverage is conditional on valid marginal stage intervals. No independence
of the intervals is required for the union bound. A timeout preserves the
current set; an empty intersection stays empty. Known-law entropy-tail
width claims additionally require the paper-only confidence-transfer theorem.

Apache-2.0. Extracted from the 30 October 2026 round-three contribution.
"""
from __future__ import annotations
from collections.abc import Callable, Generator
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import math
import random
from .budget_ladders import (
    Exact, CoinFactory, StageRun, _exact, _budget, _execute, stage, plan,
)
IntervalFactory = Callable[[int, Fraction, random.Random], Generator[int, int, object]]

def stage_delta(delta: Exact, index: int) -> Fraction:
    d = _exact(delta)
    if not 0 < d <= Fraction(1, 4):
        raise ValueError('delta must lie in (0,1/4].')
    stage(index)
    return d / ((index+1)*(index+2))

@dataclass(frozen=True)
class ClosedInterval:
    """Exact closed interval. lower > upper explicitly represents the empty set."""
    lower: Fraction
    upper: Fraction

    def __post_init__(self):
        object.__setattr__(self, 'lower', _exact(self.lower))
        object.__setattr__(self, 'upper', _exact(self.upper))

    @property
    def empty(self) -> bool:
        return self.lower > self.upper

    @property
    def width(self) -> Fraction:
        return max(Fraction(0), self.upper-self.lower)

    def contains(self, value: Exact) -> bool:
        q = _exact(value)
        return self.lower <= q <= self.upper

    def intersect(self, other: 'ClosedInterval') -> 'ClosedInterval':
        if not isinstance(other, ClosedInterval):
            raise TypeError('A ClosedInterval is required.')
        return ClosedInterval(max(self.lower, other.lower), min(self.upper, other.upper))

    def midpoint(self) -> Fraction:
        if self.empty:
            raise ValueError('An empty interval has no midpoint.')
        return (self.lower+self.upper)/2


@dataclass(frozen=True)
class ConfidenceState:
    authorized_budget: int
    reserved_budget: int
    flips: int
    interval: ClosedInterval
    spent_failure_budget: Fraction
    remaining_failure_budget: Fraction
    runs: tuple[StageRun, ...]


class ConfidenceLadder:
    """Intersect stage intervals, with exact summable failure allowances.

    An eligible interval_factory receives (flip_cap, stage_delta, private_rng).
    It must return an interval with the stated unconditional marginal coverage.
    A timeout contributes [0,upper], preserving coverage but not a width rate.
    Empty intersections remain empty and are never silently reset.
    """
    def __init__(self, interval_factory: IntervalFactory, coin_factory: CoinFactory,
                 *, delta: Exact, upper: Exact = 1, seed: int = 0):
        self.delta, self.upper = _exact(delta), _exact(upper)
        if not 0 < self.delta <= Fraction(1, 4) or not 0 < self.upper <= 1:
            raise ValueError('Require delta in (0,1/4] and upper in (0,1].')
        if type(seed) is not int:
            raise TypeError('seed must be an integer.')
        if not callable(interval_factory) or not callable(coin_factory):
            raise TypeError('Factories must be callable.')
        self._factory, self._coins = interval_factory, coin_factory
        self._rng = random.Random(seed)
        self._interval = ClosedInterval(0, self.upper)
        self._runs: list[StageRun] = []
        self._authorized = self._flips = self._reserved = 0
        self._spent = Fraction(0)
        self._failed = False

    def advance_to(self, total_budget: int) -> ConfidenceState:
        n = _budget(total_budget)
        if self._failed:
            raise RuntimeError('A callback failed; this ladder is invalidated.')
        if n < self._authorized:
            raise ValueError('Cumulative authorized budget cannot decrease.')
        self._authorized = n
        for s in plan(n)[len(self._runs):]:
            d = stage_delta(self.delta, s.index)
            prng = random.Random(self._rng.getrandbits(256))
            srng = random.Random(self._rng.getrandbits(256))
            try:
                output, used, made, timed_out = _execute(
                    self._factory(s.flip_cap, d, prng), self._coins, srng, s.flip_cap)
                if not timed_out:
                    if not isinstance(output, ClosedInterval):
                        raise TypeError('Interval program must return a ClosedInterval.')
                    self._interval = self._interval.intersect(output)
            except BaseException:
                self._failed = True
                raise
            self._spent += d
            self._flips += used
            self._reserved += s.flip_cap
            self._runs.append(StageRun(s.index, used, made, timed_out))
        assert self._flips <= self._reserved <= n
        return ConfidenceState(n, self._reserved, self._flips, self._interval,
                               self._spent, self.delta-self._spent, tuple(self._runs))


def _log_series_upper(y: Fraction, terms: int = 32) -> Fraction:
    # y in [1,2]. log(y)=2 atanh((y-1)/(y+1)). Nonnegative remainder.
    z = (y-1)/(y+1)
    z2, power, total = z*z, z, Fraction(0)
    for k in range(terms):
        total += power/(2*k+1)
        power *= z2
    return 2*(total + power/((2*terms+1)*(1-z2)))


@lru_cache(maxsize=256)
def _log_upper(x: Fraction) -> Fraction:
    if x < 1:
        raise ValueError('Internal logarithm requires x >= 1.')
    k = max(0, x.numerator.bit_length()-x.denominator.bit_length())
    power = 1 << k
    if power > x:
        k -= 1
        power >>= 1
    y = x/power
    assert 1 <= y < 2
    return k*_log_series_upper(Fraction(2)) + _log_series_upper(y)


def _sqrt_upper(q: Fraction, bits: int = 80) -> Fraction:
    scale = 1 << bits
    n = math.isqrt((q.numerator*scale*scale)//q.denominator)
    if n*n*q.denominator < q.numerator*scale*scale:
        n += 1
    return Fraction(n, scale)


def bernoulli_interval(heads: int, flips: int, delta: Exact,
                       *, upper: Exact = 1) -> ClosedInterval:
    """Rigorous Hoeffding interval for iid fresh Bernoulli observations only.

    This is NOT valid for pooled repeated flips of heterogeneous hidden coins.
    It is valid in the d=1/2 demonstration because fresh coins reveal signs.
    Exact rational log/sqrt upper bounds avoid rounding the radius downward.
    """
    if type(flips) is not int or flips <= 0 or type(heads) is not int or not 0 <= heads <= flips:
        raise ValueError('Require integers 0 <= heads <= flips and flips > 0.')
    _budget(flips)
    d, u = _exact(delta), _exact(upper)
    if not 0 < d <= 1 or not 0 < u <= 1:
        raise ValueError('Require delta and upper in (0,1].')
    r = _sqrt_upper(_log_upper(2/d)/(2*flips))
    mean = Fraction(heads, flips)
    return ClosedInterval(mean-r, mean+r).intersect(ClosedInterval(0, u))
