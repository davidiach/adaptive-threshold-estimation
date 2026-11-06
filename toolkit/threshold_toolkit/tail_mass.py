"""Observable small-gap mass certificates for an arbitrary unknown law.

The paper proof and oracle comparison are in docs/ARBITRARY_LAW_TAIL.md.
These are certificates for P(D <= 2**-depth), not intervals for the positive
fraction. Python execution and the PRNG are not formally verified.
"""

from dataclasses import dataclass
from fractions import Fraction
from math import isqrt
from random import Random

from .budget_ladders import CoinFactory, Exact, _budget, _exact


def _depth(value: int) -> int:
    if type(value) is not int or value < 1:
        raise ValueError("depth must be a positive integer.")
    return value


def _threshold(depth: int, level: int) -> int:
    square = 2 * 4**level * (depth - level + 2)
    return 1 + isqrt(square - 1)


@dataclass(frozen=True)
class TailProbeState:
    authorized_budget: int
    flips: int
    items: int
    completed: int
    unresolved: bool
    upper: Fraction


class TailMassProbe:
    """Stop on the first unresolved coin, preserving every paid prefix.

    Fresh factory calls must supply independent persistent coins. Flips are
    iid conditional on each coin's sign and gap; those two latent variables
    may be dependent. No law, latent gap, sign, or integration oracle is used.
    For a fixed depth, upper covers its small-gap mass simultaneously at all
    cumulative budgets with probability at least 7/8. A lone probe does not
    accept a user-selected failure probability; use run_tail_mass for that.
    """

    def __init__(self, depth: int, coin_factory: CoinFactory, *, seed: int = 0):
        self.depth = _depth(depth)
        if not callable(coin_factory):
            raise TypeError("coin_factory must be callable.")
        if type(seed) is not int:
            raise TypeError("seed must be an integer.")
        self._factory, self._rng = coin_factory, Random(seed)
        self._thresholds = tuple(_threshold(depth, k) for k in range(depth + 1))
        self._authorized = self._flips = self._items = self._completed = 0
        self._prefix = self._heads = self._level = 0
        self._coin = None
        self._unresolved = self._failed = False

    def advance_to(self, total_budget: int) -> TailProbeState:
        allowance = _budget(total_budget)
        if self._failed:
            raise RuntimeError("A callback failed; this probe is invalidated.")
        if allowance < self._authorized:
            raise ValueError("Cumulative authorized budget cannot decrease.")
        self._authorized = allowance
        try:
            while self._flips < allowance and not self._unresolved:
                if self._coin is None:
                    self._coin = self._factory(self._rng)
                    if not callable(self._coin):
                        raise TypeError("coin_factory must return a callable.")
                    self._items += 1
                # Charge attempted flips too, before invoking caller code.
                self._flips += 1
                bit = self._coin()
                if type(bit) is not int or bit not in (0, 1):
                    raise ValueError("A flip callback must return the integer 0 or 1.")
                self._prefix += 1
                self._heads += bit
                if self._prefix != 4**self._level:
                    continue
                resolved = abs(2 * self._heads - self._prefix) > 2 * self._thresholds[self._level]
                if resolved or self._level == self.depth:
                    self._completed += 1
                    self._unresolved = not resolved
                    self._coin = None
                    self._prefix = self._heads = self._level = 0
                else:
                    self._level += 1
        except Exception:
            self._failed = True
            raise
        upper = min(Fraction(1), Fraction(8, self._completed)) if self._completed else Fraction(1)
        return TailProbeState(allowance, self._flips, self._items,
                              self._completed, self._unresolved, upper)


@dataclass(frozen=True)
class TailMassPlan:
    depth: int
    delta: Fraction
    blocks: int

    @property
    def scale(self) -> Fraction:
        return Fraction(1, 2**self.depth)

    @property
    def block_cap(self) -> int:
        return 4**self.depth

    @property
    def flip_cap(self) -> int:
        return self.blocks * self.block_cap


@dataclass(frozen=True)
class TailMassResult:
    scale: Fraction
    upper: Fraction
    flips: int
    items: int
    blocks: tuple[TailProbeState, ...]


def plan_tail_mass(depth: int, *, delta: Exact) -> TailMassPlan:
    """Plan an odd number m >= 8 log(2/delta) of independent capped probes."""
    _depth(depth)
    failure = _exact(delta)
    if not 0 < failure < 1:
        raise ValueError("delta must lie strictly between zero and one.")
    inverse = 2 / failure
    ceiling = -(-inverse.numerator // inverse.denominator)
    exponent = (ceiling - 1).bit_length()
    return TailMassPlan(depth, failure, 8 * exponent + 1)


def run_tail_mass(
    plan: TailMassPlan, coin_factory: CoinFactory, *, budget: int, seed: int = 0
) -> TailMassResult:
    """Return a median certificate within a preauthorized physical flip cap.

    The failure allowance covers both validity and the paper's finite-budget
    width bound at this one scale. For a sequence of scales, spend delta
    across the calls as described in the proof. A failed callback aborts;
    no certificate is returned from a partial failed run.
    """
    if not isinstance(plan, TailMassPlan):
        raise TypeError("Expected a TailMassPlan.")
    if plan != plan_tail_mass(plan.depth, delta=plan.delta):
        raise ValueError("Tail-mass plan does not match its parameters.")
    if _budget(budget) < plan.flip_cap:
        raise ValueError("Authorize the entire planned flip cap before running.")
    if not callable(coin_factory):
        raise TypeError("coin_factory must be callable.")
    if type(seed) is not int:
        raise TypeError("seed must be an integer.")
    rng = Random(seed)
    states = tuple(
        TailMassProbe(plan.depth, coin_factory, seed=rng.getrandbits(256)).advance_to(plan.block_cap)
        for _ in range(plan.blocks)
    )
    upper = sorted(state.upper for state in states)[plan.blocks // 2]
    return TailMassResult(plan.scale, upper, sum(s.flips for s in states),
                          sum(s.items for s in states), states)
