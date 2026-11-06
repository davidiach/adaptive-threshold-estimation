"""Learn a conservative finite gap law from observable, physically capped probes.

Zero mass represents unresolved gaps. The statistical argument and its oracle
comparison are in docs/ARBITRARY_LAW_ADAPTATION.md. No latent gap is observed.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
from random import Random

from .budget_ladders import CoinFactory, Exact, _budget, _exact, _execute
from .known_law_oracle import FiniteGapOracle, SplitIntegrals
from .rare_event_functional import FiniteGapLaw, Interval, Precision
from .tail_mass import _depth, _threshold


@dataclass(frozen=True, init=False)
class GapEnvelope:
    """A probability law on zero and positive dyadic gaps.

    cdf[j-1] bounds the actual mass at gaps <= 2**-j. These bounds must be
    valid for the caller's population to use this as a conservative oracle;
    construction validates their structure, not their statistical premise.
    Positive atoms lie one grid step below the corresponding threshold.
    """

    cdf: tuple[F, ...]
    zero_mass: F
    atoms: tuple[tuple[F, F], ...]
    _positive: FiniteGapOracle | None

    def __init__(self, cdf):
        values = tuple(_exact(value) for value in cdf)
        if not values or values[0] != 1 or any(not 0 <= u <= 1 for u in values):
            raise ValueError("CDF bounds must start at one and lie in [0,1].")
        if any(a < b for a, b in zip(values, values[1:])):
            raise ValueError("CDF bounds must decrease with depth.")
        atoms = tuple((F(1, 2**(j + 2)), a - b)
                      for j, (a, b) in enumerate(zip(values, values[1:])) if a > b)
        mass = 1 - values[-1]
        positive = (FiniteGapOracle(FiniteGapLaw([(d, w / mass) for d, w in atoms]))
                    if mass else None)
        object.__setattr__(self, "cdf", values)
        object.__setattr__(self, "zero_mass", values[-1])
        object.__setattr__(self, "atoms", atoms)
        object.__setattr__(self, "_positive", positive)

    def null_prefix(self, heads: int, tails: int, tolerance: F) -> Interval:
        value = self.zero_mass * F(1, 2)**(heads + tails)
        value += sum((w * (F(1, 2) - d)**heads * (F(1, 2) + d)**tails
                      for d, w in self.atoms), F(0))
        return Interval(value, value)

    def split(self, rho: F, budget: F, precision: Precision) -> SplitIntegrals:
        if self.zero_mass >= rho:
            # The planner takes its constant fallback before inspecting costs.
            return SplitIntegrals({}, self.zero_mass, F(0), lambda _: F(0), lambda _: F(0))
        mass = 1 - self.zero_mass
        conditional_rho = (rho - self.zero_mass) / mass
        design = self._positive.split(conditional_rho, budget, precision)
        return SplitIntegrals(
            {j: mass * a for j, a in design.band_costs.items()},
            self.zero_mass + mass * design.unresolved_mass,
            mass * design.tail_inverse,
            lambda cap: mass * design.resolved_error(cap),
            lambda cap: mass * design.tail_work(cap),
        )


@dataclass(frozen=True)
class EnvelopePlan:
    depth: int
    rho: F
    delta: F
    blocks: int
    coin_cap: int
    probe_caps: tuple[int, ...]

    @property
    def flip_cap(self) -> int:
        return self.blocks * sum(self.probe_caps)


def plan_gap_envelope(depth: int, *, rho: Exact, delta: Exact) -> EnvelopePlan:
    _depth(depth)
    rarity, failure = _exact(rho), _exact(delta)
    if not 0 < rarity <= F(1, 4) or not 0 < failure < 1:
        raise ValueError("Require rho in (0,1/4] and delta in (0,1).")
    n = 4**depth
    inverse = 2 * depth / failure
    ceiling = -(-inverse.numerator // inverse.denominator)
    blocks = 8 * (ceiling - 1).bit_length() + 1
    squared_cap = 64 * n / rarity
    coin_cap = isqrt(squared_cap.numerator // squared_cap.denominator)
    if coin_cap**2 * squared_cap.denominator < squared_cap.numerator:
        coin_cap += 1
    caps = tuple(-(-n // (2 * j * (j + 1))) + 2**(depth + j - 2)
                 for j in range(1, depth + 1))
    return EnvelopePlan(depth, rarity, failure, blocks, coin_cap, caps)


def _probe_program(depth: int, cap: int, coin_cap: int):
    """Yield local coin IDs, stopping at the first unresolved coin or either cap."""
    used = completed = 0
    while used < cap and completed < coin_cap:
        heads = prefix = 0
        for level in range(depth + 1):
            target = 4**level
            while prefix < target:
                if used == cap:
                    return min(F(1), F(8, completed)) if completed else F(1)
                bit = yield completed
                if type(bit) is not int or bit not in (0, 1):
                    raise ValueError("A coin must return integer 0 or 1.")
                used += 1
                prefix += 1
                heads += bit
            if abs(2 * heads - prefix) > 2 * _threshold(depth, level):
                completed += 1
                break
            if level == depth:
                completed += 1
                return min(F(1), F(8, completed))
    return min(F(1), F(8, completed)) if completed else F(1)


def _relay(program, offset):
    """Close subprograms even if acquisition is interrupted or a callback fails."""
    try:
        try:
            query = next(program)
        except StopIteration as done:
            return done.value
        while True:
            bit = yield offset + query
            try:
                query = program.send(bit)
            except StopIteration as done:
                return done.value
    finally:
        program.close()


def gap_envelope_program(plan: EnvelopePlan):
    if not isinstance(plan, EnvelopePlan):
        raise TypeError("Expected an EnvelopePlan.")
    if plan != plan_gap_envelope(plan.depth, rho=plan.rho, delta=plan.delta):
        raise ValueError("Envelope plan does not match its parameters.")
    bounds, offset = [], 0
    for depth, cap in enumerate(plan.probe_caps, 1):
        outputs = []
        for _ in range(plan.blocks):
            outputs.append((yield from _relay(_probe_program(depth, cap, plan.coin_cap), offset)))
            offset += cap + 1
        median = sorted(outputs)[plan.blocks // 2]
        bounds.append(min(bounds[-1], median) if bounds else median)
    return GapEnvelope(bounds)


@dataclass(frozen=True)
class EnvelopeResult:
    envelope: GapEnvelope
    flips: int
    items: int


def run_gap_envelope(plan: EnvelopePlan, coin_factory: CoinFactory, *, budget: int, seed: int = 0):
    if not isinstance(plan, EnvelopePlan):
        raise TypeError("Expected an EnvelopePlan.")
    if plan != plan_gap_envelope(plan.depth, rho=plan.rho, delta=plan.delta):
        raise ValueError("Envelope plan does not match its parameters.")
    if _budget(budget) < plan.flip_cap:
        raise ValueError("Authorize the entire planned flip cap before running.")
    if type(seed) is not int or not callable(coin_factory):
        raise TypeError("Require an integer seed and a callable coin_factory.")
    envelope, used, made, timed_out = _execute(
        gap_envelope_program(plan), coin_factory, Random(seed), plan.flip_cap)
    if timed_out:
        raise AssertionError("Envelope program exceeded its proved physical cap.")
    return EnvelopeResult(envelope, used, made)
