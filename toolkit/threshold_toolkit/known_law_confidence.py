"""Executable known-law confidence stages and their cumulative-budget ladder.

Coverage uses the per-plan MSE/work argument in docs/KNOWN_LAW_ESTIMATOR.md,
valid oracle bounds and independent coins/private randomness. Python and its
PRNG are outside the Lean proof. Every requested flip goes through the ladder.
"""

from fractions import Fraction
from random import Random

from .budget_ladders import CoinFactory, Exact, _exact
from .confidence_amplification import MedianSchedule
from .confidence_ladders import ClosedInterval, ConfidenceLadder
from .known_law_oracle import KnownGapOracle
from .known_rare_estimator import RarePlan, known_rare_program, plan_known_rare
from .rare_event_functional import sqrt_interval


def _capped_block(plan: RarePlan, rng: Random, cap: int, offset: int):
    """Relay one block, translating its coin IDs into a disjoint namespace."""
    program = known_rare_program(plan, rng)
    labels = {}
    used = 0
    try:
        try:
            query = next(program)
        except StopIteration as done:
            return _exact(done.value), 0
        while True:
            if type(query) is not int or query < 0:
                raise ValueError("Coin IDs must be nonnegative integers.")
            if used == cap:
                return plan.rho / 2, len(labels)
            if query not in labels:
                labels[query] = offset + len(labels)
            bit = yield labels[query]
            if type(bit) is not int or bit not in (0, 1):
                raise ValueError("A coin must return integer 0 or 1.")
            used += 1
            try:
                query = program.send(bit)
            except StopIteration as done:
                return _exact(done.value), len(labels)
    finally:
        program.close()


def known_law_interval(law: KnownGapOracle, *, rho: Exact, cap: int,
                       delta: Exact, rng: Random):
    """Yield paid coin IDs; return a rational interval with failure <= delta.

    Each median block has its own coin namespace and private seed. It is
    forcibly stopped at its share of cap, including between classifier flips.
    The radius rounds sqrt(8 * plan.mse_bound) upwards. A radius of at least rho
    returns [0,rho] without sampling: then [c-r,c+r] contains [0,rho] for every
    centre c in [0,rho]. A smaller radius can still narrow [0,rho] when the
    centre lies near an end, so it samples. Oracle validity remains the
    caller's premise.
    """
    schedule = MedianSchedule(cap, rho=rho, delta=delta)
    base = plan_known_rare(law, rho=schedule.rho,
                           budget=schedule.base_expected_budget)
    radius = sqrt_interval(8 * base.mse_bound).upper
    full = ClosedInterval(0, schedule.rho)
    if radius >= schedule.rho:
        return full
    outputs = []
    offset = 0
    for _ in range(schedule.blocks):
        value, made = yield from _capped_block(
            base, Random(rng.getrandbits(256)), schedule.per_block_cap, offset)
        outputs.append(max(Fraction(0), min(schedule.rho, value)))
        offset += made
    center = sorted(outputs)[schedule.blocks // 2]
    return ClosedInterval(center - radius, center + radius).intersect(full)


def known_law_ladder(law: KnownGapOracle, coin_factory: CoinFactory, *,
                     rho: Exact, delta: Exact, seed: int = 0) -> ConfidenceLadder:
    """A nested known-law confidence sequence with a hard cumulative flip cap.

    Fresh stages receive summable failure allowances. Widths use the executable
    estimator's MSE certificates; this API does not claim Lean's exact constants.
    """
    rarity = _exact(rho)
    if not 0 < rarity <= Fraction(1, 4):
        raise ValueError("rho must lie in (0,1/4].")
    if not callable(getattr(law, "split", None)) or not callable(
            getattr(law, "null_prefix", None)):
        raise TypeError("A known gap law must implement split and null_prefix.")

    def stage(cap, failure, rng):
        return known_law_interval(law, rho=rarity, cap=cap, delta=failure, rng=rng)

    return ConfidenceLadder(stage, coin_factory, delta=delta, upper=rarity, seed=seed)
