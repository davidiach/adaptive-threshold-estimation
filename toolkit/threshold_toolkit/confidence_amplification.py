"""Hard-flip-budget median amplification of an eligible base estimator.

The driver, not the estimator, purchases observations. Each base program is
an interactive generator: yield a nonnegative local coin ID to request its
next flip; return a finite numerical estimate to stop. A new ID creates a
fresh hidden coin at its first observation. Repeated IDs retain that coin.

STATISTICAL CONTRACT (not inferred or checked by this implementation):
For every admissible population the uncapped base program must have expected
work <= schedule.base_expected_budget and mean squared error <= R**2. Base
runs and fresh coins must have independent seeds/latent states/tapes. Then
this driver has error <= sqrt(8)*R with probability >= 1-delta, and NEVER
purchases more than total_budget flips. Clipping assumes theta in [0,rho].

The package does not implement the general-law rare-event base estimator.
A factory is not certified merely because the driver accepts it. Python's
PRNG is used for reproducible experiments; it is not a formal probability
space, a cryptographic boundary, or a guarantee for adversarial callbacks.
Physical flips are capped; CPU time and callback execution are not.

Apache-2.0. Additive research contribution, 30 October 2026.
"""
from __future__ import annotations

from collections.abc import Callable, Generator, Mapping
from dataclasses import dataclass
from fractions import Fraction
import math
import random
from typing import Union

Rational = Union[int, str, Fraction]
ProgramFactory = Callable[[Fraction, random.Random], Generator[int, int, object]]
CoinFactory = Callable[[random.Random], Callable[[], int]]
SCHEMA = "ate-capped-median-v1"
SCOPE = "amplification_only_conditional_on_base_work_mse_and_independence"
MAX_INPUT_BITS = 8192


def _rational(value: Rational) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, str, Fraction)):
        raise TypeError("Use int, Fraction, or an exact decimal/rational string.")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError, OverflowError) as exc:
        raise ValueError("Invalid finite rational.") from exc
    if max(result.numerator.bit_length(), result.denominator.bit_length()) > MAX_INPUT_BITS:
        raise ValueError("Rational exceeds the input bit limit.")
    return result


def _failure_squared_le(blocks: int, delta: Fraction) -> bool:
    # (sqrt(3)/2)**blocks <= delta, decided without logarithms or floats.
    return (pow(3, blocks) * delta.denominator**2
            <= pow(4, blocks) * delta.numerator**2)


def median_block_count(delta: Rational, *, max_blocks: int = 100001) -> int:
    """Least positive odd m with (3/4)**m <= delta**2, using exact integers.

    If independent blocks fail with probabilities <= 1/4, a Chernoff bound
    is (sqrt(3)/2)**m. It need not equal the actual binomial-tail probability.
    """
    d = _rational(delta)
    if not 0 < d <= Fraction(1, 4):
        raise ValueError("delta must lie in (0,1/4].")
    if type(max_blocks) is not int or max_blocks < 1:
        raise ValueError("max_blocks must be a positive integer.")
    largest = max_blocks if max_blocks % 2 else max_blocks - 1
    maximum_k = (largest - 1) // 2
    lo, hi = 0, min(1, maximum_k)
    while not _failure_squared_le(2 * hi + 1, d):
        if hi == maximum_k:
            raise ValueError("Required block count exceeds max_blocks; no plan produced.")
        lo, hi = hi + 1, min(maximum_k, max(1, 2 * hi))
    while lo < hi:
        middle = (lo + hi) // 2
        if _failure_squared_le(2 * middle + 1, d):
            hi = middle
        else:
            lo = middle + 1
    return 2 * lo + 1


@dataclass(frozen=True, init=False)
class MedianSchedule:
    total_budget: int
    rho: Fraction
    delta: Fraction
    blocks: int
    per_block_cap: int
    base_expected_budget: Fraction

    def __init__(self, total_budget: int, *, rho: Rational, delta: Rational,
                 max_blocks: int = 100001) -> None:
        if type(total_budget) is not int or total_budget < 1:
            raise ValueError("total_budget must be a positive integer.")
        if total_budget.bit_length() > MAX_INPUT_BITS:
            raise ValueError("Budget exceeds the input bit limit.")
        r, d = _rational(rho), _rational(delta)
        if not 0 < r <= Fraction(1, 4):
            raise ValueError("rho must lie in (0,1/4].")
        m = median_block_count(d, max_blocks=max_blocks)
        object.__setattr__(self, "total_budget", total_budget)
        object.__setattr__(self, "rho", r)
        object.__setattr__(self, "delta", d)
        object.__setattr__(self, "blocks", m)
        object.__setattr__(self, "per_block_cap", total_budget // m)
        object.__setattr__(self, "base_expected_budget", Fraction(total_budget, 8 * m))

    @property
    def deterministic_flip_cap(self) -> int:
        return self.blocks * self.per_block_cap

    def record(self) -> dict[str, object]:
        return {
            "schema": SCHEMA,
            "scope": SCOPE,
            "total_budget": self.total_budget,
            "rho": str(self.rho),
            "delta": str(self.delta),
            "blocks": self.blocks,
            "per_block_cap": self.per_block_cap,
            "deterministic_flip_cap": self.deterministic_flip_cap,
            "base_expected_budget": str(self.base_expected_budget),
            "squared_failure_bound": f"(3/4)^{self.blocks}",
            "timeout_probability_bound": "1/8",
            "mse_tail_probability_bound": "1/8",
            "radius_multiplier_squared": "8",
        }


def verify_schedule_record(record: Mapping[str, object], *, total_budget: int,
                           rho: Rational, delta: Rational,
                           max_blocks: int = 100001) -> bool:
    """Replay bound to an independently supplied expected instance.

    Recalculation is not independent verification of Python correctness.
    Unknown, missing, or altered fields are rejected.
    """
    if not isinstance(record, Mapping):
        return False
    try:
        expected = MedianSchedule(total_budget, rho=rho, delta=delta,
                                  max_blocks=max_blocks).record()
    except (ValueError, TypeError, OverflowError):
        return False
    # Strict field types prevent bools silently matching integer metadata.
    return (set(record) == set(expected)
            and all(type(record[k]) is type(v) and record[k] == v
                    for k, v in expected.items()))


@dataclass(frozen=True)
class MedianResult:
    estimate: int | float | Fraction
    flips: int
    created_coins: int
    completed_blocks: int
    timed_out_blocks: int
    per_block_flips: tuple[int, ...]
    per_block_outputs: tuple[int | float | Fraction, ...]


def _finite_output(value: object, rho: Fraction) -> int | float | Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, float, Fraction)):
        raise TypeError("Base output must be a finite int, float, or Fraction.")
    if isinstance(value, float) and not math.isfinite(value):
        raise ValueError("Base output must be finite; NaN/infinity is not a timeout.")
    # Preserve rational values exactly. Floating displays are a caller concern.
    if value < 0:
        value = 0
    elif value > rho:
        value = rho
    return value


def _run_block(program: Generator[int, int, object], coin_factory: CoinFactory,
               source_rng: random.Random, cap: int, rho: Fraction
               ) -> tuple[int | float | Fraction, int, int, bool]:
    if not isinstance(program, Generator):
        raise TypeError("program_factory must return an interactive generator.")
    coins: dict[int, Callable[[], int]] = {}
    flips = 0
    try:
        try:
            query = next(program)
        except StopIteration as stop:
            return _finite_output(stop.value, rho), 0, 0, False
        while True:
            if type(query) is not int or query < 0:
                raise ValueError("Each requested coin ID must be a nonnegative integer.")
            if flips == cap:
                return rho / 2, flips, len(coins), True
            if query not in coins:
                coin = coin_factory(source_rng)
                if not callable(coin):
                    raise TypeError("coin_factory must return a zero-argument flip callable.")
                coins[query] = coin
            flips += 1
            bit = coins[query]()
            if type(bit) is not int or bit not in (0, 1):
                raise ValueError("The coin source must return integer 0 or 1.")
            try:
                query = program.send(bit)
            except StopIteration as stop:
                return _finite_output(stop.value, rho), flips, len(coins), False
    finally:
        program.close()


def run_capped_median(schedule: MedianSchedule, program_factory: ProgramFactory,
                      coin_factory: CoinFactory, *, seed: int = 0) -> MedianResult:
    """Execute capped independent-block amplification.

    The program gets only its own RNG and returned bits, not the source RNG
    or a direct flip callable. Coin IDs are namespaced separately per block.
    Unused work is not reallocated. Factory exceptions propagate explicitly.
    """
    if not isinstance(schedule, MedianSchedule):
        raise TypeError("A MedianSchedule is required.")
    if type(seed) is not int:
        raise TypeError("seed must be an integer.")
    root = random.Random(seed)
    outputs: list[int | float | Fraction] = []
    work: list[int] = []
    timeout_count = coins_count = 0
    for _ in range(schedule.blocks):
        program_rng = random.Random(root.getrandbits(256))
        source_rng = random.Random(root.getrandbits(256))
        program = program_factory(schedule.base_expected_budget, program_rng)
        result, flips, coins, timeout = _run_block(
            program, coin_factory, source_rng, schedule.per_block_cap, schedule.rho)
        outputs.append(result)
        work.append(flips)
        timeout_count += int(timeout)
        coins_count += coins
    total = sum(work)
    if total > schedule.total_budget:
        raise AssertionError("Internal error: physical-flip budget exceeded.")
    estimate = sorted(outputs)[schedule.blocks // 2]
    return MedianResult(estimate, total, coins_count,
                        schedule.blocks - timeout_count, timeout_count,
                        tuple(work), tuple(outputs))
