"""Geometric fallback for hard-budget RMS.

Conditional paper theorem: independent base runs satisfy E[T] <= b and
RMS <= C*f(b), with f(b/c) <= sqrt(c)*f(b), f(1/2)=upper and C>=1/2.
At each deterministic authorized allowance B>=4, RMS <= sqrt(32)*C*f(B).
The driver enforces observation caps, not the statistical assumptions.

Generators yield nonnegative local coin IDs and receive integer bits.
Revisits persist within a stage; namespaces and seeds are separate across
stages. Caller callbacks are trusted. This is not a CPU limit, a sandbox,
or a proof of Python/PRNG independence. Random stopping does not inherit
the deterministic-budget RMS guarantee.

Apache-2.0. Extracted from the 30 October 2026 round-three contribution.
"""
from __future__ import annotations

from collections.abc import Callable, Generator, Mapping
from dataclasses import dataclass
from fractions import Fraction
import math
import random
from typing import Union

Exact = Union[int, str, Fraction]
Number = Union[int, float, Fraction]
ProgramFactory = Callable[[int, random.Random], Generator[int, int, object]]
CoinFactory = Callable[[random.Random], Callable[[], int]]
MAX_BITS = 4096
SCHEMA = 'ate-geometric-fallback-v1'


def _exact(x: Exact) -> Fraction:
    if isinstance(x, bool) or not isinstance(x, (int, str, Fraction)):
        raise TypeError('Use an int, Fraction, or exact rational/decimal string.')
    try:
        q = Fraction(x)
    except (ValueError, ZeroDivisionError, OverflowError) as exc:
        raise ValueError('Invalid rational input.') from exc
    if max(q.numerator.bit_length(), q.denominator.bit_length()) > MAX_BITS:
        raise ValueError('Input exceeds rational bit limit.')
    return q


def _budget(n: int) -> int:
    if type(n) is not int or n < 0:
        raise ValueError('Authorized budget must be a nonnegative integer.')
    if n.bit_length() > MAX_BITS:
        raise ValueError('Budget exceeds bit limit.')
    return n


@dataclass(frozen=True)
class Stage:
    index: int
    expected_budget: int
    flip_cap: int
    checkpoint: int


def stage(index: int) -> Stage:
    if type(index) is not int or not 0 <= index < MAX_BITS - 2:
        raise ValueError('Stage index is out of range.')
    b = 1 << index
    return Stage(index, b, 4*b, 4*(2*b-1))


def plan(total_budget: int) -> tuple[Stage, ...]:
    n = _budget(total_budget)
    count = max(0, (n//4 + 1).bit_length() - 1)
    return tuple(stage(j) for j in range(count))


def schedule_record(total_budget: int) -> dict[str, object]:
    stages = plan(total_budget)
    return {
        'schema': SCHEMA,
        'scope': 'hard_flip_caps_only_statistical_contract_is_external',
        'total_budget': total_budget,
        'reserved_budget': sum(s.flip_cap for s in stages),
        'caps': [s.flip_cap for s in stages],
        'expected_budgets': [s.expected_budget for s in stages],
        'checkpoints': [s.checkpoint for s in stages],
        'timeout_probability_bound': '1/4',
        'rms_multiplier_squared': '32',
        'clock': 'deterministic_authorized_allowance_not_random_actual_spend',
    }


def _same_types(a: object, b: object) -> bool:
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(_same_types(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(_same_types(x, y) for x, y in zip(a, b))
    return a == b


def verify_schedule(record: Mapping[str, object], *, total_budget: int) -> bool:
    if not isinstance(record, Mapping):
        return False
    try:
        expected = schedule_record(total_budget)
    except (ValueError, TypeError):
        return False
    return _same_types(dict(record), expected)


def _clip(value: object, upper: Fraction) -> Number:
    if isinstance(value, bool) or not isinstance(value, (int, float, Fraction)):
        raise TypeError('Estimator must return a finite int, float, or Fraction.')
    if isinstance(value, float) and not math.isfinite(value):
        raise ValueError('Estimator returned a nonfinite value.')
    return max(Fraction(0), min(upper, value))


def _execute(program: Generator, coins: CoinFactory, source_rng: random.Random,
             cap: int) -> tuple[object, int, int, bool]:
    if not isinstance(program, Generator):
        raise TypeError('The factory must return an interactive generator.')
    sources: dict[int, Callable[[], int]] = {}
    used = 0
    try:
        try:
            query = next(program)
        except StopIteration as done:
            return done.value, 0, 0, False
        while True:
            if type(query) is not int or query < 0:
                raise ValueError('Coin IDs must be nonnegative integers.')
            if used == cap:
                return None, used, len(sources), True
            if query not in sources:
                source = coins(source_rng)
                if not callable(source):
                    raise TypeError('coin_factory must return a callable.')
                sources[query] = source
            used += 1
            bit = sources[query]()
            if type(bit) is not int or bit not in (0, 1):
                raise ValueError('A coin must return integer 0 or 1.')
            try:
                query = program.send(bit)
            except StopIteration as done:
                return done.value, used, len(sources), False
    finally:
        program.close()


@dataclass(frozen=True)
class StageRun:
    index: int
    flips: int
    created_coins: int
    timed_out: bool


@dataclass(frozen=True)
class RMSState:
    authorized_budget: int
    reserved_budget: int
    flips: int
    estimate: Number
    runs: tuple[StageRun, ...]


class RMSLadder:
    """Retain the last completed independent estimate; never reset on timeout.

    advance_to is cumulative: repeated calls do not rerun completed stages.
    A stage is launched only once its whole cap fits in the reservation ledger.
    No fresh work is done for the unused remainder of an allowance. Changing
    the schedule after examining outcomes is outside the RMS theorem.
    """
    def __init__(self, program_factory: ProgramFactory, coin_factory: CoinFactory,
                 *, upper: Exact = 1, seed: int = 0):
        self.upper = _exact(upper)
        if not 0 < self.upper <= 1:
            raise ValueError('upper must lie in (0,1].')
        if type(seed) is not int:
            raise TypeError('seed must be an integer.')
        if not callable(program_factory) or not callable(coin_factory):
            raise TypeError('Factories must be callable.')
        self._factory, self._coins = program_factory, coin_factory
        self._rng = random.Random(seed)
        self._estimate: Number = self.upper/2
        self._runs: list[StageRun] = []
        self._authorized = self._flips = self._reserved = 0
        self._failed = False

    def advance_to(self, total_budget: int) -> RMSState:
        n = _budget(total_budget)
        if self._failed:
            raise RuntimeError('A callback failed; this ladder is invalidated.')
        if n < self._authorized:
            raise ValueError('Cumulative authorized budget cannot decrease.')
        self._authorized = n
        for s in plan(n)[len(self._runs):]:
            prng = random.Random(self._rng.getrandbits(256))
            srng = random.Random(self._rng.getrandbits(256))
            try:
                output, used, made, timed_out = _execute(
                    self._factory(s.expected_budget, prng), self._coins, srng, s.flip_cap)
                if not timed_out:
                    self._estimate = _clip(output, self.upper)
            except BaseException:
                self._failed = True
                raise
            self._flips += used
            self._reserved += s.flip_cap
            self._runs.append(StageRun(s.index, used, made, timed_out))
        assert self._flips <= self._reserved <= n
        return RMSState(n, self._reserved, self._flips, self._estimate, tuple(self._runs))
