"""Distribution-blind expected-budget calibration.

Work means Bernoulli observations, not arithmetic operations or random bits.
The pilot and production calls must be IID and independent across calls.
Value and work WITHIN a call may be arbitrarily dependent.
There is no deterministic bound on total work.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import ceil, floor, isfinite, log, log2
from numbers import Integral
from typing import Callable, Protocol
import numpy as np
from threshold import Term, LEVEL_P, R, coupled_increment

class Draw(Protocol):
    def __call__(self) -> tuple[float, int]: ...

@dataclass(frozen=True)
class Result:
    value: float
    work: int
    pilot_calls: int
    production_calls: int

def calibrate(draw: Draw, cap: int, rng: np.random.Generator) -> Result:
    """Return a mean with E[work]=4*cap-c and variance=v*c/cap.

    Here c=E[per-call work]>0 and v=Var[per-call value]. Neither is input.
    Each call must have integer work in [0,cap] and finite output.
    The assertion that c>0 is a model assumption, not testable by this code.
    """
    if not isinstance(cap, Integral) or not 1 <= cap < 2**63:
        raise ValueError('cap must be a positive integer smaller than 2**63')
    def checked_draw() -> tuple[float, int]:
        y, w = draw()
        if not isfinite(y) or not isinstance(w, Integral) or not 0 <= w <= cap:
            raise ValueError('Invalid draw: require finite value and integer work in [0,cap]')
        return float(y), int(w)
    successes = calls = work = 0
    while successes < 2:
        _, w = checked_draw()
        calls += 1
        work += w
        # Exact Bernoulli(w/cap) for integer work; independent fresh randomness.
        successes += int(int(rng.integers(0, cap)) < w)
    m = calls - 1
    total = 0.0
    for _ in range(m):
        y, w = checked_draw()
        total += y
        work += w
    return Result(total / m, work, calls, m)

def draw_capped_term(new_coin: Callable[[], Callable[[int], int]],
                     level: int, rng: np.random.Generator) -> tuple[float, int]:
    """new_coin supplies a fresh coin's observation-count callback.

    The algorithm never receives the coin's latent probability or magnitude.
    A callback called with k returns successes in k new observations of that coin.
    """
    if not isinstance(level, int) or level < 0:
        raise ValueError('level must be a nonnegative integer')
    j = int(rng.geometric(LEVEL_P)) - 1
    if j > level:
        return 0.0, 0
    delta, work = coupled_increment(j, new_coin())
    return delta / (LEVEL_P * R**j), work

def estimate_budget(new_coin: Callable[[], Callable[[int], int]],
                    budget: float, rng: np.random.Generator) -> Result:
    """One estimate using only an expected observation budget, no margin law.

    Guarantee is E[work] <= budget, not work <= budget on each execution.
    No numerical confidence interval is produced without further information.
    """
    if not isfinite(budget) or budget < 1:
        raise ValueError('budget must be finite and >= 1')
    if budget < 4:
        return Result(0.5, 0, 0, 0)
    level = int(floor(log2(budget / 4)))
    if level >= 63:
        raise ValueError('Reference implementation supports caps smaller than 2**63')
    cap = 1 << level
    # Protect the budget against floating-point log rounding near powers of two.
    while 4 * cap > budget:
        level -= 1
        cap >>= 1
    return calibrate(lambda: draw_capped_term(new_coin, level, rng), cap, rng)


def estimate_confidence(new_coin: Callable[[], Callable[[int], int]],
                        budget: float, delta: float,
                        rng: np.random.Generator) -> Result:
    """Median of independent calibrated groups, using only budget and delta.

    This is a distribution-wise risk guarantee, not a computable confidence
    interval. The asserted total budget holds in expectation only. All calls
    returned by new_coin must implement fresh independent latent coins.
    """
    if not isfinite(budget) or budget < 1:
        raise ValueError('budget must be finite and >= 1')
    if not isfinite(delta) or not 0 < delta <= 0.25:
        raise ValueError('delta must lie in (0, 1/4]')
    k = int(ceil((32.0 / 9.0) * log(1.0 / delta)))
    if k % 2 == 0:
        k += 1
    group_budget = budget / k
    if group_budget < 4:
        return Result(0.5, 0, 0, 0)
    groups = [estimate_budget(new_coin, group_budget, rng) for _ in range(k)]
    return Result(float(np.median([g.value for g in groups])),
                  sum(g.work for g in groups),
                  sum(g.pilot_calls for g in groups),
                  sum(g.production_calls for g in groups))
