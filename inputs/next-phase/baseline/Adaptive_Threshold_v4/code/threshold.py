"""Adaptive threshold estimators used in the accompanying manuscript.

All work counts are Bernoulli observations, not Python operations.  Sampling
binomial increments simulates exactly the observations at dyadic checkpoints.
The estimator can be negative or larger than one; clipping destroys its exact
unbiasedness.  A finite max_level deliberately introduces truncation bias.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import ceil, expm1, floor, isfinite, log, log2, sqrt
from typing import Callable
import numpy as np

R = 2.0 ** -0.5
LEVEL_P = 1.0 - R
K = 256.0

@dataclass(frozen=True)
class Term:
    value: float
    work: int
    level: int

def decision(heads: int, n: int, cap: int) -> int | None:
    """The capped classifier. A final tie is assigned to the negative sign."""
    if n == cap:
        return int(2 * heads > n)
    threshold = sqrt((1.0 + log(cap / n)) / n)
    centered = heads / n - 0.5
    return int(centered > 0.0) if abs(centered) > threshold else None

def coupled_increment(level: int, count_source: Callable[[int], int]) -> tuple[int, int]:
    """Simulate Delta_level using a common prefix; return increment and work.

    count_source(k) supplies the number of successes among k fresh observations
    of ONE fixed coin. It must not draw a different coin on successive calls.
    """
    if not isinstance(level, int) or level < 0:
        raise ValueError('level must be a nonnegative integer')
    cap = 1 << level
    other_cap = cap // 2
    z = None
    other = 0 if level == 0 else None
    heads = 0
    previous = 0
    n = 1
    while True:
        new_heads = int(count_source(n - previous))
        if not 0 <= new_heads <= n - previous:
            raise ValueError('count_source returned an invalid success count')
        heads += new_heads
        if z is None:
            z = decision(heads, n, cap)
        if other is None:
            other = decision(heads, n, other_cap)
        if z is not None and other is not None:
            return z - other, n
        previous = n
        n *= 2

def sample_term(p: float, rng: np.random.Generator, max_level: int | None = None) -> Term:
    """Draw the universal single-term estimator for a fixed latent probability.

    No level cap is applied unless requested. Very rare large levels can require
    substantial time: this is a mathematical reference implementation, not a
    production latency guarantee. Supplying a cap changes the estimator.
    """
    if not isfinite(p) or not 0 <= p <= 1:
        raise ValueError('p must lie in [0, 1]')
    if max_level is not None and (not isinstance(max_level, int) or max_level < 0):
        raise ValueError('max_level must be a nonnegative integer or None')
    if p == 0.5 and max_level is None:
        raise ValueError('The uncapped estimator excludes an exact threshold coin (p = 1/2)')
    j = int(rng.geometric(LEVEL_P)) - 1
    if max_level is not None and j > max_level:
        return Term(0.0, 0, j)
    delta, work = coupled_increment(j, lambda k: int(rng.binomial(k, p)))
    return Term(delta / (LEVEL_P * R**j), work, j)

def omega_power(h: float, alpha: float, a: float = 0.25) -> float:
    if not all(isfinite(x) for x in (h, alpha, a)) or h < 0 or alpha <= 0 or not 0 < a <= 0.5:
        raise ValueError('Require h >= 0, alpha > 0, 0 < a <= 1/2')
    if h == 0:
        return 0.0
    if h >= a:
        return 1.0
    u = h / a
    if alpha == 1.0:
        return u * (1.0 - log(u))
    # expm1 avoids cancellation close to the critical exponent.
    return u * (1.0 - expm1((alpha - 1.0) * log(u)) / (alpha - 1.0))

def omega_log(h: float, beta: float, a: float = 0.25) -> float:
    if not all(isfinite(x) for x in (h, beta, a)) or h < 0 or beta < 0 or not 0 < a <= 0.5:
        raise ValueError('Require h >= 0, beta >= 0, 0 < a <= 1/2')
    if h == 0:
        return 0.0
    if h >= a:
        return 1.0
    u = h / a
    ell = 1.0 - log(u)
    integral = log(ell) if beta == 1.0 else expm1((1.0 - beta) * log(ell)) / (1.0 - beta)
    return u * (1.0 + integral)

def budget_plan(budget: float, omega: Callable[[float], float]) -> tuple[int, int] | None:
    """Legacy v3 known-envelope allocation, retained for comparison only.

    Main v4 API: calibration.estimate_budget, which needs no omega.
    This legacy construction has expected work <= budget.

    omega must be the exact modulus of a known magnitude law or a certified
    stochastic-dominance envelope. An estimated omega is NOT sufficient for
    the stated guarantee. None means use the deterministic estimate 1/2.
    """
    if not isfinite(budget) or budget <= 0:
        raise ValueError('budget must be positive and finite')
    if budget < 2 * K:
        return None
    level = int(floor(log2(budget / (2 * K))))
    n = 1 << level
    h = 1.0 / sqrt(n)
    om = float(omega(h))
    if not 0 < om <= 1 + 1e-12:
        raise ValueError('omega(h) must lie in (0, 1]')
    a_h = om / h
    replicates = int(ceil(n / a_h))
    assert K * replicates * a_h <= budget * (1 + 1e-12)
    return level, replicates

if __name__ == '__main__':
    print('Conservative plan:', budget_plan(1_000_000, lambda h: omega_power(h, 1.0)))
