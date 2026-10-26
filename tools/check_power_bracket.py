"""Deterministic quadrature checks and alpha>=2 upper-bracket diagnostics.

No Monte Carlo, seeds, held-out data, or new minimax upper theorem are used.
The upper bracket is Proposition generalupper from the supplied note.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq

ROOT = Path(__file__).resolve().parents[1]


def error_bound(x: float, alpha: float) -> float:
    """E min(1,(nD^2)^-2), with x=n*a^2 and power-law D/a."""
    if x <= 1:
        return 1.0
    if alpha == 4:
        return x**-2 * (1 + 2 * math.log(x))
    return (4 * x**(-alpha / 2) - alpha * x**-2) / (4 - alpha)


def work_bound_scaled(x: float, alpha: float) -> float:
    """a^2 E min(n,(1+log_+(nD^2))/D^2)."""
    if x <= 1:
        return x
    if alpha == 2:
        logx = math.log(x)
        return 1 + logx + logx * logx / 2
    beta = alpha - 2
    q = x**(-beta / 2)
    return q + alpha * ((1 + math.log(x) - q) / beta - 2 * (1 - q) / beta**2)


def rho_at_cutoff(s: float, alpha: float) -> float:
    if alpha == 2:
        return s * s * (1 - 2 * math.log(s))
    return (alpha * s * s - 2 * s**alpha) / (alpha - 2)


def power_psi(x: float, rho: float, alpha: float) -> tuple[float, float]:
    logs = brentq(lambda z: rho_at_cutoff(math.exp(z), alpha) - rho, -100, 0)
    s = math.exp(logs)
    if x >= s:
        return rho, s
    middle = alpha * x * (s**(alpha - 1) - x**(alpha - 1)) / (alpha - 1)
    tail = (alpha * x * s * (-math.log(s)) if alpha == 2 else
            alpha * x * s * (1 - s**(alpha - 2)) / (alpha - 2))
    return x**alpha + middle + tail, s


def bracket(alpha: float, rho: float, a: float, exponent: int) -> dict:
    cap = 2**exponent
    budget = 4 * cap
    levels = np.exp2(np.arange(exponent + 1, dtype=float))
    err = np.array([error_bound(n * a*a, alpha) for n in levels])
    work = np.array([work_bound_scaled(n * a*a, alpha) / (a*a) for n in levels])
    best = None
    for start in range(exponent + 1):
        v = np.r_[rho + err[start], err[start + 1:] + err[start:-1]]
        b = np.r_[17 * work[start], 34 * work[start + 1:]]
        total = float(np.sqrt(v * b).sum())
        upper = math.sqrt(err[-1]**2 + total * total / cap)
        candidate = (upper, start, total)
        best = min(best, candidate) if best else candidate
    psi, cutoff = power_psi(1 / (a * math.sqrt(budget)), rho, alpha)
    return dict(alpha=alpha, rho=rho, a=a, budget=budget, cap=cap,
                best_start=2**best[1], bracket_unclipped=best[0],
                upper=min(rho / 2, best[0]), psi=psi,
                upper_over_psi=min(rho / 2, best[0]) / psi,
                cutoff_over_a=cutoff)


def main():
    checks = []
    for alpha in [2., 2.5, 3., 4., 6.]:
        for x in [.25, 1., 2., 16., 1024.]:
            split = min(1., 1 / math.sqrt(x))
            tolerance = dict(epsabs=1e-13, epsrel=1e-13)
            e = quad(lambda u: alpha * u**(alpha - 1), 0, split, **tolerance)[0]
            m = x * e
            if split < 1:
                e += quad(lambda u: alpha * u**(alpha - 1) / (x*u*u)**2, split, 1, **tolerance)[0]
                m += quad(lambda u: alpha * u**(alpha - 3) * (1 + math.log(x*u*u)), split, 1, **tolerance)[0]
            assert math.isclose(e, error_bound(x, alpha), rel_tol=1e-10, abs_tol=1e-12)
            assert math.isclose(m, work_bound_scaled(x, alpha), rel_tol=1e-10, abs_tol=1e-12)
            checks.append(dict(alpha=alpha, x=x, error=e, work_scaled=m))
    rows = [bracket(alpha, rho, .25, exponent)
            for alpha in [2., 3., 4.] for rho in [.01, .0001, .000001]
            for exponent in [24, 36, 48]]
    output = dict(status="numerical evidence; deterministic quadrature", checks=checks, rows=rows)
    (ROOT / "results" / "power_bracket.json").write_text(json.dumps(output, indent=2) + "\n")
    print(f"Passed {len(checks)} analytic-formula quadrature checks; wrote {len(rows)} bracket cases.")
    for row in rows:
        if row['cap'] == 2**48:
            print(f"alpha={row['alpha']:g} rho={row['rho']:g} upper/Psi={row['upper_over_psi']:.3f}")


if __name__ == "__main__":
    main()
