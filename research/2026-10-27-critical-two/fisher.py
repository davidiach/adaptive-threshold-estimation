"""Finite-horizon, floating-point Fisher/work diagnostic for one hidden coin.

This is neither an all-population converse nor a certified numerical bound.
The policy is chosen at eta=0 and is then held fixed under local perturbation.
No Monte Carlo, data fitting, or random seed is used.
"""
from __future__ import annotations

import hashlib
import json
import platform
from pathlib import Path
import time

import numpy as np


def prediction_tables(k: int, horizon: int, a: float = 0.25, c: float = 1 / 16):
    index = np.arange(k + 1, dtype=np.float64)
    gaps = a * np.exp2(-index)
    masses = gaps**2 / np.sum(gaps**2)
    q = c * np.exp2(2 * (index - k))
    rho = float(np.dot(masses, q))
    coin_p = np.concatenate((0.5 - gaps, 0.5 + gaps))
    weights = np.concatenate((masses * (1 - q), masses * q))
    component_score = np.concatenate((-q / (1 - q), np.ones(k + 1)))
    log_weights = np.log(weights)
    log_p = np.log(coin_p)
    log_t = np.log1p(-coin_p)
    size = horizon * (horizon + 1) // 2
    predictions = np.empty(size, dtype=np.float64)
    information = np.empty(size, dtype=np.float64)
    for n in range(horizon):
        heads = np.arange(n + 1, dtype=np.float64)[:, None]
        log_terms = log_weights + heads * log_p + (n - heads) * log_t
        log_terms -= np.max(log_terms, axis=1, keepdims=True)
        posterior = np.exp(log_terms)
        posterior /= np.sum(posterior, axis=1, keepdims=True)
        predicted_p = posterior @ coin_p
        score = posterior @ component_score
        derivative_p = posterior @ (component_score * coin_p) - predicted_p * score
        begin = n * (n + 1) // 2
        predictions[begin:begin + n + 1] = predicted_p
        information[begin:begin + n + 1] = derivative_p**2 / (predicted_p * (1 - predicted_p))
    return predictions, information, rho, gaps, masses, q


def bellman(predictions, information, horizon, penalty, extract=False):
    """Maximize Fisher information minus penalty times expected observations."""
    values = np.zeros(horizon + 1)
    if extract:
        costs = np.zeros(horizon + 1)
        infos = np.zeros(horizon + 1)
        policy = np.zeros(len(predictions), dtype=np.bool_)
    for n in range(horizon - 1, -1, -1):
        begin = n * (n + 1) // 2
        p = predictions[begin:begin + n + 1]
        step_info = information[begin:begin + n + 1]
        advantage = step_info - penalty + (1 - p) * values[:n + 1] + p * values[1:n + 2]
        go = advantage > 0
        values = np.maximum(advantage, 0)
        if extract:
            costs = np.where(go, 1 + (1 - p) * costs[:n + 1] + p * costs[1:n + 2], 0)
            infos = np.where(go, step_info + (1 - p) * infos[:n + 1] + p * infos[1:n + 2], 0)
            policy[begin:begin + n + 1] = go
    if not extract:
        return float(values[0])
    return {
        "root_objective": float(values[0]),
        "expected_work": float(costs[0]),
        "fisher_information": float(infos[0]),
        "policy_continuation_nodes": int(np.sum(policy)),
        "policy_sha256": hashlib.sha256(np.packbits(policy).tobytes()).hexdigest(),
    }


def run_case(k, horizon):
    started = time.perf_counter()
    p, information, rho, gaps, masses, q = prediction_tables(k, horizon)
    lower = 0.0
    upper = float(np.max(information))
    # A finite stopping policy's ratio is a nonnegative weighted average of
    # conditional per-observation information, hence max(information) brackets it.
    for _ in range(44):
        midpoint = (lower + upper) / 2
        if bellman(p, information, horizon, midpoint) > 0:
            lower = midpoint
        else:
            upper = midpoint
    # Move slightly into the continuation region to avoid a rounded zero at root.
    penalty = lower * (1 - 1e-9)
    result = bellman(p, information, horizon, penalty, extract=True)
    work = result["expected_work"]
    info = result["fisher_information"]
    if not work > 0:
        raise ArithmeticError("Extracted policy has zero work")
    ratio = info / work
    identity_error = abs(result["root_objective"] - (info - penalty * work))
    if identity_error > 1e-9 * max(1.0, abs(info)):
        raise ArithmeticError("Bellman information/work identity failed")
    if ratio < lower * (1 - 1e-7) or ratio > upper * (1 + 1e-7):
        raise ArithmeticError("Extracted policy disagrees with numerical ratio bracket")
    a = 0.25
    return {
        "K": k, "atom_count": k + 1, "a": a, "c": 1 / 16,
        "horizon": horizon, "rho": rho,
        "gaps": gaps.tolist(), "masses": masses.tolist(), "baseline_q": q.tolist(),
        "parameter_path": "q_eta=(1+eta)*baseline_q; policy fixed at eta=0",
        "per_flip_information_at_root": float(information[0]),
        "numerical_ratio_search_lower": lower,
        "numerical_ratio_search_upper": upper,
        "extracted_policy_penalty": penalty,
        "fisher_per_expected_work": ratio,
        "ratio_to_a_squared_rho_over_K": ratio / (a * a * rho / k),
        "ratio_to_a_squared_rho_over_atom_count": ratio / (a * a * rho / (k + 1)),
        "bellman_identity_absolute_residual": identity_error,
        "table_storage_bytes": int(p.nbytes + information.nbytes),
        "elapsed_seconds": time.perf_counter() - started,
        **result,
    }


def sanity_checks():
    # Independent central differences of finite-prefix mixture likelihoods.
    k = 3
    atom = np.arange(k + 1, dtype=np.float64)
    gaps = 0.25 * np.exp2(-atom)
    masses = gaps**2 / np.sum(gaps**2)
    q = (1 / 16) * np.exp2(2 * (atom - k))
    coin_p = np.concatenate((0.5 - gaps, 0.5 + gaps))
    predictions, information, *_ = prediction_tables(k, 65)
    residuals = []
    for n in (0, 1, 7, 64):
        for heads in sorted({0, n // 2, n}):
            likelihood = coin_p**heads * (1 - coin_p)**(n - heads)

            def predict(eta):
                weight = np.concatenate((masses * (1 - (1 + eta) * q), masses * (1 + eta) * q))
                return np.dot(weight * likelihood, coin_p) / np.dot(weight, likelihood)

            step = 1e-4
            derivative = (predict(step) - predict(-step)) / (2 * step)
            offset = n * (n + 1) // 2 + heads
            p = predictions[offset]
            finite_difference_info = derivative**2 / (p * (1 - p))
            residual = abs(finite_difference_info - information[offset])
            if residual > 1e-7 * max(1e-12, information[offset]):
                raise ArithmeticError("Finite-difference predictive Fisher check failed")
            residuals.append(residual)
    # Exhaust all 2^6 count-state stop/continue policies at horizon three.
    horizon = 3
    p, information, *_ = prediction_tables(2, horizon)
    best_ratio = 0.0
    for bits in range(1 << len(p)):
        work = np.zeros(horizon + 1)
        info = np.zeros(horizon + 1)
        for n in range(horizon - 1, -1, -1):
            begin = n * (n + 1) // 2
            pr = p[begin:begin + n + 1]
            go = np.array([(bits >> (begin + h)) & 1 for h in range(n + 1)], dtype=bool)
            work = np.where(go, 1 + (1 - pr) * work[:n + 1] + pr * work[1:n + 2], 0)
            info = np.where(go, information[begin:begin + n + 1] +
                            (1 - pr) * info[:n + 1] + pr * info[1:n + 2], 0)
        if work[0] > 0:
            best_ratio = max(best_ratio, float(info[0] / work[0]))
    checked = run_case(2, horizon)["fisher_per_expected_work"]
    if abs(best_ratio - checked) > 1e-12:
        raise ArithmeticError("Exhaustive three-flip policy comparison failed")
    return {"finite_difference_states": len(residuals),
            "maximum_finite_difference_information_residual": max(residuals),
            "exhaustive_horizon": horizon, "exhaustive_policy_count": 1 << len(p),
            "exhaustive_ratio": best_ratio, "bellman_ratio": checked}


def main():
    checks = sanity_checks()
    cases = []
    for k in (2, 3, 4):
        for horizon in (256, 512, 1024):
            result = run_case(k, horizon)
            cases.append(result)
            print(f"K={k} N={horizon}: I/W={result['fisher_per_expected_work']:.8g}; "
                  f"normalized={result['ratio_to_a_squared_rho_over_K']:.6g}", flush=True)
    record = {
        "status": "numerical evidence",
        "scope": "One-coin stopping policies using (flip count, head count), at finite horizon",
        "not_claimed": ["certified floating-point optimum", "unbounded-horizon optimum",
                        "all-population minimax lower bound", "uniform-in-K theorem"],
        "method": "Posterior prediction and score; backwards Bellman ratio search; exact policy cost/info recursions in float64",
        "seeds": None,
        "rarity_caveat": "rho records baseline mean. The two-sided local eta path lies in Q_(2rho) near zero; positive eta is outside Q_rho itself.",
        "python": platform.python_version(), "numpy": np.__version__,
        "bisection_iterations": 44,
        "rounding_controls": "log-sum-exp stabilization and algebraic identity checks; no interval enclosure",
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "sanity_checks": checks,
        "cases": cases,
    }
    Path(__file__).with_name("fisher.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
