#!/usr/bin/env python3
"""Independent compact conic dual and exact Bellman feasibility repair.

Run with the round-three dependency directory on PYTHONPATH if needed.
The numerical solver selects four priors. Those priors are repaired to
exact rational rarity-feasible points. An independent backward recursion
then constructs rational feasible Bellman potentials and a work price.
Only that verified certificate is called a lower bound.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import importlib.util
import json
import math
from pathlib import Path
import sys
import time

import cvxpy as cp
import numpy as np
from scipy.stats import binom

from verify_finite_dual import (
    adaptive_squared_lower, children_sum, exact_latent_rewards, exact_kernel,
    fraction_text, rational, sqrt_lower_decimal, states_for, verify,
)


class CompactDual:
    def __init__(self, gaps, weights, rho, cap, genie=False):
        self.gaps = np.asarray(gaps, dtype=float)
        self.weights = np.asarray(weights, dtype=float)
        self.rho = float(rho)
        self.cap = int(cap)
        self.states = states_for(cap)
        self.index = {state: i for i, state in enumerate(self.states)}
        depth = np.array([s[0] for s in self.states])
        heads = np.array([s[1] for s in self.states])
        minus = binom.pmf(heads[None, :], depth[None, :],
                         0.5 - self.gaps[:, None])
        plus = binom.pmf(heads[None, :], depth[None, :],
                        0.5 + self.gaps[:, None])
        difference = plus - minus
        null = self.weights @ minus
        size = len(self.gaps)
        self.signal_mass = cp.Variable(nonneg=True, name="signal_mass")
        self.high_mass = cp.Variable(size, nonneg=True, name="high_mass")
        self.low_mass = cp.Variable(size, nonneg=True, name="low_mass")
        self.variance_prior = cp.Variable(size, nonneg=True, name="variance_prior")
        self.work_price = cp.Variable(nonneg=True, name="work_price")
        self.work_mass = cp.Variable(size, nonneg=True, name="work_mass")
        self.potential = cp.Variable(len(self.states), nonneg=True, name="potential")
        self.budget = cp.Parameter(nonneg=True, name="budget")
        s, eta = self.signal_mass, self.work_price
        uh, ul, qv, ew = (self.high_mass, self.low_mass,
                         self.variance_prior, self.work_mass)
        constraints = [
            uh <= s, ul <= s,
            self.weights @ uh <= self.rho * s,
            self.weights @ ul <= self.rho * s,
            qv <= 1, self.weights @ qv <= self.rho,
            ew <= eta, self.weights @ ew <= self.rho * eta,
            self.potential[0] == 0,
        ]
        signal = difference.T @ cp.multiply(self.weights, uh - ul)
        variance = null + difference.T @ cp.multiply(self.weights, qv)
        work = eta * null + difference.T @ cp.multiply(self.weights, ew)
        x = self.potential
        constraints.append(cp.SOC(variance[1:] + x[1:],
                           cp.vstack([signal[1:], variance[1:] - x[1:]]),
                           axis=0))
        if genie:
            plus_latent = cp.Variable(size, nonneg=True, name="positive_latent_perspective")
            minus_latent = cp.Variable(size, nonneg=True, name="negative_latent_perspective")
            contrast = uh - ul
            constraints.append(cp.SOC(qv + plus_latent,
                cp.vstack([2 * contrast, qv - plus_latent]), axis=0))
            constraints.append(cp.SOC(1 - qv + minus_latent,
                cp.vstack([2 * contrast, 1 - qv - minus_latent]), axis=0))
            terminal = np.array([n == cap for n, _ in self.states])
            latent_reward = (plus[:, terminal].T @ cp.multiply(self.weights, plus_latent)
                             + minus[:, terminal].T @ cp.multiply(self.weights, minus_latent)) / 4
            constraints.append(x[terminal] >= latent_reward)
        for i, (n, k) in enumerate(self.states):
            if n == cap:
                continue
            rhs = ((n + 1 - k) / (n + 1) * x[self.index[(n + 1, k)]]
                   + (k + 1) / (n + 1) * x[self.index[(n + 1, k + 1)]])
            constraints.append(x[i] + work[i] >= rhs)
        objective = (self.weights @ (uh - ul) / self.rho
                     - cp.square(s) - self.budget * eta)
        self.constraints = constraints
        self.problem = cp.Problem(cp.Maximize(objective), constraints)
        assert self.problem.is_dcp()

    def solve(self, budget):
        self.budget.value = float(budget)
        self.problem.solve(solver="CLARABEL", verbose=False, warm_start=True,
                           tol_gap_abs=1e-10, tol_gap_rel=1e-9,
                           tol_feas=1e-10, max_iter=400)
        if self.problem.status not in (cp.OPTIMAL, cp.OPTIMAL_INACCURATE):
            raise RuntimeError(self.problem.status)
        s = float(self.signal_mass.value)
        eta = float(self.work_price.value)
        if s > 1e-12:
            high = np.asarray(self.high_mass.value) / s
            low = np.asarray(self.low_mass.value) / s
        else:
            high = np.full_like(self.gaps, self.rho)
            low = np.zeros_like(self.gaps)
        qv = np.asarray(self.variance_prior.value)
        qw = (np.asarray(self.work_mass.value) / eta
              if eta > 1e-14 else np.full_like(self.gaps, self.rho / 2))
        return {
            "status": self.problem.status,
            "raw_dual_normalized_objective": float(self.problem.value),
            "raw_dual_rms": self.rho * math.sqrt(max(0, self.problem.value)),
            "max_constraint_violation": max(
                float(np.max(np.asarray(c.violation()))) for c in self.constraints),
            "priors": {"high": high, "low": low, "variance": qv, "work": qw},
        }


def repair_prior(values, weights, rho, regularize=False, denominator=10**12):
    """Return exact rationals satisfying every rarity inequality."""
    prior = [Fraction(min(denominator, max(0, int(round(float(x) * denominator)))),
                      denominator) for x in values]
    mass = sum(w * q for w, q in zip(weights, prior))
    if mass > rho:
        prior = [q * rho / mass for q in prior]
    if regularize:
        eps = Fraction(1, 10**8)
        prior = [(1 - eps) * q + eps * rho / 2 for q in prior]
    assert all(0 <= q <= 1 for q in prior)
    assert sum(w * q for w, q in zip(weights, prior)) <= rho
    return prior


def float_bellman_price(reward, work, states, index):
    """Locate a price numerically; this result is not yet a certificate."""
    def residual(price):
        values = np.zeros(len(states))
        for i in range(len(states) - 1, 0, -1):
            n, k = states[i]
            if n == states[-1][0]:
                values[i] = reward[i]
            else:
                onward = ((n + 1 - k) / (n + 1) * values[index[(n + 1, k)]]
                          + (k + 1) / (n + 1) * values[index[(n + 1, k + 1)]])
                values[i] = max(reward[i], onward - price * work[i])
        return values[index[(1, 0)]] + values[index[(1, 1)]] - price

    low, high = 0.0, max(float(np.sum(reward)), 1e-15)
    while residual(high) > 0:
        high *= 2
    for _ in range(70):
        middle = (low + high) / 2
        if residual(middle) <= 0:
            high = middle
        else:
            low = middle
    return high


def dyadic_ceiling(value, bits):
    value = Fraction(value)
    denominator = 1 << bits
    numerator = -((-value.numerator * denominator) // value.denominator)
    return Fraction(numerator, denominator)


def build_certificate(gaps, weights, rho, budget, cap, priors, bits=96,
                      genie=False, full_genie=False):
    if genie and full_genie:
        raise ValueError("Choose either midpoint or four-prior genie mode")
    gaps = list(map(rational, gaps))
    weights = list(map(rational, weights))
    rho, budget = rational(rho), rational(budget)
    repaired = {
        name: repair_prior(priors[name], weights, rho,
                           regularize=name in ("variance", "work"))
        for name in ("low", "high", "variance", "work")
    }
    gap = sum(w * (h - l) for w, h, l in zip(
        weights, repaired["high"], repaired["low"]))
    if gap < 0:
        repaired["high"], repaired["low"] = repaired["low"], repaired["high"]
        gap = -gap
    if genie:
        # Map four priors to one symmetric pair. Every coordinate operation is
        # exact and Q_rho is convex, so this preserves all rarity constraints.
        repaired["high"] = [(h + v + w) / 3 for h, v, w in zip(
            repaired["high"], repaired["variance"], repaired["work"])]
        repaired["low"] = [(l + v + w) / 3 for l, v, w in zip(
            repaired["low"], repaired["variance"], repaired["work"])]
        midpoint = [(h + l) / 2 for h, l in zip(
            repaired["high"], repaired["low"])]
        repaired["variance"] = midpoint
        repaired["work"] = midpoint
        gap /= 3
    kernels = {name: exact_kernel(gaps, weights, prior, cap)
               for name, prior in repaired.items()}
    states = states_for(cap)
    index = {state: i for i, state in enumerate(states)}
    rewards = []
    for kh, kl, kv in zip(kernels["high"], kernels["low"], kernels["variance"]):
        delta = kh - kl
        if kv == 0:
            assert delta == 0
            rewards.append(Fraction(0))
        else:
            rewards.append(delta**2 / kv)
    if genie or full_genie:
        genie_rewards = exact_latent_rewards(
            gaps, weights, repaired["low"], repaired["high"],
            repaired["variance"], cap)
        for i, (n, _) in enumerate(states):
            if n == cap:
                rewards[i] = genie_rewards[i]
    suggested = float_bellman_price(
        np.array(list(map(float, rewards))),
        np.array(list(map(float, kernels["work"]))), states, index)
    price = (rational(math.nextafter(suggested, math.inf))
             * Fraction(100000001, 100000000) + Fraction(1, 10**30))
    for attempt in range(20):
        values = [Fraction(0)] * len(states)
        for i in range(len(states) - 1, 0, -1):
            n, k = states[i]
            required = rewards[i]
            if n < cap:
                required = max(required, children_sum(values, index, n, k)
                               - price * kernels["work"][i])
            values[i] = dyadic_ceiling(max(required, 0), bits)
        root_slack = price - children_sum(values, index, 0, 0)
        if root_slack >= 0:
            break
        price = price * Fraction(1000001, 1000000) + Fraction(1, 1 << bits)
    else:
        raise RuntimeError("Could not repair Bellman root inequality")
    lower = (adaptive_squared_lower(gap, budget, price) if genie
             else gap**2 / (4 + budget * price))
    certificate = {
        "description": (
            "Exact rational four-prior Bellman certificate with a latent-genie terminal reward, bounding the unrestricted flow program. Mapping to a midpoint pair also certifies an unrestricted adaptive minimax RMS lower bound."
            if full_genie else
            "Exact rational midpoint Bellman certificate with a latent-genie terminal reward. The Bayes-affinity theorem converts it to an unrestricted adaptive minimax RMS lower bound."
            if genie else
            "Exact rational Bellman dual certificate for the finite-cap flow program; not an unscaled lower bound on unrestricted minimax risk."),
        "certificate_kind": ("uncapped_four_prior_genie" if full_genie else
                             "uncapped_midpoint_genie" if genie else "finite_cap"),
        "gaps": list(map(fraction_text, gaps)),
        "weights": list(map(fraction_text, weights)),
        "rho": fraction_text(rho), "budget": fraction_text(budget), "cap": cap,
        "priors": {name: list(map(fraction_text, q)) for name, q in repaired.items()},
        "information_work_price": fraction_text(price),
        "information_potentials": list(map(fraction_text, values)),
        "certified_squared_lower_bound": fraction_text(lower),
        "certified_rms_lower_bound_decimal": sqrt_lower_decimal(lower),
        "repair": {"dyadic_precision_bits": bits,
                   "backward_passes": attempt + 1,
                   "reference_regularization": "1/100000000",
                   "float_bisection_price": suggested},
    }
    if full_genie:
        adaptive = adaptive_squared_lower(gap / 3, budget, price)
        certificate["certified_adaptive_squared_lower_bound"] = fraction_text(adaptive)
        certificate["certified_adaptive_rms_lower_bound_decimal"] = sqrt_lower_decimal(adaptive)
    verification = verify(certificate)
    return certificate, verification


def load_primal():
    path = Path(__file__).with_name("inherited_flow_primal.py")
    spec = importlib.util.spec_from_file_location("round3_primal", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.FlowProgram


def run(output_dir, cap=8):
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    Primal = load_primal()
    cases = [
        ("one_gap", [0.25], [1.0], 0.1),
        ("three_scales", [0.4, 0.2, 0.08], [0.75, 0.20, 0.05], 0.1),
        ("rare_hard_atom", [0.45, 0.08], [0.99, 0.01], 0.1),
        ("perfect_labels", [0.5], [1.0], 0.1),
    ]
    summaries = []
    for name, gaps, weights, rho in cases:
        chosen_cap = 1 if name == "perfect_labels" else cap
        dual = CompactDual(gaps, weights, rho, chosen_cap)
        primal = Primal(gaps, weights, rho, chosen_cap)
        for budget in (100.0, 1000.0):
            started = time.monotonic()
            raw = dual.solve(budget)
            certificate, verification = build_certificate(
                gaps, weights, rho, budget, chosen_cap, raw["priors"])
            filename = f"{name}_N{chosen_cap}_B{int(budget)}.json"
            (output_dir / filename).write_text(json.dumps(certificate, indent=2) + "\n")
            upper = primal.solve(budget)
            certified = float(rational(certificate["certified_squared_lower_bound"]))
            row = {
                "case": name, "cap": chosen_cap, "budget": budget,
                "dual_status": raw["status"],
                "raw_dual_rms": raw["raw_dual_rms"],
                "dual_max_constraint_violation": raw["max_constraint_violation"],
                "certified_lower_rms_decimal":
                    certificate["certified_rms_lower_bound_decimal"],
                "primal_program_rms": upper["program_rms"],
                "reconstructed_upper_rms": upper["reconstructed_rms_bound"],
                "relative_certificate_gap":
                    upper["reconstructed_rms_bound"] / math.sqrt(certified) - 1,
                "certificate": filename,
                "exact_verification": verification,
                "elapsed_seconds": time.monotonic() - started,
            }
            assert math.sqrt(certified) <= upper["reconstructed_rms_bound"] + 1e-8
            summaries.append(row)
            print(json.dumps({key: row[key] for key in (
                "case", "cap", "budget", "certified_lower_rms_decimal",
                "reconstructed_upper_rms", "relative_certificate_gap",
                "elapsed_seconds")}), flush=True)
    payload = {
        "scope": "Independent finite-atom conic dual, followed by exact rational Bellman repair and standard-library verification. Lower bounds concern the cap-N convex program.",
        "cvxpy_version": cp.__version__, "results": summaries,
    }
    (output_dir / "dual_comparison_results.json").write_text(
        json.dumps(payload, indent=2) + "\n")
    return payload


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", default=str(Path(__file__).with_name("certificates")))
    parser.add_argument("--cap", type=int, default=8)
    args = parser.parse_args()
    run(args.output_dir, args.cap)
