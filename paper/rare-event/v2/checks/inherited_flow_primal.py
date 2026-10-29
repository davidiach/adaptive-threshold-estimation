#!/usr/bin/env python3
# Local copy from round three; original implementation unchanged.
# Source: research_round3/checks/solve_flow_program.py, 28 October 2026.
# This copy makes the round-four source bundle independently reproducible.
# The new dual solvers and rational verifiers are separate adjacent files.
"""Finite-support implementation of the robust triangular-flow program.

The returned values are numerical upper-risk certificates for a finite cap,
not exact minimax risks. An independent forward recursion reconstructs an
observable stopping policy and recomputes its worst bias, variance and work.
Dependencies: NumPy, SciPy, CVXPY and a conic solver (Clarabel by default).
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy.sparse as sp
from scipy.stats import binom
import cvxpy as cp


def rarity_support(values, weights, rho):
    """Exact fractional-knapsack evaluation, up to floating-point arithmetic."""
    values = np.asarray(values, dtype=float)
    weights = np.asarray(weights, dtype=float)
    remaining = float(rho)
    total = 0.0
    for j in np.argsort(-values):
        if values[j] <= 0 or remaining <= 0:
            break
        mass = min(remaining, weights[j])
        total += mass * values[j]
        remaining -= mass
    return float(total)


def rarity_vertices(weights, rho):
    """All vertices of [0,1]^m intersected with weights @ q <= rho."""
    weights = np.asarray(weights, dtype=float)
    m = len(weights)
    points = {}
    for bits in itertools.product((0.0, 1.0), repeat=m):
        q = np.array(bits)
        if weights @ q <= rho + 1e-13:
            points[tuple(q)] = q
    for j in range(m):
        others = [i for i in range(m) if i != j]
        for bits in itertools.product((0.0, 1.0), repeat=m - 1):
            q = np.zeros(m)
            q[others] = bits
            q[j] = (rho - weights @ q) / weights[j]
            if -1e-12 <= q[j] <= 1 + 1e-12:
                q[j] = np.clip(q[j], 0, 1)
                points[tuple(np.round(q, 14))] = q
    return np.array(list(points.values()))


class FlowProgram:
    def __init__(self, gaps, weights, rho, cap):
        self.gaps = np.asarray(gaps, dtype=float)
        self.weights = np.asarray(weights, dtype=float)
        self.rho = float(rho)
        self.cap = int(cap)
        assert np.all((self.gaps > 0) & (self.gaps <= 0.5))
        assert np.all(self.weights > 0)
        assert abs(self.weights.sum() - 1) < 1e-12
        assert 0 < self.rho <= 0.25 and self.cap >= 1
        self.states = [(n, k) for n in range(self.cap + 1)
                       for k in range(n + 1)]
        self.index = {state: i for i, state in enumerate(self.states)}
        n = np.array([state[0] for state in self.states])
        k = np.array([state[1] for state in self.states])
        self.minus = binom.pmf(k[None, :], n[None, :],
                               0.5 - self.gaps[:, None])
        self.plus = binom.pmf(k[None, :], n[None, :],
                              0.5 + self.gaps[:, None])
        self.difference = self.plus - self.minus
        count = len(self.states)
        rows, cols, vals = [], [], []
        for i, (depth, heads) in enumerate(self.states):
            if depth == 0:
                continue
            if heads < depth:
                rows.append(i)
                cols.append(self.index[(depth - 1, heads)])
                vals.append((depth - heads) / depth)
            if heads > 0:
                rows.append(i)
                cols.append(self.index[(depth - 1, heads - 1)])
                vals.append(heads / depth)
        pascal = sp.csr_matrix((vals, (rows, cols)), shape=(count, count))

        # Work flows are divided by B; mean/output coefficients by rho;
        # second-moment coefficients by rho^2/B. This preserves z^2 <= a*t.
        self.a = cp.Variable(count, nonneg=True, name="stopping_flow")
        self.c = cp.Variable(count, nonneg=True, name="continuation_flow")
        self.z = cp.Variable(count, name="output_numerator")
        self.t = cp.Variable(count, nonneg=True, name="moment_epigraph")
        self.offset = cp.Variable(name="offset_over_rho")
        self.bias = cp.Variable(nonneg=True, name="bias_over_rho")
        self.variance = cp.Variable(nonneg=True, name="variance_times_B_over_rho2")
        self.inverse_budget = cp.Parameter(nonneg=True, name="inverse_budget")
        constraints = [
            self.a[0] == 0, self.z[0] == 0, self.t[0] == 0,
            self.a[1:] + self.c[1:] == (pascal @ self.c)[1:],
            self.c[n == self.cap] == 0,
            cp.SOC(self.a + self.t,
                   cp.vstack([2 * self.z, self.a - self.t]), axis=0),
        ]

        def support_epigraph(values, label):
            cutoff = cp.Variable(nonneg=True, name=label + "_cutoff")
            excess = cp.Variable(len(self.gaps), nonneg=True,
                                 name=label + "_excess")
            constraints.append(excess >= values - cutoff)
            return self.rho * cutoff + self.weights @ excess

        null_mean = self.weights @ (self.minus @ self.z)
        delta_mean = self.difference @ self.z
        constraints.extend([
            self.offset + null_mean + support_epigraph(
                delta_mean - 1 / self.rho, "positive_bias") <= self.bias,
            -self.offset - null_mean + support_epigraph(
                1 / self.rho - delta_mean, "negative_bias") <= self.bias,
            self.weights @ (self.minus @ self.t) + support_epigraph(
                self.difference @ self.t, "variance") <= self.variance,
            self.weights @ (self.minus @ self.c) + support_epigraph(
                self.difference @ self.c, "work") <= 1,
        ])
        self.constraints = constraints
        self.problem = cp.Problem(
            cp.Minimize(cp.square(self.bias) +
                        self.inverse_budget * self.variance), constraints)
        assert self.problem.is_dcp()

    def solve(self, budget, solver="CLARABEL"):
        budget = float(budget)
        assert budget > 0
        self.inverse_budget.value = 1 / budget
        options = dict(solver=solver, verbose=False, warm_start=True)
        if solver == "CLARABEL":
            options.update(tol_gap_abs=1e-10, tol_gap_rel=1e-9,
                           tol_feas=1e-10, max_iter=300)
        self.problem.solve(**options)
        if self.problem.status not in (cp.OPTIMAL, cp.OPTIMAL_INACCURATE):
            raise RuntimeError(f"Solver status: {self.problem.status}")
        value = max(0.0, float(self.problem.value))
        solved = {
            "status": self.problem.status,
            "cap": self.cap,
            "budget": budget,
            "rho": self.rho,
            "states": len(self.states),
            "program_rms": self.rho * math.sqrt(value),
            "program_bias_bound": self.rho * float(self.bias.value),
            "program_variance_bound": self.rho**2 * float(self.variance.value) / budget,
            "max_constraint_violation": max(
                float(np.max(np.asarray(con.violation())))
                for con in self.constraints),
        }
        arrays = {"a": np.maximum(self.a.value, 0),
                  "c": np.maximum(self.c.value, 0),
                  "z": np.asarray(self.z.value),
                  "offset": self.rho * float(self.offset.value)}
        solved.update(self.reconstruct_and_verify(arrays, budget))
        return solved

    def reconstruct_and_verify(self, arrays, budget):
        a, c, z = arrays["a"], arrays["c"], arrays["z"]
        root = float(c[0])
        if root <= 1e-12:
            bias = max(abs(arrays["offset"]),
                       abs(arrays["offset"] - self.rho))
            return {"reconstructed_rms_bound": bias,
                    "actual_worst_rms": bias, "actual_worst_work": 0.0,
                    "actual_bias_bound": bias, "actual_variance_bound": 0.0,
                    "poisson_intensity": 0.0, "probability_error": 0.0,
                    "flow_recursion_error": 0.0}
        gamma = np.divide(a, a + c, out=np.zeros_like(a), where=(a + c) > 0)
        gamma = np.clip(gamma, 0, 1)
        gamma[0] = 0
        for k in range(self.cap + 1):
            gamma[self.index[(self.cap, k)]] = 1
        outputs = np.zeros_like(z)
        # Negligible-flow leaves are assigned zero, then all errors are
        # independently recomputed. No unverified solver output is certified.
        keep = a > 1e-11
        outputs[keep] = self.rho * z[keep] / (budget * a[keep])
        outcomes = []
        max_probability_error = 0.0
        max_flow_error = 0.0
        for sign in (-1, 1):
            means, moments, works = [], [], []
            for d in self.gaps:
                p = 0.5 + sign * d
                reaches = np.zeros(len(self.states))
                reaches[0] = 1
                stopped = np.zeros_like(reaches)
                work = 0.0
                for i, (n, k) in enumerate(self.states):
                    stop = reaches[i] * gamma[i]
                    stopped[i] = stop
                    cont = reaches[i] - stop
                    if n < self.cap:
                        work += cont
                        reaches[self.index[(n + 1, k)]] += cont * (1 - p)
                        reaches[self.index[(n + 1, k + 1)]] += cont * p
                max_probability_error = max(max_probability_error,
                                            abs(stopped.sum() - 1))
                means.append(float(stopped @ outputs))
                moments.append(float(stopped @ (outputs**2)))
                works.append(work)
                # An independently computed normalized Pascal flow yields
                # the same state probabilities as the direct probability DP.
                fair_inflow = np.zeros_like(reaches)
                fair_inflow[0] = 1
                for i, (n, k) in enumerate(self.states):
                    if n == 0:
                        continue
                    if k < n:
                        parent = self.index[(n - 1, k)]
                        fair_inflow[i] += (n - k) / n * fair_inflow[parent] * (1 - gamma[parent])
                    if k > 0:
                        parent = self.index[(n - 1, k - 1)]
                        fair_inflow[i] += k / n * fair_inflow[parent] * (1 - gamma[parent])
                likelihood = np.array([binom.pmf(k, n, p) for n, k in self.states])
                max_flow_error = max(max_flow_error,
                                     float(np.max(abs(fair_inflow * likelihood - reaches))))
            outcomes.append(tuple(np.array(x) for x in (means, moments, works)))
        minus, plus = outcomes
        intensity = budget * root
        raw_worst_work = intensity * (
            self.weights @ minus[2] + rarity_support(plus[2] - minus[2], self.weights, self.rho))
        # A deterministic rescaling of intensity and outputs enforces the
        # observation budget, preserving all means even after numerical repair.
        scale = min(1.0, budget / max(raw_worst_work, 1e-300))
        scale *= (1 - 1e-10)
        final_intensity = intensity * scale
        mean_minus = arrays["offset"] + intensity * (self.weights @ minus[0])
        mean_delta = intensity * (plus[0] - minus[0])
        variance_minus = intensity / scale * (self.weights @ minus[1])
        variance_delta = intensity / scale * (plus[1] - minus[1])
        work_minus = final_intensity * (self.weights @ minus[2])
        work_delta = final_intensity * (plus[2] - minus[2])
        b_plus = mean_minus + rarity_support(mean_delta - 1, self.weights, self.rho)
        b_minus = -mean_minus + rarity_support(1 - mean_delta, self.weights, self.rho)
        bias = max(0, b_plus, b_minus)
        variance = variance_minus + rarity_support(variance_delta, self.weights, self.rho)
        work = work_minus + rarity_support(work_delta, self.weights, self.rho)
        vertices = rarity_vertices(self.weights, self.rho)
        vertex_bias = mean_minus + vertices @ (self.weights * (mean_delta - 1))
        vertex_var = variance_minus + vertices @ (self.weights * variance_delta)
        vertex_work = work_minus + vertices @ (self.weights * work_delta)
        exact_mse = float(np.max(vertex_bias**2 + vertex_var))
        assert max_probability_error < 1e-10
        assert max_flow_error < 1e-10
        assert work <= budget * (1 + 1e-10)
        assert abs(max(abs(vertex_bias)) - bias) < 1e-9
        assert abs(max(vertex_var) - variance) < 1e-9
        assert abs(max(vertex_work) - work) < 1e-8
        self.last_policy = {
            "description": "Draw Poisson(poisson_intensity) fresh units. On each unit follow stop_probability at count state (n,k), return terminal_output on stopping, and add all outputs to offset. All observations, including first observations, are charged.",
            "gaps": self.gaps.tolist(), "weights": self.weights.tolist(),
            "rho": self.rho, "budget": budget, "cap": self.cap,
            "poisson_intensity": float(final_intensity),
            "offset": float(arrays["offset"]),
            "states": self.states,
            "stop_probability": gamma.tolist(),
            "terminal_output": (outputs / scale).tolist(),
            "numerical_worst_work": float(work),
            "numerical_rms_bound": math.sqrt(max(0, bias**2 + variance)),
        }
        return {
            "reconstructed_rms_bound": math.sqrt(max(0, bias**2 + variance)),
            "actual_worst_rms": math.sqrt(max(0, exact_mse)),
            "actual_bias_bound": float(bias),
            "actual_variance_bound": float(variance),
            "actual_worst_work": float(work),
            "poisson_intensity": float(final_intensity),
            "probability_error": max_probability_error,
            "flow_recursion_error": max_flow_error,
            "rarity_polytope_vertices": len(vertices),
            "intensity_repair_factor": float(scale),
        }


def run_suite(output_path):
    cases = [
        ("one_gap", [0.25], [1.0], 0.1),
        ("three_scales", [0.4, 0.2, 0.08], [0.75, 0.20, 0.05], 0.1),
        ("rare_hard_atom", [0.45, 0.08], [0.99, 0.01], 0.1),
    ]
    results = []
    for name, gaps, weights, rho in cases:
        for cap in (4, 8, 16, 32):
            model = FlowProgram(gaps, weights, rho, cap)
            for budget in (100.0, 1000.0):
                row = model.solve(budget)
                row.update(case=name, gaps=gaps, weights=weights)
                results.append(row)
                if name == "three_scales" and cap == 32 and budget == 1000:
                    Path(output_path).with_name("example_policy.json").write_text(
                        json.dumps(model.last_policy, indent=2) + "\n")
                print(json.dumps({k: row[k] for k in (
                    "case", "cap", "budget", "program_rms",
                    "reconstructed_rms_bound", "actual_worst_work")}), flush=True)
    # Monotonicity is tested only to numerical tolerance, and no finite
    # cap is equated to the unrestricted minimax risk.
    for case, *_ in cases:
        for budget in (100.0, 1000.0):
            rows = [r for r in results if r["case"] == case and r["budget"] == budget]
            vals = [r["program_rms"] for r in rows]
            assert all(y <= x + 2e-5 for x, y in zip(vals, vals[1:]))
    analytic_checks = []
    for cap in (1, 4, 8):
        model = FlowProgram([0.5], [1.0], 0.1, cap)
        for budget in (1.0, 100.0, 1000.0):
            row = model.solve(budget)
            # Perfect labels at one observation: optimize response slope s.
            # The squared certificate is a(1-s)^2+c*s^2, where
            # a=rho^2/4 and c=rho(1-rho)/B. Its minimum is ac/(a+c).
            a0 = model.rho**2 / 4
            c0 = model.rho * (1 - model.rho) / budget
            expected = math.sqrt(a0 * c0 / (a0 + c0))
            relative_error = abs(row["program_rms"] / expected - 1)
            assert relative_error < 2e-5, (row, expected)
            analytic_checks.append({"cap": cap, "budget": budget,
                                    "computed": row["program_rms"],
                                    "analytic": expected,
                                    "relative_error": relative_error})
    payload = {
        "scope": "Numerical finite-cap upper certificates; not formal verification, exact minimax risks, or a claim that cap 32 is universally sufficient.",
        "cvxpy_version": cp.__version__,
        "solver": "CLARABEL",
        "results": results,
        "perfect_label_analytic_checks": analytic_checks,
    }
    Path(output_path).write_text(json.dumps(payload, indent=2) + "\n")
    return payload


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default=str(Path(__file__).with_name("flow_results.json")))
    args = parser.parse_args()
    run_suite(args.output)
