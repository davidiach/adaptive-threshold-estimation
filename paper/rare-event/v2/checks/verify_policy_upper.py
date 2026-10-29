#!/usr/bin/env python3
"""Exact rational verification of an observable finite-cap Poisson policy.

This standard-library-only verifier evaluates the actual stopping policy,
not the solver's flow variables or objective. Its returned RMS upper bound
is valid for both the finite-cap flow program and unrestricted minimax risk.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

from verify_finite_dual import fraction_text, rational, require, states_for


def sqrt_upper_decimal(value, digits=12):
    value = Fraction(value)
    require(value >= 0)
    scale = 10**digits
    root = math.isqrt(value.numerator * scale**2 // value.denominator)
    if root**2 * value.denominator < value.numerator * scale**2:
        root += 1
    return f"{root // scale}.{root % scale:0{digits}d}"


def rarity_support(values, weights, rho):
    remaining, value = rho, Fraction(0)
    for i in sorted(range(len(values)), key=lambda i: values[i], reverse=True):
        if values[i] <= 0 or remaining == 0:
            break
        mass = min(weights[i], remaining)
        value += mass * values[i]
        remaining -= mass
    return value


def evaluate(policy):
    gaps = list(map(rational, policy["gaps"]))
    weights = list(map(rational, policy["weights"]))
    rho, budget = rational(policy["rho"]), rational(policy["budget"])
    cap = int(policy["cap"])
    intensity = rational(policy["poisson_intensity"])
    offset = rational(policy["offset"])
    gamma = list(map(rational, policy["stop_probability"]))
    outputs = list(map(rational, policy["terminal_output"]))
    require(cap >= 1 and budget > 0 and 0 < rho <= Fraction(1, 4))
    require(len(gaps) == len(weights) > 0)
    require(sum(weights) == 1 and all(w > 0 for w in weights))
    require(all(0 < d <= Fraction(1, 2) for d in gaps))
    require(intensity >= 0)
    states = states_for(cap)
    index = {state: i for i, state in enumerate(states)}
    require(len(gamma) == len(outputs) == len(states))
    require(gamma[0] == 0 and all(0 <= g <= 1 for g in gamma))
    require(all(gamma[index[(cap, k)]] == 1 for k in range(cap + 1)))
    outcomes = []
    for sign in (-1, 1):
        means, moments, works = [], [], []
        for d in gaps:
            p = Fraction(1, 2) + sign * d
            reaches = [Fraction(0)] * len(states)
            reaches[0] = Fraction(1)
            mean = moment = work = stopped_mass = Fraction(0)
            for i, (n, k) in enumerate(states):
                stopped = reaches[i] * gamma[i]
                continued = reaches[i] - stopped
                stopped_mass += stopped
                mean += stopped * outputs[i]
                moment += stopped * outputs[i]**2
                if n < cap:
                    work += continued
                    reaches[index[(n + 1, k)]] += continued * (1 - p)
                    reaches[index[(n + 1, k + 1)]] += continued * p
            require(stopped_mass == 1)
            means.append(mean)
            moments.append(moment)
            works.append(work)
        outcomes.append((means, moments, works))
    minus, plus = outcomes
    null_mean = offset + intensity * sum(w * x for w, x in zip(weights, minus[0]))
    mean_delta = [intensity * (p - m) - 1 for p, m in zip(plus[0], minus[0])]
    positive_bias = null_mean + rarity_support(mean_delta, weights, rho)
    negative_bias = -null_mean + rarity_support([-x for x in mean_delta], weights, rho)
    bias = max(Fraction(0), positive_bias, negative_bias)
    variance = intensity * (sum(w * x for w, x in zip(weights, minus[1]))
                           + rarity_support([p - m for p, m in zip(plus[1], minus[1])], weights, rho))
    unit_work = (sum(w * x for w, x in zip(weights, minus[2]))
                 + rarity_support([p - m for p, m in zip(plus[2], minus[2])], weights, rho))
    work = intensity * unit_work
    return {"bias": bias, "variance": variance, "work": work,
            "unit_work": unit_work, "upper_squared": bias**2 + variance,
            "budget": budget, "states_checked": len(states)}


def verify(policy):
    evaluated = evaluate(policy)
    require(evaluated["work"] <= evaluated["budget"], "work budget")
    claimed = rational(policy["certified_squared_upper_bound"])
    require(claimed >= evaluated["upper_squared"])
    if "certified_rms_upper_bound_decimal" in policy:
        displayed = rational(policy["certified_rms_upper_bound_decimal"])
        require(displayed >= 0 and displayed**2 >= claimed, "upper RMS rounding")
    return {
        "verified_with": "exact Python Fraction arithmetic",
        "states_checked": evaluated["states_checked"],
        "worst_bias_bound": fraction_text(evaluated["bias"]),
        "worst_variance_bound": fraction_text(evaluated["variance"]),
        "worst_expected_work": fraction_text(evaluated["work"]),
        "certified_squared_upper_bound": fraction_text(claimed),
        "certified_rms_upper_bound_decimal": sqrt_upper_decimal(claimed),
    }


def certify_numerical_policy(numerical_policy, denominator=10**12):
    policy = {
        key: numerical_policy[key] for key in ("gaps", "weights", "rho", "budget", "cap")
    }
    for key in ("gaps", "weights"):
        policy[key] = [fraction_text(rational(x)) for x in policy[key]]
    for key in ("rho", "budget"):
        policy[key] = fraction_text(rational(policy[key]))
    policy["poisson_intensity"] = fraction_text(rational(numerical_policy["poisson_intensity"]))
    policy["offset"] = fraction_text(rational(numerical_policy["offset"]))
    policy["stop_probability"] = [fraction_text(Fraction(
        min(denominator, max(0, int(round(float(x) * denominator)))), denominator))
        for x in numerical_policy["stop_probability"]]
    policy["terminal_output"] = [fraction_text(rational(x))
                                   for x in numerical_policy["terminal_output"]]
    evaluated = evaluate(policy)
    intensity = rational(policy["poisson_intensity"])
    if evaluated["work"] > evaluated["budget"]:
        scale = evaluated["budget"] / evaluated["work"]
        policy["poisson_intensity"] = fraction_text(intensity * scale)
        policy["terminal_output"] = [fraction_text(rational(x) / scale)
                                       for x in policy["terminal_output"]]
        evaluated = evaluate(policy)
    policy["description"] = "Exact rational observable cap-N Poisson policy, independently evaluated at every atomic sign and over the full rarity polytope."
    policy["certified_squared_upper_bound"] = fraction_text(evaluated["upper_squared"])
    policy["certified_rms_upper_bound_decimal"] = sqrt_upper_decimal(evaluated["upper_squared"])
    return policy, verify(policy)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("policy", type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(json.loads(args.policy.read_text())), indent=2))
