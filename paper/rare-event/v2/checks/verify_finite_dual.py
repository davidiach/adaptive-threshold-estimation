#!/usr/bin/env python3
"""Check a finite-support Bellman dual certificate with exact rational arithmetic.

This verifier uses only the Python standard library. It does not invoke a
numerical optimizer or trust a stored solver objective. Ordinary certificates
bound the cap-N convex program. Midpoint certificates with a latent-genie
boundary bound the unrestricted adaptive minimax risk, using the accompanying
Bayes-affinity theorem.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path


def rational(value):
    return Fraction(str(value))


def require(condition, *context):
    """Checks remain active even when Python is invoked with -O."""
    if not condition:
        raise ValueError(context or ("invalid certificate",))


def fraction_text(value):
    value = Fraction(value)
    return f"{value.numerator}/{value.denominator}"


def states_for(cap):
    return [(n, k) for n in range(cap + 1) for k in range(n + 1)]


def exact_kernel(gaps, weights, prior, cap):
    """Mixture binomial mass at each count state, as an exact Fraction."""
    result = []
    for n, k in states_for(cap):
        mass = Fraction(0)
        choose = math.comb(n, k)
        for d, w, q in zip(gaps, weights, prior):
            pm, pp = Fraction(1, 2) - d, Fraction(1, 2) + d
            bm = choose * pm**k * (1 - pm)**(n - k)
            bp = choose * pp**k * (1 - pp)**(n - k)
            mass += w * ((1 - q) * bm + q * bp)
        result.append(mass)
    return result


def exact_latent_rewards(gaps, weights, low, high, reference, cap):
    """Information after free revelation of (D,S), grouped by count state."""
    result = []
    for n, k in states_for(cap):
        reward = Fraction(0)
        choose = math.comb(n, k)
        for d, w, ql, qh, qv in zip(gaps, weights, low, high, reference):
            contrast = qh - ql
            pm, pp = Fraction(1, 2) - d, Fraction(1, 2) + d
            bm = choose * pm**k * (1 - pm)**(n - k)
            bp = choose * pp**k * (1 - pp)**(n - k)
            if qv > 0:
                reward += w * contrast**2 * bp / qv
            else:
                require(contrast == 0, "singular positive latent reference")
            if qv < 1:
                reward += w * contrast**2 * bm / (1 - qv)
            else:
                require(contrast == 0, "singular negative latent reference")
        result.append(reward)
    return result


def exact_genie_rewards(gaps, weights, low, high, cap):
    midpoint = [(l + h) / 2 for l, h in zip(low, high)]
    return exact_latent_rewards(gaps, weights, low, high, midpoint, cap)


def children_sum(values, index, n, k):
    return (Fraction(n + 1 - k, n + 1) * values[index[(n + 1, k)]]
            + Fraction(k + 1, n + 1) * values[index[(n + 1, k + 1)]])


def sqrt_lower_decimal(value, digits=12):
    """A decimal lower bound, rounded downward with integer arithmetic."""
    value = Fraction(value)
    if value <= 0:
        return "0." + "0" * digits
    scale = 10**digits
    numerator = value.numerator * scale**2 // value.denominator
    lower = math.isqrt(numerator)
    return f"{lower // scale}.{lower % scale:0{digits}d}"


def adaptive_squared_lower(target_gap, budget, price):
    """Exact square of max_{0<=s<=1} s*t/2*(1-s*s*B*k/4)_+."""
    x = budget * price
    if x <= Fraction(4, 3):
        return target_gap**2 * (1 - x / 4)**2 / 4
    return 4 * target_gap**2 / (27 * x)


def verify(certificate):
    gaps = list(map(rational, certificate["gaps"]))
    weights = list(map(rational, certificate["weights"]))
    rho = rational(certificate["rho"])
    budget = rational(certificate["budget"])
    cap = int(certificate["cap"])
    kind = certificate.get("certificate_kind", "finite_cap")
    require(kind in ("finite_cap", "uncapped_midpoint_genie", "uncapped_four_prior_genie"))
    require(cap >= 1 and budget > 0 and 0 < rho <= Fraction(1, 4))
    require(len(gaps) == len(weights) > 0)
    require(sum(weights) == 1 and all(w > 0 for w in weights))
    require(all(0 < d <= Fraction(1, 2) for d in gaps))
    priors = {name: list(map(rational, certificate["priors"][name]))
              for name in ("low", "high", "variance", "work")}
    for name, prior in priors.items():
        require(len(prior) == len(weights), name)
        require(all(0 <= q <= 1 for q in prior), name)
        require(sum(w * q for w, q in zip(weights, prior)) <= rho, name)

    kernels = {name: exact_kernel(gaps, weights, prior, cap)
               for name, prior in priors.items()}
    genie_rewards = None
    if kind == "uncapped_midpoint_genie":
        midpoint = [(ql + qh) / 2 for ql, qh in zip(
            priors["low"], priors["high"])]
        require(priors["variance"] == midpoint)
        require(priors["work"] == midpoint)
    if kind in ("uncapped_midpoint_genie", "uncapped_four_prior_genie"):
        genie_rewards = exact_latent_rewards(
            gaps, weights, priors["low"], priors["high"], priors["variance"], cap)
    price = rational(certificate["information_work_price"])
    potentials = list(map(rational, certificate["information_potentials"]))
    states = states_for(cap)
    index = {state: i for i, state in enumerate(states)}
    require(price >= 0 and len(potentials) == len(states))
    require(potentials[0] == 0)
    require(all(x >= 0 for x in potentials))
    minimum_stop_slack = None
    minimum_continue_slack = None
    for i, (n, k) in enumerate(states):
        if n == 0:
            continue
        delta = kernels["high"][i] - kernels["low"][i]
        stop_slack = kernels["variance"][i] * potentials[i] - delta**2
        require(stop_slack >= 0, "stop inequality", n, k, stop_slack)
        if genie_rewards is not None and n == cap:
            require(potentials[i] >= genie_rewards[i], "genie boundary inequality", n, k)
        minimum_stop_slack = (stop_slack if minimum_stop_slack is None
                              else min(minimum_stop_slack, stop_slack))
        if n < cap:
            continuation_slack = (
                potentials[i] + price * kernels["work"][i]
                - children_sum(potentials, index, n, k))
            require(continuation_slack >= 0, "continuation inequality", n, k, continuation_slack)
            minimum_continue_slack = (
                continuation_slack if minimum_continue_slack is None
                else min(minimum_continue_slack, continuation_slack))
    root_slack = price - children_sum(potentials, index, 0, 0)
    require(root_slack >= 0, "root inequality", root_slack)
    target_gap = sum(w * (qh - ql) for w, qh, ql in zip(
        weights, priors["high"], priors["low"]))
    require(target_gap >= 0)
    if kind == "uncapped_midpoint_genie":
        lower_squared = adaptive_squared_lower(target_gap, budget, price)
    else:
        lower_squared = target_gap**2 / (4 + budget * price)
    claimed = rational(certificate["certified_squared_lower_bound"])
    require(0 <= claimed <= lower_squared)
    if "certified_rms_lower_bound_decimal" in certificate:
        displayed = rational(certificate["certified_rms_lower_bound_decimal"])
        require(displayed >= 0 and displayed**2 <= claimed, "lower RMS rounding")
    result = {
        "verified_with": "exact Python Fraction arithmetic",
        "certificate_kind": kind,
        "bound_scope": ({"uncapped_midpoint_genie": "unrestricted adaptive minimax RMS risk",
                         "uncapped_four_prior_genie": "unrestricted flow-program RMS value",
                         "finite_cap": "cap-N convex program RMS value"}[kind]),
        "states_checked": len(states),
        "target_gap": fraction_text(target_gap),
        "information_work_price": fraction_text(price),
        "root_slack": fraction_text(root_slack),
        "minimum_stop_slack": fraction_text(minimum_stop_slack or 0),
        "minimum_continue_slack": fraction_text(minimum_continue_slack or 0),
        "certified_squared_lower_bound": fraction_text(claimed),
        "certified_rms_lower_bound_decimal": sqrt_lower_decimal(claimed),
    }
    if kind == "uncapped_four_prior_genie":
        adaptive = adaptive_squared_lower(target_gap / 3, budget, price)
        if "certified_adaptive_squared_lower_bound" in certificate:
            require(0 <= rational(certificate["certified_adaptive_squared_lower_bound"]) <= adaptive)
        if "certified_adaptive_rms_lower_bound_decimal" in certificate:
            displayed = rational(certificate["certified_adaptive_rms_lower_bound_decimal"])
            require(displayed >= 0 and displayed**2 <= adaptive, "adaptive RMS rounding")
        result["certified_adaptive_squared_lower_bound"] = fraction_text(adaptive)
        result["certified_adaptive_rms_lower_bound_decimal"] = sqrt_lower_decimal(adaptive)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    payload = json.loads(args.certificate.read_text())
    print(json.dumps(verify(payload), indent=2))
