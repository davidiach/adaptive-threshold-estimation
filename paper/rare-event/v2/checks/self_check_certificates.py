#!/usr/bin/env python3
"""Recheck stored exact certificates and reject targeted corruptions."""
from __future__ import annotations

import copy
import json
from pathlib import Path

from verify_finite_dual import (
    exact_kernel, exact_latent_rewards, fraction_text, rational, states_for,
    verify as verify_lower,
)
from verify_policy_upper import verify as verify_upper


def must_reject(payload, verifier, name):
    try:
        verifier(payload)
    except (ValueError, AssertionError):
        return name
    raise RuntimeError(f"Verifier accepted corrupted certificate: {name}")


def main():
    base = Path(__file__).resolve().parent
    checked = {"lower": 0, "upper": 0}
    for directory in ("certificates", "genie_certificates", "optimized_genie"):
        for path in sorted((base / directory).glob("*.json")):
            payload = json.loads(path.read_text())
            if "information_potentials" in payload:
                verify_lower(payload)
                checked["lower"] += 1
            elif "stop_probability" in payload:
                verify_upper(payload)
                checked["upper"] += 1

    seed = json.loads((base / "optimized_genie/three_scales_N8_B1000_lower.json").read_text())
    rejected = []
    changed = copy.deepcopy(seed)
    changed["priors"]["high"] = ["1/1"] * len(seed["gaps"])
    rejected.append(must_reject(changed, verify_lower, "rarity constraint"))
    changed = copy.deepcopy(seed)
    changed["information_work_price"] = "0/1"
    rejected.append(must_reject(changed, verify_lower, "Bellman work price"))
    changed = copy.deepcopy(seed)
    changed["certified_squared_lower_bound"] = "1/1"
    rejected.append(must_reject(changed, verify_lower, "overstated lower value"))

    gaps = list(map(rational, seed["gaps"]))
    weights = list(map(rational, seed["weights"]))
    priors = {key: list(map(rational, value)) for key, value in seed["priors"].items()}
    kernels = {key: exact_kernel(gaps, weights, prior, seed["cap"])
               for key, prior in priors.items()}
    latent = exact_latent_rewards(gaps, weights, priors["low"], priors["high"],
                                 priors["variance"], seed["cap"])
    for i, (n, k) in enumerate(states_for(seed["cap"])):
        if n != seed["cap"] or kernels["variance"][i] == 0:
            continue
        ordinary = (kernels["high"][i] - kernels["low"][i])**2 / kernels["variance"][i]
        if latent[i] > ordinary:
            changed = copy.deepcopy(seed)
            changed["information_potentials"][i] = fraction_text((ordinary + latent[i]) / 2)
            rejected.append(must_reject(changed, verify_lower, "genie boundary reward"))
            break
    else:
        raise RuntimeError("No strict genie boundary state available for negative control")

    policy = json.loads((base / "optimized_genie/three_scales_N8_B1000_upper.json").read_text())
    changed = copy.deepcopy(policy)
    changed["poisson_intensity"] = fraction_text(1000 * rational(policy["poisson_intensity"]))
    rejected.append(must_reject(changed, verify_upper, "actual policy budget"))
    changed = copy.deepcopy(policy)
    changed["certified_squared_upper_bound"] = "0/1"
    rejected.append(must_reject(changed, verify_upper, "understated policy risk"))
    bracket_results = json.loads((base / "optimized_genie/genie_bracket_results.json").read_text())
    decisions = 0
    analytic_checks = []
    for row in bracket_results["results"]:
        lo = json.loads((base / "optimized_genie" / row["lower_certificate"]).read_text())
        hi = json.loads((base / "optimized_genie" / row["upper_policy"]).read_text())
        lower = rational(lo["certified_squared_lower_bound"])
        upper = rational(hi["certified_squared_upper_bound"])
        if (upper <= 4 * lower) != row["exact_factor_two_stopping_test"]:
            raise RuntimeError("Incorrect stored cap-stopping decision")
        decisions += 1
        if row["case"] == "perfect_labels":
            rho, budget = rational(lo["rho"]), rational(lo["budget"])
            a, c = rho**2 / 4, rho * (1 - rho) / budget
            analytic = a * c / (a + c)
            if not lower <= analytic <= upper:
                raise RuntimeError("Analytic perfect-label value outside exact bracket")
            analytic_checks.append({"budget": str(budget), "cap": row["cap"],
                                    "analytic_squared_value": str(analytic),
                                    "contained_in_exact_bracket": True})
    result = {"exact_certificates_rechecked": checked,
              "exact_stopping_decisions_rechecked": decisions,
              "perfect_label_analytic_checks": analytic_checks,
              "targeted_corruptions_rejected": rejected}
    (base / "certificate_self_check.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
