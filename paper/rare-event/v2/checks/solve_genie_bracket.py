#!/usr/bin/env python3
"""Optimize a genie dual and certify both sides of an adaptive-risk bracket.

Only the optimizer uses floating point. The final lower certificate, the
observable upper policy, and the cap-doubling stopping test use exact rational
arithmetic and independent standard-library verifiers.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import time

from solve_finite_dual import CompactDual, build_certificate, load_primal
from verify_finite_dual import rational, verify as verify_lower
from verify_policy_upper import certify_numerical_policy, verify as verify_upper


def run(output_dir, caps=(4, 8, 16, 32)):
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    Primal = load_primal()
    cases = [
        ("one_gap", [0.25], [1.0], 0.1),
        ("three_scales", [0.4, 0.2, 0.08], [0.75, 0.20, 0.05], 0.1),
        ("rare_hard_atom", [0.45, 0.08], [0.99, 0.01], 0.1),
        ("perfect_labels", [0.5], [1.0], 0.1),
    ]
    results = []
    for name, gaps, weights, rho in cases:
        for budget in (100.0, 1000.0):
            for cap in ((1,) if name == "perfect_labels" else caps):
                started = time.monotonic()
                dual = CompactDual(gaps, weights, rho, cap, genie=True)
                raw = dual.solve(budget)
                certificate, lower_check = build_certificate(
                    gaps, weights, rho, budget, cap, raw["priors"], full_genie=True)
                primal = Primal(gaps, weights, rho, cap)
                primal.solve(budget)
                policy, upper_check = certify_numerical_policy(primal.last_policy)
                lower_sq = rational(certificate["certified_squared_lower_bound"])
                adaptive_sq = rational(certificate["certified_adaptive_squared_lower_bound"])
                upper_sq = rational(policy["certified_squared_upper_bound"])
                stopping_test = upper_sq <= 4 * lower_sq
                stem = f"{name}_N{cap}_B{int(budget)}"
                lower_file, upper_file = stem + "_lower.json", stem + "_upper.json"
                (output_dir / lower_file).write_text(json.dumps(certificate, indent=2) + "\n")
                (output_dir / upper_file).write_text(json.dumps(policy, indent=2) + "\n")
                assert verify_lower(json.loads((output_dir / lower_file).read_text())) == lower_check
                assert verify_upper(json.loads((output_dir / upper_file).read_text())) == upper_check
                row = {
                    "case": name, "cap": cap, "budget": budget,
                    "dual_status": raw["status"],
                    "raw_genie_dual_rms": raw["raw_dual_rms"],
                    "certified_unrestricted_program_lower_decimal": lower_check["certified_rms_lower_bound_decimal"],
                    "certified_adaptive_rms_lower_decimal": lower_check["certified_adaptive_rms_lower_bound_decimal"],
                    "certified_rms_upper_decimal": upper_check["certified_rms_upper_bound_decimal"],
                    "program_bracket_ratio": math.sqrt(float(upper_sq / lower_sq)),
                    "adaptive_risk_bracket_ratio": math.sqrt(float(upper_sq / adaptive_sq)),
                    "exact_factor_two_stopping_test": stopping_test,
                    "lower_certificate": lower_file, "upper_policy": upper_file,
                    "elapsed_seconds": time.monotonic() - started,
                }
                results.append(row)
                print(json.dumps(row), flush=True)
                if stopping_test:
                    break
    payload = {
        "scope": "Fully exact rational lower and upper certificates. The program interval encloses the unrestricted flow value. The adaptive interval encloses fully adaptive minimax RMS risk. The factor-two stopping decision is an exact rational comparison.",
        "results": results,
    }
    (output_dir / "genie_bracket_results.json").write_text(json.dumps(payload, indent=2) + "\n")
    return payload


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).with_name("optimized_genie"))
    parser.add_argument("--caps", type=int, nargs="+", default=[4, 8, 16, 32])
    args = parser.parse_args()
    run(args.output_dir, tuple(args.caps))
