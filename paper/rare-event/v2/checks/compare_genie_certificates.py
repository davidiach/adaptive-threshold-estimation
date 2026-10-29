#!/usr/bin/env python3
"""Turn four-prior certificates into exact unrestricted-risk certificates.

The terminal Bellman reward reveals the latent magnitude and sign for free.
This dominates every subsequent sampling policy, so a verified work price
upper-bounds the uncapped midpoint information/work ratio. The accompanying
Bayes-affinity theorem then supplies a fully adaptive minimax lower bound.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

from solve_finite_dual import build_certificate, float_bellman_price
from verify_finite_dual import exact_kernel, rational, states_for, verify


def run(source_dir, output_dir, caps=(8, 32)):
    source_dir, output_dir = Path(source_dir), Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    results = []
    for path in sorted(source_dir.glob("*.json")):
        source = json.loads(path.read_text())
        if "priors" not in source or source.get("certificate_kind") == "uncapped_midpoint_genie":
            continue
        raw_priors = {key: [float(rational(x)) for x in values]
                      for key, values in source["priors"].items()}
        gaps = list(map(rational, source["gaps"]))
        weights = list(map(rational, source["weights"]))
        for cap in caps:
            cert, checked = build_certificate(
                gaps, weights, rational(source["rho"]),
                rational(source["budget"]), cap, raw_priors, genie=True)
            priors = {key: list(map(rational, values))
                      for key, values in cert["priors"].items()}
            kernels = {key: exact_kernel(gaps, weights, prior, cap)
                       for key, prior in priors.items()}
            ordinary_reward = [float((h-l)**2/v) if v else 0.0
                               for h, l, v in zip(kernels["high"],
                                                 kernels["low"],
                                                 kernels["variance"])]
            states = states_for(cap)
            index = {state: i for i, state in enumerate(states)}
            ordinary_price = float_bellman_price(
                np.array(ordinary_reward),
                np.array(list(map(float, kernels["work"]))), states, index)
            destination = f"{path.stem}_genieN{cap}.json"
            (output_dir / destination).write_text(json.dumps(cert, indent=2) + "\n")
            checked_again = verify(json.loads((output_dir / destination).read_text()))
            assert checked_again == checked
            row = {
                "source_certificate": path.name,
                "genie_cap": cap,
                "target_gap": float(rational(checked["target_gap"])),
                "ordinary_midpoint_price_numerical": ordinary_price,
                "genie_price_exact_upper_as_float": float(rational(
                    cert["information_work_price"])),
                "unrestricted_rms_lower_bound_decimal":
                    checked["certified_rms_lower_bound_decimal"],
                "certificate": destination,
                "exact_verification": checked,
            }
            results.append(row)
            print(json.dumps({key: row[key] for key in (
                "source_certificate", "genie_cap",
                "ordinary_midpoint_price_numerical",
                "genie_price_exact_upper_as_float",
                "unrestricted_rms_lower_bound_decimal")}), flush=True)
    payload = {
        "scope": "Exact rational midpoint genie-boundary certificates for unrestricted adaptive RMS risk. Ordinary midpoint prices are numerical diagnostics only.",
        "results": results,
    }
    (output_dir / "genie_comparison_results.json").write_text(
        json.dumps(payload, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    base = Path(__file__).resolve().parent
    parser.add_argument("--source-dir", type=Path, default=base / "certificates")
    parser.add_argument("--output-dir", type=Path, default=base / "genie_certificates")
    parser.add_argument("--caps", type=int, nargs="+", default=[8, 32])
    args = parser.parse_args()
    run(args.source_dir, args.output_dir, tuple(args.caps))
