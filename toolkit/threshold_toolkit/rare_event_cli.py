"""Evaluate the finite-law rare-event rate functional without running an estimator.

    python -m threshold_toolkit rare-event --gaps 0.01,0.1,0.4 --weights 1,2,7 --rarity 0.05 --budget 100000

This module can also be invoked directly with only the standard library:
``python -m threshold_toolkit.rare_event_cli ...``.
"""

import argparse
from dataclasses import asdict
import json
import math
import re
import sys

from .rare_events import FiniteGapLaw, RareEventProfile


def _numbers(text):
    values = [float(token) for token in re.split(r"[\s,;]+", text.strip()) if token]
    if not values:
        raise ValueError("give at least one number")
    return values


def _json_safe(value):
    """Keep JSON standards-compliant when a diagnostic exceeds float range."""
    if isinstance(value, float) and not math.isfinite(value):
        return None
    if isinstance(value, dict):
        return {key: _json_safe(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [_json_safe(item) for item in value]
    return value


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="python -m threshold_toolkit rare-event",
        description="Evaluate the paper's Q(B) rate functional for a known finite gap law.")
    parser.add_argument("--gaps", required=True,
                        help="positive magnitudes |p - 1/2| in (0, 0.5], comma separated")
    parser.add_argument("--weights", help="nonnegative relative masses; default: equal masses")
    parser.add_argument("--rarity", required=True, type=float,
                        help="known global bound rho on the positive fraction, in (0, 0.25]")
    goal = parser.add_mutually_exclusive_group(required=True)
    goal.add_argument("--budget", type=float, help="positive expected flip budget B")
    goal.add_argument("--target-rate", type=float,
                      help="invert Q(B) at this target; this is not an achieved RMS-error target")
    parser.add_argument("--json", action="store_true", help="emit a structured numerical report")
    args = parser.parse_args(argv)

    try:
        law = FiniteGapLaw(_numbers(args.gaps),
                           None if args.weights is None else _numbers(args.weights))
        profile = RareEventProfile(law, args.rarity)
        inversion = None
        if args.budget is not None:
            result = profile.evaluate(args.budget)
        else:
            inversion = profile.budget_for_rate(args.target_rate)
            result = (profile.evaluate(inversion.budget)
                      if 0 < inversion.budget < math.inf else None)
    except (ValueError, OverflowError, TypeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    scope = ("Q is a paper-proof rate functional, not an achieved error or a certified "
             "execution budget. Numerical values use floating-point arithmetic, not interval certification.")
    if args.json:
        payload = {
            "law": {"gaps": law.gaps, "weights": law.weights},
            "rarity": profile.rho,
            "quantile_gap": profile.quantile_gap,
            "evaluation": None if result is None else asdict(result),
            "inversion": None if inversion is None else asdict(inversion),
            "scope": scope,
            "nonfinite_values": "null means outside the floating-point range; consult inversion status and log_budget",
        }
        print(json.dumps(_json_safe(payload), indent=2, allow_nan=False))
        return 0

    count = len(law.gaps)
    print(f"Known finite law: {count} distinct positive gap{'' if count == 1 else 's'}; "
          f"global rarity rho = {profile.rho:.6g}.")
    print(f"Smallest-gap mass rho ends at gap {profile.quantile_gap:.6g}.\n")
    if inversion is not None:
        print(f"Target Q: {inversion.target:.6g}")
        if inversion.budget == 0:
            print("Every positive budget meets this rate target; the budget infimum is 0.")
        elif math.isinf(inversion.budget):
            print("The required budget exceeds the floating-point range.")
            print(f"Its natural logarithm is approximately {inversion.log_budget:.10g}.")
        else:
            print(f"Budget at the Q target: approximately {inversion.budget:.10g} flips.")
        print()
    if result is not None:
        print(f"At expected budget B = {result.budget:.10g}:")
        print(f"  Tail contribution:         {result.tail:.10g}")
        print(f"  Core entropy contribution: {result.entropy_term:.10g}")
        print(f"  Q(B), capped at rho:       {result.value:.10g}")
        print(f"  Selection K(B) comparison: [{result.selection_lower:.10g}, {result.selection_upper:.10g}]")
        print()
    print(scope)
    return 0


if __name__ == "__main__":
    sys.exit(main())
