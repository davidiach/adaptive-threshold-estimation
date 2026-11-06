"""Record the distinct-cost example and a small exhaustive comparison.

Creates a fresh .runtime directory. Does not replace published evidence.
Run from any working directory with Python 3.12 and the standard library.
"""

from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "toolkit"))
from threshold_toolkit.approximate_selection import select_approximately
from threshold_toolkit.band_cost_selection import select_by_band_cost
from threshold_toolkit.rare_event_functional import FiniteGapLaw


def make_law(n):
    gaps = [F(1, 2**i) for i in range(1, n + 1)]
    masses = [d*d*(1+F(i, 10**12)) for i, d in enumerate(gaps)]
    return FiniteGapLaw([(d, w/sum(masses)) for d, w in zip(gaps, masses)])


def record(n):
    law = make_law(n)
    result = select_approximately(law, rho="1/4", budget=2**32,
                                 epsilon="1/10", max_transitions=20_000)
    assert len({a.mass/a.gap**2 for a in law.atoms}) == n
    assert result.value.upper <= (1+result.epsilon)*result.value.lower
    answer = {
        "bands": n, "distinct_positive_costs": n,
        "law": law.canonical(), "rho": "1/4", "budget": str(2**32),
        "epsilon": str(result.epsilon), "suffix_count": result.suffix_count,
        "final_states": result.final_states, "peak_states": result.peak_states,
        "transitions": result.transitions, "subdivisions": result.subdivisions,
        "value": result.value.as_dict(), "witness_value": result.witness_value.as_dict(),
        "selected": list(result.selected),
        "selected_gaps": [str(a.gap) for a, keep in zip(law.atoms, result.selected) if keep],
        "relative_enclosure_display": float(result.value.upper/result.value.lower),
    }
    if n == 8:
        exact = select_by_band_cost(law, rho="1/4", budget=2**32)
        assert result.value.lower <= exact.value.upper
        assert exact.value.lower <= result.value.upper
        assert result.value.upper <= (1+result.epsilon)*exact.value.lower
        answer["exact_comparison"] = exact.value.as_dict()
    return answer


def main():
    sources = [
        "research/2026-11-06-selection-approximation/CONTRACT.md",
        "research/2026-11-06-selection-approximation/NOTE.md",
        "research/2026-11-06-selection-approximation/reproduce.py",
        "toolkit/threshold_toolkit/approximate_selection.py",
        "toolkit/threshold_toolkit/band_cost_selection.py",
        "toolkit/threshold_toolkit/rare_event_functional.py",
        "toolkit/tests/test_approximate_selection.py",
        "lean/ThresholdHC/GapLawMenus/Full.lean",
    ]
    evidence = {
        "baseline_commit": "68adbf3",
        "scope": "deterministic_finite_law_approximation_paper_proof_not_lean_verified",
        "source_sha256": {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                          for name in sources},
        "cases": [record(8), record(64)],
    }
    parent = ROOT / ".runtime" / "selection-approximation"
    parent.mkdir(parents=True, exist_ok=True)
    out = Path(tempfile.mkdtemp(prefix="replay-", dir=parent)) / "evidence.json"
    out.write_text(json.dumps(evidence, indent=2) + "\n", encoding="utf-8")
    for case in evidence["cases"]:
        print(f"{case['bands']} bands: {case['suffix_count']} suffixes, "
              f"{case['final_states']} retained states, {case['transitions']} transitions")
    print(out)


if __name__ == "__main__":
    main()
