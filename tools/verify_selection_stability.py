"""Verify total variation, rounding and transported enclosures for the original selection functional."""
import json
import subprocess

from verify_blind_upper_components import DECLARATION, FORBIDDEN, sha, strip_comments, validate_dependency_freeze, validate_reports
from verify_entropy_tail import ROOT, FREEZE, FROZEN
from verify_entropy_tail_components import LEAN, dependency_order

PREFIX = "ThresholdHC.SelectionStability."
SOURCE = LEAN / "ThresholdHC/SelectionStability"
SPEC_SHA256 = "c2ffa9d5fecfc88a60eaa6e33ed6c33b559df33c82fe9d5b0ebcba8b2ba1bbe9"


def audit_input(module="FiniteApproximation"):
    if sha(SOURCE / "Specification.lean") != SPEC_SHA256:
        raise ValueError("Changed stability statements from 0d2bb96")
    freeze = json.loads(FREEZE.read_text(encoding="utf-8"))
    if freeze["source_sha256"] != FROZEN or any(sha(ROOT / p) != h for p, h in FROZEN.items()):
        raise ValueError("Changed original entropy-tail specification")
    validate_dependency_freeze(LEAN / "ThresholdHC/EntropyTail/Specification.lean", freeze)
    paths = dependency_order([SOURCE / (module + ".lean")])
    if module == "FiniteApproximation" and not set(SOURCE.rglob("*.lean")).issubset(paths):
        raise ValueError("Unregistered stability module")
    roots = set()
    for path in paths:
        src = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(src):
            raise ValueError(f"Forbidden proof escape in {path}")
        if path.parent == SOURCE:
            for name in DECLARATION.findall(src):
                if PREFIX + name in roots:
                    raise ValueError(f"Duplicate stability declaration {name}")
                roots.add(PREFIX + name)
    checks = ["import " + PREFIX + module, "open ThresholdHC.SelectionStability"]
    for name, statement, dep in [("total_variation_stability", "TVStatement", "Variation"),
                                 ("band_preserving_rounding", "RoundingStatement", "Rounding")]:
        if SOURCE / (dep + ".lean") in paths:
            checks.append(f"example : {statement} := {name}")
    if module == "FiniteApproximation":
        checks += [
            "open MeasureTheory Set ThresholdHC.Tier6 ThresholdHC.EntropyTail",
            "example (μ : Measure Gap) [IsProbabilityMeasure μ] {η r : ℝ} (hη : 0 < η) (hr : 1 < r) : "
            "∃ (ν : Measure Gap) (T : Gap → Gap), IsProbabilityMeasure ν ∧ Measurable T ∧ "
            "tvDist μ ν / 2 ≤ η ∧ (∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) ∧ "
            "(∀ j, T ⁻¹' band j = band j) ∧ (ν.map T).support.Finite := finite_approximation_exists μ hη hr",
            "example (μ ν : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] "
            "(T : Gap → Gap) (hm : Measurable T) {r η ρ B L U : ℝ} (hr : 1 ≤ r) "
            "(hρ : 0 < ρ) (hrho : ρ ≤ 1/4) (hb : 0 < B) (hη : tvDist μ ν / 2 ≤ η) "
            "(hd : ∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) "
            "(hj : ∀ j, T ⁻¹' band j = band j) (hl : L ≤ (selection (ν.map T) ρ B).toReal) "
            "(hu : (selection (ν.map T) ρ B).toReal ≤ U) : "
            "max 0 (L-η) ≤ (selection μ ρ B).toReal ∧ (selection μ ρ B).toReal ≤ min ρ (r*U+η) := "
            "transfer_enclosure μ ν T hm hr hρ hrho hb hη hd hj hl hu",
            "example (μ ν : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] "
            "(T : Gap → Gap) (hm : Measurable T) {r η ρ B : ℝ} (hr : 1 ≤ r) "
            "(hρ : 0 < ρ) (hrho : ρ ≤ 1/4) (hb : 0 < B) (hη : tvDist μ ν / 2 ≤ η) "
            "(hd : ∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) "
            "(hj : ∀ j, T ⁻¹' band j = band j) : "
            "let Q := (ThresholdHC.EntropyTailQuantile.closedQuantileValue (ν.map T) ρ B).toReal; "
            "max 0 (5/8*Q-η) ≤ (selection μ ρ B).toReal ∧ (selection μ ρ B).toReal ≤ min ρ (r*Q+η) := "
            "quantile_enclosure μ ν T hm hr hρ hrho hb hη hd hj",
        ]
    return "\n".join(checks + ["#print axioms " + r for r in sorted(roots)]) + "\n", roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", PREFIX + "FiniteApproximation"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         capture_output=True, text=True, encoding="utf-8")
    report = run.stdout + run.stderr
    print(report, end="")
    validate_reports(report, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
