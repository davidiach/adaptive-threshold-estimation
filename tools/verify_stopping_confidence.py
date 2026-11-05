"""Audit the confidence lower bound charged to the reference experiment's physical work."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ConfidenceProgram.Lower
noncomputable section
open MeasureTheory InformationTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceTransfer
open scoped ENNReal
example {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q r : SignLaw) {κ B : ℝ} (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (h : LocalReferenceWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) κ)
    (hw : expectedWork μ A (smoothedSign q r) ≤ ENNReal.ofReal B)
    (hw' : expectedWork μ A (smoothedSign r q) < ∞) :
    klDiv (observableDecisionLaw μ A (smoothedSign q r) id) (observableDecisionLaw μ A (smoothedSign r q) id) ≤
      ENNReal.ofReal ((8/3)*κ*B) := stopped_reference_work_kl μ A q r κ B hκ hB h hw hw'
open ThresholdHC.ConfidenceProgram ThresholdHC.Genie
example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/2) (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    infiniteProgramValue μ ρ (B/Real.log (1/δ))/30 ≤ rareConfidenceRadius μ ρ B δ :=
  stopping_confidence_lower μ hr hu hb hd hd'
example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    (ENNReal.ofReal ((10:ℝ)⁻¹^17)*ThresholdHC.EntropyTail.selection μ ρ (B/Real.log (1/δ)))/30 ≤
      rareConfidenceRadius μ ρ B δ := entropy_tail_confidence_lower μ hr hu hb hd hd'
""".lstrip()
    roots = {"ThresholdHC.ConfidenceTransfer." + name for name in [
        "finite_reference_work_kl", "finite_null_work_kl", "local_reference_of_null",
        "creation_reference_work_kl", "creation_null_work_kl", "observable_reference_work_kl",
        "observable_null_work_kl", "stopped_reference_work_kl", "stopped_null_work_kl",
        "pair_reference_confidence_work", "pair_confidence_work",
    ]}
    roots.update({"ThresholdHC.ConfidenceProgram." + name for name in [
        "midpoint_reference_bound", "quartet_confidence", "stopping_confidence_lower", "entropy_tail_confidence_lower",
    ]})
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ConfidenceProgram.Lower"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
