"""Verify the CDF-defined unknown-law envelope in the observable statistical experiment."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.Envelope.Minimax
import ThresholdHC.Envelope.Unbiased
noncomputable section
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.Confidence ThresholdHC.Envelope
open scoped ENNReal

example (μ ν : Measure Gap) [IsProbabilityMeasure μ]
    (h : ∀ t : ℝ, 0 < t → ν {d : Gap | (d:ℝ) ≤ t} ≤ μ {d : Gap | (d:ℝ) ≤ t})
    {a : ℝ} (ha : 0 < a) : modulus ν a ≤ modulus μ a := modulus_le μ ν h ha

example (μ ν : Measure Gap) (h : Within μ ν) (hi : Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) :
    Integrable (fun d : Gap => (d:ℝ)⁻¹) ν ∧
      (∫ d : Gap, (d:ℝ)⁻¹ ∂ν) ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂μ := inverse_moment_le μ ν h hi

example (μ : Measure Gap) [IsProbabilityMeasure μ] {B : ℝ} (h : 1 ≤ B) :
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/64) ≤ minimaxRMS μ B ∧
      minimaxRMS μ B ≤ ENNReal.ofReal (512*modulus μ (1/Real.sqrt B)) := rms_bounds μ h

example (μ : Measure Gap) [IsProbabilityMeasure μ] {B δ : ℝ} (hb : 1 ≤ B) (hd : 0 < δ) (hu : δ ≤ 1/4) :
    ENNReal.ofReal ((15/(256*Real.sqrt 2))*modulus μ (confidenceScale B δ)) ≤ minimaxRadius μ B δ ∧
      minimaxRadius μ B δ ≤ ENNReal.ofReal (8192*modulus μ (confidenceScale B δ)) :=
  confidence_bounds μ hb hd hu

example (μ : Measure Gap) [IsProbabilityMeasure μ] :
    (∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R) (V W : ℝ),
      0 ≤ V ∧ 0 ≤ W ∧ UnbiasedAt μ A V W) ↔ Integrable (fun d : Gap => (d:ℝ)⁻¹) μ := unbiased_iff μ

example (μ : Measure Gap) [IsProbabilityMeasure μ] (hi : Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) :
    let I := ∫ d : Gap, (d:ℝ)⁻¹ ∂μ
    ENNReal.ofReal (I^2/16) ≤ varianceWork μ ∧ varianceWork μ ≤ ENNReal.ofReal (713*I^2) :=
  variance_work_bounds μ hi
""".lstrip()
    roots = {"ThresholdHC.Envelope." + name for name in [
        "within_self", "modulus_le", "inverse_moment_le", "blind_rms_upper", "rms_bounds",
        "blind_confidence_upper", "confidence_bounds", "blind_unbiased_upper", "unbiased_lower",
        "unbiased_iff", "variance_work_bounds",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.Envelope.Minimax", "ThresholdHC.Envelope.Unbiased"],
                   cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
