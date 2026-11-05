"""Check physical caps, confidence amplification and the two minimax rates."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ConfidenceProgram.Upper
noncomputable section
open MeasureTheory ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.HardBudget ThresholdHC.Confidence ThresholdHC.ConfidenceProgram
open ThresholdHC.ConfidenceTransfer ThresholdHC.EntropyTail ThresholdHC.CriticalUpper
open scoped ENNReal

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (m N : ℕ) (M : ℝ) :
    PathwiseCap (cappedMedian A m N M) ((2*m+1)*N) := cappedMedian_cap A m N M

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (m N : ℕ) (M : ℝ) (r : ℕ → R) (s : Table) :
    (cappedMedian A m N M).output (r,populationPath ((cappedMedian A m N M).policy r) s) =
      median m (fun i => localValue M (outcome A N M (stageInputs (r,s) i.val))) :=
  cappedMedian_output A m N M r s

example {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (m : ℕ) {B M r δ : ℝ}
    (hb : 0 < B) (hd : 0 ≤ δ) (hm : (3/4:ℝ)^(2*m+1) ≤ δ^2)
    (hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ M) (hr : 0 ≤ r)
    (hw : expectedWork μ A q ≤ ENNReal.ofReal (B/(8*(2*(m:ℝ)+1))))
    (hR : rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) ≤ ENNReal.ofReal r) :
    let n := ⌊B/(2*(m:ℝ)+1)⌋₊
    PathwiseCap (cappedMedian A m n M) ⌊B⌋₊ ∧
      failureProbability μ (cappedMedian A m n M) q (Real.sqrt 8*r) ≤ ENNReal.ofReal δ :=
  capped_median_at_level μ A q m hb hd hm hθ hr hw hR

example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    let K := selection μ ρ (B/Real.log (1/δ))
    ENNReal.ofReal ((10:ℝ)⁻¹^17)*K/30 ≤ rareConfidenceRadius μ ρ B δ ∧
      rareConfidenceRadius μ ρ B δ ≤ hardConfidenceRadius μ ρ B δ ∧
      hardConfidenceRadius μ ρ B δ ≤ 750000*K := general_confidence_rate μ hr hu hb hd hd'

example : ∃ c : ℝ, 0 < c ∧ ∀ (ρ B δ : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
    let z := min ρ (Real.sqrt (ρ*ThresholdHC.CriticalEntropy.criticalLogFactor ρ*Real.log (1/δ)/B))
    ENNReal.ofReal (c*z) ≤ rareConfidenceRadius criticalPositiveLaw ρ B δ ∧
      rareConfidenceRadius criticalPositiveLaw ρ B δ ≤ hardConfidenceRadius criticalPositiveLaw ρ B δ ∧
      hardConfidenceRadius criticalPositiveLaw ρ B δ ≤ ENNReal.ofReal (2670000*z) := critical_confidence_rate
""".lstrip()
    roots = {"ThresholdHC.ConfidenceProgram." + name for name in [
        "independent_words", "observed_block", "cappedMedian_cap", "stageResult_value", "cappedMedian_output",
        "single_capped_failure", "quarter_majority", "capped_median_failure", "median_budget_cap",
        "hard_median_transfer", "capped_median_at_level", "schedule_failure", "baseBudget_scale",
        "expected_confidence_le_hard", "hard_confidence_of_base", "general_hard_confidence_upper",
        "critical_hard_confidence_upper", "general_confidence_rate", "critical_confidence_rate",
    ]}
    roots.update({"ThresholdHC.HardBudget." + name for name in ["stopAt_pathwise_cap", "timeout_work", "rare_base"]})
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ConfidenceProgram.Upper"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
