import ThresholdHC.ClippingBoundary.Kurtosis

/-! The uniform clipped floor in the original experiment.

For a rare sign law `q` the target `signMean μ q.val` lies in `[0,ρ]`, so the
RMS transfer applies to the raw output under `experimentLaw μ A q`. That
clipped RMS is the `q` term of `rareRisk μ (clippedEstimator A ρ) ρ`. The left
side is rewritten as a supremum over rare sign laws by moving the square root,
the minimum with `ρ` and the constant factor through the supremum. -/
noncomputable section
namespace ThresholdHC.ClippingBoundary
open MeasureTheory
open ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.RareAboveTwo
  ThresholdHC.RobustContinuation

/-- The square root, the minimum with `a` and the factor `c` commute with a supremum. -/
theorem mul_min_iSup_rpow {ι : Sort*} (c a : ENNReal) (f : ι → ENNReal) :
    c * min a ((⨆ i, f i) ^ (1 / 2 : ℝ)) = ⨆ i, c * min a (f i ^ (1 / 2 : ℝ)) := by
  rw [ENNReal.iSup_rpow_of_pos (by norm_num), ← ENNReal.mul_iSup]
  congr 1
  exact inf_iSup_eq a _

/-- One rare sign law: the `q` term of the uniform floor, in `ℝ≥0∞` with
`evariance`. -/
theorem rare_term_floor {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) {ρ K : ℝ} (hK : 1 ≤ K) (q : SignLaw) (hq : RarePrior μ ρ q)
    (h4mem : MemLp (populationOutput A) 4 (experimentLaw μ A q))
    (hmean : (∫ z, populationOutput A z ∂experimentLaw μ A q) = signMean μ q.val)
    (h4 : (∫ z, (populationOutput A z - signMean μ q.val) ^ 4 ∂experimentLaw μ A q) ≤
      K * ProbabilityTheory.variance (populationOutput A) (experimentLaw μ A q) ^ 2) :
    ENNReal.ofReal (1 / (16 * K)) * min (ENNReal.ofReal ρ)
      (ProbabilityTheory.evariance (populationOutput A) (experimentLaw μ A q) ^ (1 / 2 : ℝ)) ≤
      rootMeanRisk (experimentLaw μ (clippedEstimator A ρ) q)
        (populationOutput (clippedEstimator A ρ)) (signMean μ q.val) := by
  have hθ0 : 0 ≤ signMean μ q.val := integral_nonneg (fun d => (q.property.2 d).1)
  have hK0 : 0 < K := by linarith
  have h := clipped_rms_floor (P := experimentLaw μ A q) (populationOutput A) (signMean μ q.val)
    ρ K h4mem hmean hθ0 hq hK h4
  set v := ProbabilityTheory.variance (populationOutput A) (experimentLaw μ A q) with hv
  have hv0 : 0 ≤ v := ProbabilityTheory.variance_nonneg _ _
  have hev : ProbabilityTheory.evariance (populationOutput A) (experimentLaw μ A q) =
      ENNReal.ofReal v :=
    (ProbabilityTheory.ofReal_variance (h4mem.mono_exponent (by norm_num))).symm
  rw [hev, ENNReal.ofReal_rpow_of_nonneg hv0 (by norm_num), ← Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_min, ← ENNReal.ofReal_mul (by positivity), one_div_mul_eq_div]
  exact h

end ThresholdHC.ClippingBoundary
