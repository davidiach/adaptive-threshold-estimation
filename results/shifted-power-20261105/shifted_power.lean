import ThresholdHC.ShiftedPower.Full
import ThresholdHC.ShiftedPower.Constants
noncomputable section
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile
open ThresholdHC.Confidence ThresholdHC.ConfidenceTransfer ThresholdHC.ConfidenceProgram
open ThresholdHC.HardBudget ThresholdHC.ShiftedPower
open scoped ENNReal

example (μ : Measure Gap) [IsProbabilityMeasure μ] {a ρ h : ℝ}
    (hm : ExactPowerLaw μ 1 a) (ha : 0 < a) (hr : 0 < ρ) (hu : ρ ≤ 1) (hh : 0 < h) :
    min ρ ((h/a)*(1+max 0 (Real.log (ρ/(h/a))))) ≤ tailModulus (quantileTail μ ρ) h :=
  linear_tail μ hm ha hr hu hh

example (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ h : ℝ}
    (hm : ExactPowerLaw μ α a) (hα : 0 < α) (ha : 0 < a) (hr : 0 < ρ) (hu : ρ ≤ 1) (hh : 0 < h) :
    min ρ (ρ^(1-1/α)*(h/a)) ≤ tailModulus (quantileTail μ ρ) h :=
  intermediate_tail μ hm hα ha hr hu hh

example {a ρ B : ℝ} (ha : 0 < a) (ha' : a ≤ 1) (hr : 0 < ρ) (hr' : ρ ≤ 1) (hB : 0 < B) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν 1 a →
      RareBudget ν A ρ B ∧ rareRisk ν A ρ ≤ ENNReal.ofReal (linearConstant*linearRate ρ ((Real.sqrt B)⁻¹/a)) :=
  linear_rms_family ha ha' hr hr' hB

example {α a ρ B : ℝ} (hα : 1 < α) (hu : α < 2) (ha : 0 < a) (ha' : a ≤ 1)
    (hr : 0 < ρ) (hr' : ρ ≤ 1) (hB : 0 < B) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
      RareBudget ν A ρ B ∧ rareRisk ν A ρ ≤ ENNReal.ofReal (intermediateConstant α*intermediateRate α ρ ((Real.sqrt B)⁻¹/a)) :=
  intermediate_rms_family hα hu ha ha' hr hr' hB

example {a ρ B δ : ℝ} (ha : 0 < a) (ha' : a ≤ 1) (hr : 0 < ρ) (hr' : ρ ≤ 1)
    (hB : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R), PathwiseCap A ⌊B⌋₊ ∧
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν 1 a →
      RareBudget ν A ρ B ∧ ∀ q : SignLaw, RarePrior ν ρ q →
        failureProbability ν A q (27*linearConstant*linearRate ρ (confidenceScale B δ/a)) ≤ ENNReal.ofReal δ :=
  linear_confidence_family ha ha' hr hr' hB hd hd'

example {α a ρ B δ : ℝ} (hα : 1 < α) (hu : α < 2) (ha : 0 < a) (ha' : a ≤ 1)
    (hr : 0 < ρ) (hr' : ρ ≤ 1) (hB : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R), PathwiseCap A ⌊B⌋₊ ∧
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
      RareBudget ν A ρ B ∧ ∀ q : SignLaw, RarePrior ν ρ q →
        failureProbability ν A q (27*intermediateConstant α*intermediateRate α ρ (confidenceScale B δ/a)) ≤ ENNReal.ofReal δ :=
  intermediate_confidence_family hα hu ha ha' hr hr' hB hd hd'

example (μ : Measure Gap) [IsProbabilityMeasure μ] {a ρ B δ : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1) (hm : ExactPowerLaw μ 1 a) (hr : 0 < ρ) (hu : ρ ≤ 1/4)
    (hB : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    let z := linearRate ρ ((Real.sqrt B)⁻¹/a)
    let w := linearRate ρ (confidenceScale B δ/a)
    (ENNReal.ofReal (z/32) ≤ rareMinimaxRisk μ ρ B ∧ rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (linearConstant*z)) ∧
    (ENNReal.ofReal (w/960) ≤ rareConfidenceRadius μ ρ B δ ∧ rareConfidenceRadius μ ρ B δ ≤ hardConfidenceRadius μ ρ B δ ∧
      hardConfidenceRadius μ ρ B δ ≤ ENNReal.ofReal (27*linearConstant*w)) :=
  linear_rates μ ha ha' hm hr hu hB hd hd'

example (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ B δ : ℝ}
    (hα : 1 < α) (hu : α < 2) (ha : 0 < a) (ha' : a ≤ 1) (hm : ExactPowerLaw μ α a)
    (hr : 0 < ρ) (hr' : ρ ≤ 1/4) (hB : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    let z := intermediateRate α ρ ((Real.sqrt B)⁻¹/a)
    let w := intermediateRate α ρ (confidenceScale B δ/a)
    (ENNReal.ofReal (z/32) ≤ rareMinimaxRisk μ ρ B ∧ rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (intermediateConstant α*z)) ∧
    (ENNReal.ofReal (w/960) ≤ rareConfidenceRadius μ ρ B δ ∧ rareConfidenceRadius μ ρ B δ ≤ hardConfidenceRadius μ ρ B δ ∧
      hardConfidenceRadius μ ρ B δ ≤ ENNReal.ofReal (27*intermediateConstant α*w)) :=
  intermediate_rates μ hα hu ha ha' hm hr hr' hB hd hd'

example : linearConstant ≤ 287 := linearConstant_le
example {α : ℝ} (hα : 0 < α) (hu : α < 2) : workConstant α = 68*(α+2)/(2-α)^2 := workConstant_formula hα hu
#print axioms ThresholdHC.ShiftedPower.amplify_margin
#print axioms ThresholdHC.ShiftedPower.amplitude_identity
#print axioms ThresholdHC.ShiftedPower.base_level
#print axioms ThresholdHC.ShiftedPower.certificate_formula
#print axioms ThresholdHC.ShiftedPower.classifierCall_difference
#print axioms ThresholdHC.ShiftedPower.classifierCall_error
#print axioms ThresholdHC.ShiftedPower.classifierCall_work
#print axioms ThresholdHC.ShiftedPower.finite_bias_level
#print axioms ThresholdHC.ShiftedPower.increment_variance
#print axioms ThresholdHC.ShiftedPower.intermediate_certificate
#print axioms ThresholdHC.ShiftedPower.intermediate_confidence_family
#print axioms ThresholdHC.ShiftedPower.intermediate_lower
#print axioms ThresholdHC.ShiftedPower.intermediate_rates
#print axioms ThresholdHC.ShiftedPower.intermediate_rms_family
#print axioms ThresholdHC.ShiftedPower.intermediate_scale
#print axioms ThresholdHC.ShiftedPower.intermediate_tail
#print axioms ThresholdHC.ShiftedPower.linearConstant_le
#print axioms ThresholdHC.ShiftedPower.linear_certificate
#print axioms ThresholdHC.ShiftedPower.linear_confidence_family
#print axioms ThresholdHC.ShiftedPower.linear_levels
#print axioms ThresholdHC.ShiftedPower.linear_lower
#print axioms ThresholdHC.ShiftedPower.linear_rates
#print axioms ThresholdHC.ShiftedPower.linear_rms_family
#print axioms ThresholdHC.ShiftedPower.linear_scale
#print axioms ThresholdHC.ShiftedPower.linear_tail
#print axioms ThresholdHC.ShiftedPower.log_work_bound
#print axioms ThresholdHC.ShiftedPower.lower_from_quantile
#print axioms ThresholdHC.ShiftedPower.population_bias
#print axioms ThresholdHC.ShiftedPower.population_classifier_bias
#print axioms ThresholdHC.ShiftedPower.population_classifier_difference
#print axioms ThresholdHC.ShiftedPower.population_classifier_work
#print axioms ThresholdHC.ShiftedPower.population_nonnegative_bound
#print axioms ThresholdHC.ShiftedPower.power_kernel_bound
#print axioms ThresholdHC.ShiftedPower.shifted_bounds
#print axioms ThresholdHC.ShiftedPower.workConstant_formula
