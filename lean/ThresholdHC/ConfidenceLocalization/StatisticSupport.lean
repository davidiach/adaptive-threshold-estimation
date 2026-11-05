import ThresholdHC.ConfidenceLocalization.CappedMixture

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

theorem statistic_mass_midpoint {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (n : ℕ)
    (i : Fin (n+1) × Fin (n+1)) :
    (cappedStatisticLaw μ ν p₀ p₁ (midpointPrior q r) A n).real {i} =
      ((cappedStatisticLaw μ ν p₀ p₁ q A n).real {i}+
        (cappedStatisticLaw μ ν p₀ p₁ r A n).real {i})/2 := by
  let := cappedStatisticLaw_probability μ ν p₀ p₁ q h₀ h₁ hq A n
  let := cappedStatisticLaw_probability μ ν p₀ p₁ r h₀ h₁ hr A n
  rw [statistic_law_midpoint μ ν p₀ p₁ q r h₀ h₁ hq hr A n]
  simp only [Measure.real,Measure.add_apply,Measure.smul_apply,ENNReal.smul_def,smul_eq_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul,ENNReal.coe_toReal,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
  ring

theorem statistic_common_support {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/2)
    (A : StoppedProcedure R E) (n : ℕ) (i : Fin (n+1) × Fin (n+1))
    (hz : (cappedStatisticLaw μ ν p₀ p₁ (fun _ => c) A n).real {i} = 0) :
    (cappedStatisticLaw μ ν p₀ p₁ q A n).real {i} = 0 := by
  let := cappedStatisticLaw_probability μ ν p₀ p₁ q h₀ h₁ hq A n
  let := cappedStatisticLaw_probability μ ν p₀ p₁ (fun _ => c) h₀ h₁ measurable_const A n
  have h := Measure.le_iff'.mp (statistic_law_const_domination μ ν p₀ p₁ q h₀ h₁ hq c hc A n) {i}
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) h
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal c.property.1] at hr
  change (c : ℝ)*(cappedStatisticLaw μ ν p₀ p₁ q A n).real {i} ≤
    (cappedStatisticLaw μ ν p₀ p₁ (fun _ => c) A n).real {i} at hr
  rw [hz] at hr
  apply le_antisymm ?_ measureReal_nonneg
  by_contra! hbad
  have hp := mul_pos hc0 hbad
  linarith

end ThresholdHC.ConfidenceLocalization
