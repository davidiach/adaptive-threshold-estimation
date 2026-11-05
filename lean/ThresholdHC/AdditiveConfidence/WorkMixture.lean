import ThresholdHC.AdditiveConfidence.Decomposition

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy

theorem GapMixture.work_decomposition {I R E : Type} [Fintype I]
    [MeasurableSpace R] [MeasurableSpace E] {μ : Measure Gap} [IsProbabilityMeasure μ]
    (M : GapMixture I μ) (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : Gap → unitInterval) (A : StoppedProcedure R E) :
    populationExpectedWork μ ν p₀ p₁ q A =
      populationExpectedWork M.residual ν p₀ p₁ q A+
        ∑ i, (M.weight i : ℝ≥0∞)*populationExpectedWork (M.law i) ν p₀ p₁ q A := by
  have he := congrArg (fun η => populationExpectedWork η ν p₀ p₁ q A) M.eq_measure
  conv_lhs => rw [he]
  simp only [populationExpectedWork,populationMeasure,Measure.add_prod,
    ← Measure.sum_fintype,Measure.prod_sum_left,Measure.prod_smul_left,
    lintegral_add_measure,lintegral_sum_measure,lintegral_smul_measure,
    tsum_fintype,ENNReal.smul_def,smul_eq_mul]

theorem GapMixture.component_work_le {I R E : Type} [Fintype I]
    [MeasurableSpace R] [MeasurableSpace E] {μ : Measure Gap} [IsProbabilityMeasure μ]
    (M : GapMixture I μ) (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : Gap → unitInterval) (A : StoppedProcedure R E)
    (n : ℕ) (hcap : ∀ z, A.stop z ≤ n) :
    (∑ i, (M.weight i : ℝ)*(populationExpectedWork (M.law i) ν p₀ p₁ q A).toReal) ≤
      (populationExpectedWork μ ν p₀ p₁ q A).toReal := by
  have hfin (η : Measure Gap) [IsProbabilityMeasure η] :
      populationExpectedWork η ν p₀ p₁ q A ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) (population_capped_work_le η ν p₀ p₁ q A n hcap)
  have hle : (∑ i, (M.weight i : ℝ≥0∞)*populationExpectedWork (M.law i) ν p₀ p₁ q A) ≤
      populationExpectedWork μ ν p₀ p₁ q A := by
    rw [M.work_decomposition ν p₀ p₁ q A]
    exact le_add_left le_rfl
  have h := ENNReal.toReal_mono (hfin μ) hle
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.coe_ne_top (hfin (M.law i)))] at h
  simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal] using h

end ThresholdHC.AdditiveConfidence
