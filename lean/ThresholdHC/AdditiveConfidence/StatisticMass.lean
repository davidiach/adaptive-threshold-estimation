import ThresholdHC.AdditiveConfidence.StatisticMixture

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

theorem GapMixture.statistic_mass {I R E : Type} [Fintype I]
    [MeasurableSpace R] [MeasurableSpace E] {μ : Measure Gap} [IsProbabilityMeasure μ]
    (M : GapMixture I μ) (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q : I → SignLaw) (hq : ∀ i d, (q i).val d ≤ 1/2)
    (A : StoppedProcedure R E) (n : ℕ) (z : Fin (n+1) × Fin (n+1)) :
    (cappedStatisticLaw μ ν p₀ p₁ (signUnit (M.mixedSign q)) A n).real {z} =
      (tapeStatisticLaw ν (M.residual.map p₀) A n).real {z}+
        ∑ i, (M.weight i : ℝ)*(cappedStatisticLaw (M.law i) ν p₀ p₁ (signUnit (q i)) A n).real {z} := by
  let (i : I) : IsProbabilityMeasure (cappedStatisticLaw (M.law i) ν p₀ p₁ (signUnit (q i)) A n) :=
    cappedStatisticLaw_probability _ _ _ _ _ h₀ h₁ (measurable_signUnit _) A n
  rw [M.statistic_law ν p₀ p₁ h₀ h₁ q hq A n,measureReal_add_apply]
  congr 1
  simp only [Measure.real,Measure.finsetSum_apply,Measure.smul_apply,ENNReal.smul_def,smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul,ENNReal.coe_toReal]

theorem GapMixture.statistic_mass_balance {I R E : Type} [Fintype I]
    [MeasurableSpace R] [MeasurableSpace E] {μ : Measure Gap} [IsProbabilityMeasure μ]
    (M : GapMixture I μ) (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ : Gap → unitInterval) (h₀ : Measurable p₀) (A : StoppedProcedure R E) (n : ℕ) :
    (∑ z, (tapeStatisticLaw ν (M.residual.map p₀) A n).real {z})+
      ∑ i, (M.weight i : ℝ) = 1 := by
  have he : (∑ z, (tapeStatisticLaw ν (M.residual.map p₀) A n).real {z}) =
      M.residual.real Set.univ := by
    calc
      _ = (tapeStatisticLaw ν (M.residual.map p₀) A n).real Set.univ := by
        simp
      _ = (M.residual.map p₀).real Set.univ := tapeStatisticLaw_mass ν _ A n
      _ = M.residual.real Set.univ := by
        simp only [Measure.real,Measure.map_apply h₀ MeasurableSet.univ,Set.preimage_univ]
  rw [he]
  exact M.mass_balance

end ThresholdHC.AdditiveConfidence
