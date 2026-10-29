import ThresholdHC.RareAboveTwo.FixedIdentities

/-! Expected work and squared error of the original observable batch estimator. -/

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ProbabilityTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

theorem measurable_rareArrayWork (a ρ : ℝ) (n : ℕ) : Measurable (rareArrayWork a ρ n) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_stoppedProcedureWork (rareUnbiasedProcedure a ρ)).comp (measurable_pi_apply i.val)

theorem fixed_expectedWork_bound (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (a ρ W : ℝ) (hwork : (∫⁻ z, stoppedProcedureWork (rareUnbiasedProcedure a ρ) z
      ∂samplingMeasure (originalPopulationTapeLaw μ q)) ≤ ENNReal.ofReal W) (n : ℕ) :
    expectedWork μ (fixedEstimator a ρ n) q ≤
      ENNReal.ofReal (((n : ℝ)+1)*(W)) := by
  rw [original_expectedWork_simulation]
  change (∫⁻ z, totalProcessWork (populationPath (fixedPolicy a ρ (n+1) z.1) z.2)
    ∂rareSeedLaw.prod (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))) ≤ _
  simp_rw [fixed_population_work]
  rw [(rareCalls_preserving μ q).lintegral_comp (measurable_rareArrayWork a ρ n)]
  exact rareArrayWork_bound μ q a ρ W hwork n

theorem fixed_squaredRisk_bound (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a) (q : SignLaw)
    (hq : RarePrior μ ρ q) (n : ℕ) :
    squaredRisk (experimentLaw μ (fixedEstimator a ρ n) q)
      (populationOutput (fixedEstimator a ρ n)) (signMean μ q.val) ≤
      ENNReal.ofReal (28*ρ/((n : ℝ)+1)) := by
  rw [original_squaredRisk_simulation]
  change (∫⁻ z, ENNReal.ofReal ((fixedOutput a ρ (n+1) (z.1,populationPath (fixedPolicy a ρ (n+1) z.1) z.2)-
    (signMean μ q.val))^2)
    ∂rareSeedLaw.prod (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))) ≤ _
  simp_rw [fixed_population_output]
  have hmeas : Measurable (fun z => ENNReal.ofReal ((rareAverage a ρ n z-
      (signMean μ q.val))^2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_productionAverage
      (rareUnbiasedProcedure a ρ).output (rareUnbiasedProcedure a ρ).measurable_output n).sub
        measurable_const).pow_const 2)
  rw [(rareCalls_preserving μ q).lintegral_comp hmeas]
  exact rareAverage_mse μ α a ρ hα ha ha' hρ hρ1 hm q hq n

end ThresholdHC.RareAboveTwo
