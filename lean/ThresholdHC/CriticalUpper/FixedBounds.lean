import ThresholdHC.CriticalUpper.FixedIdentities
import ThresholdHC.CriticalUpper.Simulation

/-! Expected work and squared error of the original observable batch estimator. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory ProbabilityTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

theorem measurable_criticalArrayWork (ρ : ℝ) (n : ℕ) : Measurable (criticalArrayWork ρ n) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_stoppedProcedureWork (criticalUnbiasedProcedure ρ)).comp (measurable_pi_apply i.val)

theorem fixed_expectedWork_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) (n : ℕ) :
    criticalExpectedWork (fixedEstimator ρ n) q hq ≤
      ENNReal.ofReal (((n : ℝ)+1)*(112000000*criticalLogFactor ρ)) := by
  rw [critical_expectedWork_simulation]
  change (∫⁻ z, totalProcessWork (populationPath (fixedPolicy ρ (n+1) z.1) z.2)
    ∂criticalSeedLaw.prod (Measure.infinitePi (fun _ : ℕ => criticalTapeLaw q))) ≤ _
  simp_rw [fixed_population_work]
  rw [(criticalCalls_preserving q hq).lintegral_comp (measurable_criticalArrayWork ρ n)]
  exact criticalArrayWork_bound ρ hρ hρ1 q hq hmass n

theorem fixed_squaredRisk_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) (n : ℕ) :
    squaredRisk (criticalExperimentLaw (fixedEstimator ρ n) q hq)
      (fun z => (fixedEstimator ρ n).output (z.1.1,z.2)) (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤
      ENNReal.ofReal (28*ρ/((n : ℝ)+1)) := by
  rw [critical_squaredRisk_simulation]
  change (∫⁻ z, ENNReal.ofReal ((fixedOutput ρ (n+1) (z.1,populationPath (fixedPolicy ρ (n+1) z.1) z.2)-
    (∫ d, (q d : ℝ) ∂criticalGapLaw))^2)
    ∂criticalSeedLaw.prod (Measure.infinitePi (fun _ : ℕ => criticalTapeLaw q))) ≤ _
  simp_rw [fixed_population_output]
  have hm : Measurable (fun z => ENNReal.ofReal ((criticalAverage ρ n z-
      (∫ d, (q d : ℝ) ∂criticalGapLaw))^2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_productionAverage
      (criticalUnbiasedProcedure ρ).output (criticalUnbiasedProcedure ρ).measurable_output n).sub
        measurable_const).pow_const 2)
  rw [(criticalCalls_preserving q hq).lintegral_comp hm]
  exact criticalAverage_mse ρ hρ hρ1 q hq hmass n

end ThresholdHC.CriticalUpper
