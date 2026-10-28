import ThresholdHC.CriticalUpper.CoinLaw
import ThresholdHC.CriticalEntropy.CriticalExperiment
import ThresholdHC.ObservableSimulation.PopulationLaw

/-! Exact observable-law and risk/work transfer from the original critical experiment. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.Tier3 ThresholdHC.Tier6
open scoped ENNReal

def criticalSimulationLaw {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) (q : ℝ → unitInterval) : Measure (R × (ℕ → ℕ → Bool)) :=
  A.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => criticalTapeLaw q))

theorem critical_observable_simulation_law {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q) :
    (criticalExperimentLaw A q hq).map (fun z => (z.1.1,z.2)) =
      (criticalSimulationLaw A q).map (fun z => (z.1,populationPath (A.policy z.1) z.2)) := by
  exact population_simulation_observable_law A.randomLaw criticalGapLaw (criticalExperimentLaw A q hq)
    Prod.fst Prod.snd (fun d => criticalParameter d false) (fun d => criticalParameter d true) q
    (measurable_criticalParameter false) (measurable_criticalParameter true) hq
    criticalClippedGap measurable_criticalClippedGap criticalClippedGap_bounds
    criticalClipped_parameters.1 criticalClipped_parameters.2
    A.policy A.policy_measurable measurable_fst measurable_snd (criticalExperimentLaw_realizes A q hq)

theorem critical_observable_lintegral {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q)
    (F : R × ProcessTape → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (z.1.1,z.2) ∂criticalExperimentLaw A q hq) =
      ∫⁻ z, F (z.1,populationPath (A.policy z.1) z.2) ∂criticalSimulationLaw A q := by
  have hm : Measurable (fun z : R × (ℕ → ℕ → Bool) =>
      (z.1,populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun xs => measurable_to_countable' (A.policy_measurable xs)))
  have hm₀ : Measurable (fun z : (R × (ℕ → ℝ)) × ProcessTape => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  calc
    _ = ∫⁻ z, F z ∂(criticalExperimentLaw A q hq).map (fun z => (z.1.1,z.2)) :=
      (lintegral_map hF hm₀).symm
    _ = _ := by rw [critical_observable_simulation_law,lintegral_map hF hm]

theorem critical_expectedWork_simulation {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q) :
    criticalExpectedWork A q hq =
      ∫⁻ z, totalProcessWork (populationPath (A.policy z.1) z.2) ∂criticalSimulationLaw A q := by
  apply critical_observable_lintegral A q hq (fun z => totalProcessWork z.2)
  exact measurable_totalProcessWork (Prod.snd : R × ProcessTape → ProcessTape) (fun n b =>
    measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const)

theorem critical_squaredRisk_simulation {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q) (a : ℝ) :
    squaredRisk (criticalExperimentLaw A q hq) (fun z => A.output (z.1.1,z.2)) a =
      ∫⁻ z, ENNReal.ofReal ((A.output (z.1,populationPath (A.policy z.1) z.2)-a)^2)
        ∂criticalSimulationLaw A q := by
  apply critical_observable_lintegral A q hq (fun z => ENNReal.ofReal ((A.output z-a)^2))
  exact ((A.output_measurable.sub measurable_const).pow_const 2).ennreal_ofReal

end ThresholdHC.CriticalUpper
