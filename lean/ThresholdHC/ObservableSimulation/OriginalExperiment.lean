import ThresholdHC.ObservableSimulation.PopulationLaw
import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.Tier6.Process

noncomputable section

namespace ThresholdHC.ObservableSimulation
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.Tier6
open scoped ENNReal

def gapParameter (s : Bool) (d : Gap) : unitInterval :=
  ⟨1/2 + (if s then (d : ℝ) else -(d : ℝ)), by
    have hd := d.property
    cases s <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> linarith⟩

theorem measurable_gapParameter (s : Bool) : Measurable (gapParameter s) := by
  apply Measurable.subtype_mk
  cases s <;> simp only [gapParameter,
    Bool.false_eq_true,ite_false,ite_true]
  · exact measurable_const.add measurable_subtype_coe.neg
  · exact measurable_const.add measurable_subtype_coe

def signUnit (q : SignLaw) (d : Gap) : unitInterval := ⟨q.val d,q.property.2 d⟩

theorem measurable_signUnit (q : SignLaw) : Measurable (signUnit q) :=
  q.property.1.subtype_mk

/-- The actual marginal law of one population coin's complete iid tape. -/
def originalPopulationTapeLaw (μ : Measure Gap) (q : SignLaw) : Measure (ℕ → Bool) :=
  parameterTapeLaw (populationParameterLaw μ (gapParameter false) (gapParameter true) (signUnit q))

instance originalPopulationTapeLaw_probability (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    IsProbabilityMeasure (originalPopulationTapeLaw μ q) := by
  letI := populationParameterLaw_probability μ (gapParameter false) (gapParameter true) (signUnit q)
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
  exact parameterTapeLaw_probability _

def originalSimulationLaw {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) (A : AdaptiveEstimator R) (q : SignLaw) : Measure (R × (ℕ → ℕ → Bool)) :=
  A.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))

theorem original_observable_simulation_law {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    (experimentLaw μ A q).map (fun z => (z.1.1,z.2)) =
      (originalSimulationLaw μ A q).map (fun z => (z.1,populationPath (A.policy z.1) z.2)) := by
  apply population_simulation_observable_law A.randomLaw μ (experimentLaw μ A q)
    Prod.fst Prod.snd (gapParameter false) (gapParameter true) (signUnit q)
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
    (fun d : Gap => (d : ℝ)) measurable_subtype_coe
    (fun d => ⟨d.property.1.le,d.property.2⟩)
    (ae_of_all _ (fun d => by simp [gapParameter,sub_eq_add_neg]))
    (ae_of_all _ (fun d => by simp [gapParameter]))
    A.policy A.policy_measurable measurable_fst measurable_snd
  exact creationProcessLaw_realizes (populationSeedLaw μ A) (populationPolicy A)
    populationGap (populationPrior q) (measurable_populationPolicy A)
    measurable_populationGap (measurable_populationPrior q)
    populationGap_range (populationPrior_range q)

theorem original_observable_lintegral {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (F : R × ProcessTape → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (z.1.1,z.2) ∂experimentLaw μ A q) =
      ∫⁻ z, F (z.1,populationPath (A.policy z.1) z.2) ∂originalSimulationLaw μ A q := by
  have hm : Measurable (fun z : R × (ℕ → ℕ → Bool) =>
      (z.1,populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun xs => measurable_to_countable' (A.policy_measurable xs)))
  have hm₀ : Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1,z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  calc
    _ = ∫⁻ z, F z ∂(experimentLaw μ A q).map (fun z => (z.1.1,z.2)) :=
      (lintegral_map hF hm₀).symm
    _ = _ := by rw [original_observable_simulation_law,lintegral_map hF hm]

theorem original_expectedWork_simulation {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    expectedWork μ A q =
      ∫⁻ z, totalProcessWork (populationPath (A.policy z.1) z.2) ∂originalSimulationLaw μ A q := by
  apply original_observable_lintegral μ A q (fun z => totalProcessWork z.2)
  exact measurable_totalProcessWork (Prod.snd : R × ProcessTape → ProcessTape) (fun n b =>
    measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const)

theorem original_squaredRisk_simulation {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) (a : ℝ) :
    squaredRisk (experimentLaw μ A q) (populationOutput A) a =
      ∫⁻ z, ENNReal.ofReal ((A.output (z.1,populationPath (A.policy z.1) z.2)-a)^2)
        ∂originalSimulationLaw μ A q := by
  apply original_observable_lintegral μ A q (fun z => ENNReal.ofReal ((A.output z-a)^2))
  exact ((A.output_measurable.sub measurable_const).pow_const 2).ennreal_ofReal

end ThresholdHC.ObservableSimulation
