import ThresholdHC.ObservedState.Targets
import ThresholdHC.ObservableSimulation.OriginalExperiment

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.ObservedState
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation

local instance (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

/-- An adaptive estimator on a finite collection of persistent cells. -/
structure Estimator (m : ℕ) (R : Type) [MeasurableSpace R] where
  randomLaw : Measure R
  probability : IsProbabilityMeasure randomLaw
  policy : R → List Bool → Option (Fin m)
  policy_measurable : MeasurablePolicy policy
  output : R × ProcessTape → ℝ
  output_measurable : Measurable output

instance estimator_probability {m : ℕ} {R : Type} [MeasurableSpace R] (A : Estimator m R) :
    IsProbabilityMeasure A.randomLaw := A.probability

def modelLaw {m : ℕ} {R : Type} [MeasurableSpace R] (A : Estimator m R)
    (d : Fin m → Gap) (s : Fin m → Bool) : Measure (R × ProcessTape) :=
  (A.randomLaw.prod (Measure.pi (fun i => ThresholdHC.Tier2.tapeMeasure (gapParameter (s i) (d i))))).map
    (fun z => (z.1,populationPath (A.policy z.1) z.2))

theorem measurable_observation {m : ℕ} {R : Type} [MeasurableSpace R] (A : Estimator m R) :
    Measurable (fun z : R × (Fin m → ℕ → Bool) => (z.1,populationPath (A.policy z.1) z.2)) :=
  measurable_fst.prodMk (measurable_seeded_populationPath A.policy
    (fun xs => measurable_to_countable' (fun a => A.policy_measurable xs a)))

instance modelLaw_probability {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (s : Fin m → Bool) :
    IsProbabilityMeasure (modelLaw A d s) := by
  unfold modelLaw
  exact (Measure.isProbabilityMeasure_map_iff (measurable_observation A).aemeasurable).mpr inferInstance

/-- The fixed-sign model is mixed only for the testing argument. -/
def bayesLaw {m : ℕ} {R : Type} [MeasurableSpace R] (A : Estimator m R)
    (d : Fin m → Gap) (q : Fin m → unitInterval) : Measure (R × ProcessTape) :=
  ∑ s, (signLaw q) {s} • modelLaw A d s

theorem signLaw_total {m : ℕ} (q : Fin m → unitInterval) :
    ∑ s : Fin m → Bool, (signLaw q) {s} = 1 := by
  simpa only [Finset.coe_univ,measure_univ] using
    sum_measure_singleton (μ := signLaw q) (s := Finset.univ)

instance bayesLaw_probability {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (q : Fin m → unitInterval) :
    IsProbabilityMeasure (bayesLaw A d q) where
  measure_univ := by
    simp only [bayesLaw,Measure.finsetSum_apply,Measure.smul_apply,measure_univ,
      smul_eq_mul,mul_one]
    exact signLaw_total q

def expectedWork {m : ℕ} {R : Type} [MeasurableSpace R] (A : Estimator m R)
    (d : Fin m → Gap) (s : Fin m → Bool) : ℝ≥0∞ :=
  ∫⁻ z, totalProcessWork z.2 ∂modelLaw A d s

theorem bayes_work_le {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (q : Fin m → unitInterval) (B : ℝ)
    (hw : ∀ s, expectedWork A d s ≤ ENNReal.ofReal B) :
    (∫⁻ z, totalProcessWork z.2 ∂bayesLaw A d q) ≤ ENNReal.ofReal B := by
  rw [bayesLaw,lintegral_finsetSum_measure]
  simp_rw [lintegral_smul_measure]
  calc
    _ ≤ ∑ s, (signLaw q) {s} * ENNReal.ofReal B :=
      Finset.sum_le_sum (fun s _ => mul_le_mul' le_rfl (hw s))
    _ = _ := by rw [← Finset.sum_mul,signLaw_total,one_mul]

end ThresholdHC.ObservedState
