import ThresholdHC.Tier6.Full

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.Confidence
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6

/-- Information bound for any positive clipping scale, with the actual
expected flip count in the original adaptive experiment. -/
theorem hard_pair_information {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (B h : ℝ) (hh : 0 < h) (hbudget : UniformBudget μ A B) :
    let hv := hard_pair_validity h hh
    let qp : SignLaw := ⟨hardPlus h, hv.2.1, fun d => (hv.2.2.2 d).2.2.1⟩
    let qm : SignLaw := ⟨hardMinus h, hv.2.2.1, fun d => (hv.2.2.2 d).2.2.2⟩
    klDiv (experimentLaw μ A qp) (experimentLaw μ A qm) ≤
      ENNReal.ofReal ((128/225:ℝ)*h^2*B) := by
  intro hv qp qm
  let P := experimentLaw μ A qp
  let Q := experimentLaw μ A qm
  let η : PopulationSeed R → ℕ → ℝ := fun u i => hardEta h (u.2 i)
  have hP := (population_realization R μ A qp).2
  have hQ := (population_realization R μ A qm).2
  have hηm : MeasurableEnvironment η := by
    intro i
    exact (measurable_hardEta h).comp ((measurable_pi_apply i).comp measurable_snd)
  have hw : (∫⁻ z, totalProcessWork z.2 ∂P) ≤ ENNReal.ofReal B := hbudget qp
  have hwork : (∫⁻ z, totalProcessWork z.2 ∂P) < ∞ :=
    lt_of_le_of_lt hw ENNReal.ofReal_lt_top
  have hbound := creation_infinite_kl_bound (PopulationSeed R) (PopulationSeed R × ProcessTape)
    (populationSeedLaw μ A) P Q Prod.fst Prod.snd (populationPolicy A) populationGap η h
    measurable_fst (fun n b => measurableSet_eq_fun
      ((measurable_pi_apply n).comp measurable_snd) measurable_const)
    (measurable_populationPolicy A) measurable_populationGap hηm
    (by exact hP)
    (by exact hQ)
    hh (fun u i => (u.2 i).property)
    (fun u i => hardEta_bounds hh.le (u.2 i))
    (fun u i => gap_mul_hardEta_le (u.2 i)) hwork
  have hk : klDiv P Q ≤ ENNReal.ofReal ((128/225:ℝ)*h^2) *
      ∫⁻ z, totalProcessWork z.2 ∂P := by
    simpa only [infiniteTranscriptLaw, Prod.mk.eta, Measure.map_id'] using hbound
  apply hk.trans
  calc
    _ ≤ ENNReal.ofReal ((128/225:ℝ)*h^2) * ENNReal.ofReal B :=
      mul_le_mul le_rfl hw bot_le bot_le
    _ = ENNReal.ofReal ((128/225:ℝ)*h^2*B) :=
      (ENNReal.ofReal_mul (by positivity)).symm

end ThresholdHC.Confidence
