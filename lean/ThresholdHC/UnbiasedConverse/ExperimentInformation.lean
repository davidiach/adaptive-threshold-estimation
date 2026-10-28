import ThresholdHC.UnbiasedConverse.Tilt

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.UnbiasedConverse
open ThresholdHC ThresholdHC.Proofs.Transcript
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6

theorem tilt_experiment_information {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {W h e : ℝ} (hh : 0 < h) (he : 0 ≤ e) (he1 : e ≤ 1/8)
    (hbudget : UniformBudget μ A W) :
    klDiv (experimentLaw μ A (tiltPlus h e hh he he1))
      (experimentLaw μ A (tiltMinus h e hh he he1)) ≤ ENNReal.ofReal (tiltCoefficient h e * W) ∧
    klDiv (experimentLaw μ A (tiltMinus h e hh he he1))
      (experimentLaw μ A (tiltPlus h e hh he he1)) ≤ ENNReal.ofReal (tiltCoefficient h e * W) := by
  have hc : 0 ≤ tiltCoefficient h e := by unfold tiltCoefficient; positivity
  have bound (q v : SignLaw)
      (hq : ∀ d, (3/8:ℝ) ≤ q.val d ∧ q.val d ≤ 5/8)
      (hv : ∀ d, (3/8:ℝ) ≤ v.val d ∧ v.val d ≤ 5/8)
      (hstep : ∀ (d : Gap) (A B : ℝ), 0 ≤ A → 0 ≤ B → 0 < A+B →
        klB (mixPredict (d:ℝ) (q.val d) A B) (mixPredict (d:ℝ) (v.val d) A B) ≤
          tiltCoefficient h e) :
      klDiv (experimentLaw μ A q) (experimentLaw μ A v) ≤
        ENNReal.ofReal (tiltCoefficient h e*W) := by
    have hw := hbudget q
    have ht n b : MeasurableSet {z : PopulationSeed R × ProcessTape | z.2 n = b} :=
      measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const
    have hb := creation_information_bound (PopulationSeed R) (PopulationSeed R × ProcessTape)
      (populationSeedLaw μ A) (experimentLaw μ A q) (experimentLaw μ A v) Prod.fst Prod.snd
      (populationPolicy A) populationGap (populationPrior q) (populationPrior v)
      (tiltCoefficient h e) measurable_fst ht (measurable_populationPolicy A)
      measurable_populationGap (measurable_populationPrior q) (measurable_populationPrior v)
      (population_realization R μ A q).2 (population_realization R μ A v).2
      (fun u i => (u.2 i).property) (fun u i => hq (u.2 i)) (fun u i => hv (u.2 i))
      (fun u i => hstep (u.2 i)) hc (lt_of_le_of_lt hw ENNReal.ofReal_lt_top)
    simp only [infiniteTranscriptLaw, Prod.mk.eta, Measure.map_id'] at hb
    apply hb.trans
    calc
      _ ≤ ENNReal.ofReal (tiltCoefficient h e) * ENNReal.ofReal W :=
        mul_le_mul le_rfl hw bot_le bot_le
      _ = _ := (ENNReal.ofReal_mul hc).symm
  have hp d : (3/8:ℝ) ≤ (tiltPlus h e hh he he1).val d ∧
      (tiltPlus h e hh he he1).val d ≤ 5/8 := by
    have hb := tiltEta_bounds hh he d
    dsimp [tiltPlus]; constructor <;> linarith [hb.1,hb.2.1]
  have hm d : (3/8:ℝ) ≤ (tiltMinus h e hh he he1).val d ∧
      (tiltMinus h e hh he he1).val d ≤ 5/8 := by
    have hb := tiltEta_bounds hh he d
    dsimp [tiltMinus]; constructor <;> linarith [hb.1,hb.2.1]
  have hlocal d A B (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A+B) :=
    local_tilt_information d.property.1 d.property.2 (tiltEta_bounds hh he d).1
      (tiltEta_bounds hh he d).2.1 hh he he1 (tiltEta_bounds hh he d).2.2 hA hB hAB
  exact ⟨bound _ _ hp hm (fun d A B hA hB hAB => (hlocal d A B hA hB hAB).1),
    bound _ _ hm hp (fun d A B hA hB hAB => (hlocal d A B hA hB hAB).2)⟩

end ThresholdHC.UnbiasedConverse
