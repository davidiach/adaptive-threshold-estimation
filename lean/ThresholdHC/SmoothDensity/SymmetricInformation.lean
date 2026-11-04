import ThresholdHC.SmoothDensity.Information
import ThresholdHC.UnbiasedConverse.ExperimentInformation

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.SmoothDensity
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.UnbiasedConverse ThresholdHC.Proofs.Transcript

theorem hidden_reverse_pair_information {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (η : Gap → ℝ) (hηb : ∀ d, 0 ≤ η d ∧ η d ≤ 1 / 8)
    (qp qm : SignLaw) (hp : ∀ d, qp.val d = 1 / 2 + η d)
    (hm : ∀ d, qm.val d = 1 / 2 - η d)
    (B h : ℝ) (hh : 0 < h) (hgap : ∀ d : Gap, (d : ℝ) * η d ≤ h / 8)
    (hwork : expectedWork μ A qm ≤ ENNReal.ofReal B) :
    klDiv (experimentLaw μ A qm) (experimentLaw μ A qp) ≤
      ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2 * B) := by
  have hqp d : (3 / 8 : ℝ) ≤ qp.val d ∧ qp.val d ≤ 5 / 8 := by
    rw [hp]
    constructor <;> linarith [(hηb d).1,(hηb d).2]
  have hqm d : (3 / 8 : ℝ) ≤ qm.val d ∧ qm.val d ≤ 5 / 8 := by
    rw [hm]
    constructor <;> linarith [(hηb d).1,(hηb d).2]
  have hc : tiltCoefficient h (1 / 8) = (128 / 225 : ℝ) * h ^ 2 := by
    unfold tiltCoefficient
    ring
  have hstep (d : Gap) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
      klB (mixPredict (d : ℝ) (qm.val d) a b) (mixPredict (d : ℝ) (qp.val d) a b) ≤
        (128 / 225 : ℝ) * h ^ 2 := by
    rw [hm,hp,← hc]
    exact (local_tilt_information d.property.1 d.property.2 (hηb d).1 (hηb d).2
      hh (by norm_num) le_rfl (by simpa only [div_eq_mul_inv,one_mul] using hgap d) ha hb hab).2
  have hb := creation_information_bound (PopulationSeed R) (PopulationSeed R × ProcessTape)
    (populationSeedLaw μ A) (experimentLaw μ A qm) (experimentLaw μ A qp) Prod.fst Prod.snd
    (populationPolicy A) populationGap (populationPrior qm) (populationPrior qp)
    ((128 / 225 : ℝ) * h ^ 2) measurable_fst
    (fun n b => measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const)
    (measurable_populationPolicy A) measurable_populationGap
    (measurable_populationPrior qm) (measurable_populationPrior qp)
    (population_realization R μ A qm).2 (population_realization R μ A qp).2
    (fun u i => (u.2 i).property) (fun u i => hqm (u.2 i)) (fun u i => hqp (u.2 i))
    (fun u i => hstep (u.2 i)) (by positivity)
    (lt_of_le_of_lt hwork ENNReal.ofReal_lt_top)
  simp only [infiniteTranscriptLaw,Prod.mk.eta,Measure.map_id'] at hb
  calc
    _ ≤ _ := hb
    _ ≤ ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2) * ENNReal.ofReal B :=
      mul_le_mul le_rfl hwork bot_le bot_le
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

end ThresholdHC.SmoothDensity
