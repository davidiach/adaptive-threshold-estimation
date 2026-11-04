import ThresholdHC.OracleLower.Information
import ThresholdHC.Confidence.Lower

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.SmoothDensity
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.OracleLower ThresholdHC.Confidence

/-- A local sign pair. Only the plus experiment's expected work is charged. -/
theorem local_pair_information {R : Type} [MeasurableSpace R]
    (A : OracleEstimator R) (η : Gap → ℝ) (hη : Measurable η)
    (hηb : ∀ d, 0 ≤ η d ∧ η d ≤ 1 / 8)
    (qp qm : SignLaw) (hp : ∀ d, qp.val d = 1 / 2 + η d)
    (hm : ∀ d, qm.val d = 1 / 2 - η d)
    (B h : ℝ) (hh : 0 < h) (hgap : ∀ d : Gap, (d : ℝ) * η d ≤ h / 8)
    (hwork : (∫⁻ z, totalProcessWork z.2 ∂oracleLaw A qp) ≤ ENNReal.ofReal B) :
    klDiv (oracleLaw A qp) (oracleLaw A qm) ≤ ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2 * B) := by
  have hP := (oracle_realization R A qp).2
  have hQ := (oracle_realization R A qm).2
  simp_rw [hp] at hP
  simp_rw [hm] at hQ
  have hb := creation_infinite_kl_bound R (R × ProcessTape)
    A.randomLaw (oracleLaw A qp) (oracleLaw A qm) Prod.fst Prod.snd A.policy
    (fun u i => A.gap u i) (fun u i => η (A.gap u i)) h
    measurable_fst (fun n b => measurableSet_eq_fun
      ((measurable_pi_apply n).comp measurable_snd) measurable_const)
    A.policy_measurable (fun i => measurable_subtype_coe.comp (A.gap_measurable i))
    (fun i => hη.comp (A.gap_measurable i)) hP hQ hh
    (fun u i => (A.gap u i).property) (fun u i => hηb (A.gap u i))
    (fun u i => hgap (A.gap u i)) (lt_of_le_of_lt hwork ENNReal.ofReal_lt_top)
  have hb' : klDiv (oracleLaw A qp) (oracleLaw A qm) ≤
      ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2) *
        ∫⁻ z, totalProcessWork z.2 ∂oracleLaw A qp := by
    simpa only [infiniteTranscriptLaw, Prod.mk.eta, Measure.map_id'] using hb
  calc
    _ ≤ _ := hb'
    _ ≤ ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2) * ENNReal.ofReal B :=
      mul_le_mul le_rfl hwork bot_le bot_le
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-- The original hidden-gap estimator inherits the local-pair bound, with
no requirement on its work outside the two selected smooth models. -/
theorem hidden_local_pair_information {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (η : Gap → ℝ) (hη : Measurable η) (hηb : ∀ d, 0 ≤ η d ∧ η d ≤ 1 / 8)
    (qp qm : SignLaw) (hp : ∀ d, qp.val d = 1 / 2 + η d)
    (hm : ∀ d, qm.val d = 1 / 2 - η d)
    (B h : ℝ) (hh : 0 < h) (hgap : ∀ d : Gap, (d : ℝ) * η d ≤ h / 8)
    (hwork : expectedWork μ A qp ≤ ENNReal.ofReal B) :
    klDiv (experimentLaw μ A qp) (experimentLaw μ A qm) ≤
      ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2 * B) :=
  local_pair_information (hiddenOracle μ A) η hη hηb qp qm hp hm B h hh hgap hwork

theorem local_pair_confidence_cost {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (η : Gap → ℝ) (hη : Measurable η) (hηb : ∀ d, 0 ≤ η d ∧ η d ≤ 1 / 8)
    (qp qm : SignLaw) (hp : ∀ d, qp.val d = 1 / 2 + η d)
    (hm : ∀ d, qm.val d = 1 / 2 - η d)
    (B h ε δ : ℝ) (hh : 0 < h) (hgap : ∀ d : Gap, (d : ℝ) * η d ≤ h / 8)
    (hwork : expectedWork μ A qp ≤ ENNReal.ofReal B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hsep : 2 * ε < signMean μ qp.val - signMean μ qm.val)
    (hcPlus : failureProbability μ A qp ε ≤ ENNReal.ofReal δ)
    (hcMinus : failureProbability μ A qm ε ≤ ENNReal.ofReal δ) :
    Real.log (1 / δ) / 4 ≤ (128 / 225 : ℝ) * h ^ 2 * B := by
  have htest := confidence_testing_bound (experimentLaw μ A qp) (experimentLaw μ A qm)
    (populationOutput A) (measurable_populationOutput A)
    (signMean μ qp.val) (signMean μ qm.val) ε δ hδ hδ1 hsep hcPlus hcMinus
  have hkl := hidden_local_pair_information μ A η hη hηb qp qm hp hm B h hh hgap hwork
  have hl := confidence_log_pos hδ hδ1
  have hpos : 0 < ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2 * B) :=
    (ENNReal.ofReal_pos.mpr (by positivity : 0 < Real.log (1 / δ) / 4)).trans_le
      (htest.trans hkl)
  exact (ENNReal.ofReal_le_ofReal_iff (ENNReal.ofReal_pos.mp hpos).le).mp
    (htest.trans hkl)

end ThresholdHC.SmoothDensity
