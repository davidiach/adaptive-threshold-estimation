import ThresholdHC.ObservedState.Realization

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.ObservedState
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier6

/-- The finite-cell Bayes experiment is the concrete independent-tape
experiment, with actual work inherited from every deterministic sign array. -/
theorem bayes_information_bound {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (η : Fin m → ℝ)
    (qp qm : Fin m → unitInterval)
    (hp : ∀ i, (qp i : ℝ) = 1 / 2 + η i) (hm : ∀ i, (qm i : ℝ) = 1 / 2 - η i)
    {B h : ℝ} (hh : 0 < h) (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1 / 8)
    (hd : ∀ i, (d i : ℝ) * η i ≤ h / 8)
    (hw : ∀ s, expectedWork A d s ≤ ENNReal.ofReal B) :
    klDiv (bayesLaw A d qp) (bayesLaw A d qm) ≤
      ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2 * B) := by
  have hP := bayes_realizes A d qp
  have hQ := bayes_realizes A d qm
  simp_rw [hp] at hP
  simp_rw [hm] at hQ
  have hwork := bayes_work_le A d qp B hw
  have hb := infinite_kl_bound R (R × ProcessTape) A.randomLaw
    (bayesLaw A d qp) (bayesLaw A d qm) m Prod.fst Prod.snd A.policy
    (fun i => (d i : ℝ)) η h measurable_fst
    (fun n b => measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const)
    A.policy_measurable hP hQ hh (fun i => (d i).property) hη hd
    (lt_of_le_of_lt hwork ENNReal.ofReal_lt_top)
  simp only [infiniteTranscriptLaw,Prod.mk.eta,Measure.map_id'] at hb
  calc
    _ ≤ _ := hb
    _ ≤ ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2) * ENNReal.ofReal B :=
      mul_le_mul' le_rfl hwork
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

end ThresholdHC.ObservedState
