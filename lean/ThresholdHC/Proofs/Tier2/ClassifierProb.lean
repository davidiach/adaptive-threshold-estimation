import ThresholdHC.Proofs.Tier2.ClassifierExpectations
import ThresholdHC.Proofs.Tier2.ClassifierMoments
import ThresholdHC.Proofs.Tier2.ClassifierTelescoping

noncomputable section
namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory Tier2 Uniform713

theorem lemma6_error : ThresholdHC.Targets.lemma6_error := by
  intro L d S hd hdmax
  rw [errProbK_eq_measure L d S hd hdmax]
  apply le_min measureReal_le_one
  have htail := tape_mean_tails (coinParameter d S hd hdmax)
  have hb : (tapeMeasure (coinParameter d S hd hdmax)).real
      {ω | Model.decision (fun j => dyadicMean observations j ω) L ≠ bit S} ≤
        Model.errorPrefactor / (cap L*d^2)^2 := by
    cases S
    · simpa [coinP, bit] using
        Model.error_negative_bound L hd (by simpa [coinP, sub_eq_add_neg] using htail)
    · simpa [coinP, bit] using
        Model.error_positive_bound L hd (by simpa [coinP, sub_eq_add_neg] using htail)
  calc
    _ ≤ Model.errorPrefactor / (cap L*d^2)^2 := hb
    _ ≤ 1 / (cap L*d^2)^2 := div_le_div_of_nonneg_right
      (Model.errorPrefactor_le.trans (by norm_num)) (sq_nonneg _)
    _ = _ := by simp only [cap, one_div, inv_pow]

theorem lemma6_work : ThresholdHC.Targets.lemma6_work := by
  intro L d S hd hdmax
  rw [workK_eq_integral L d S hd hdmax]
  have htail := tape_mean_tails (coinParameter d S hd hdmax)
  cases S
  · simpa [mN, workEnvelope, cap] using
      Model.expected_work_negative_bound L hd hdmax (by simpa [coinP, sub_eq_add_neg] using htail)
  · simpa [mN, workEnvelope, cap] using
      Model.expected_work_positive_bound L hd hdmax (by simpa [coinP, sub_eq_add_neg] using htail)

theorem lemma7_second_moment : ThresholdHC.Targets.lemma7_second_moment := by
  intro L d S hd hdmax
  unfold secondMomentK
  apply finite_secondMoment_bound L d hd hdmax
  intro l hl
  rw [← coinParameter_val d S hd hdmax,
    deltaK_secondMoment_eq_integral L l hl (coinParameter d S hd hdmax)]
  have htail := tape_mean_tails (coinParameter d S hd hdmax)
  cases S
  · exact Model.increment_secondMoment_negative l hd hdmax (by simpa [coinP, sub_eq_add_neg] using htail)
  · exact Model.increment_secondMoment_positive l hd hdmax (by simpa [coinP, sub_eq_add_neg] using htail)

theorem lemma7_work : ThresholdHC.Targets.lemma7_work := by
  intro L d S hd hdmax
  unfold workMomentK
  apply finite_workMoment_bound L d hd hdmax
  intro l hl
  rw [← coinParameter_val d S hd hdmax,
    levelWork_eq_integral L l hl (coinParameter d S hd hdmax)]
  have htail := tape_mean_tails (coinParameter d S hd hdmax)
  cases S
  · exact Model.expected_work_negative_bound l hd hdmax (by simpa [coinP, sub_eq_add_neg] using htail)
  · exact Model.expected_work_positive_bound l hd hdmax (by simpa [coinP, sub_eq_add_neg] using htail)

end ThresholdHC.Proofs
