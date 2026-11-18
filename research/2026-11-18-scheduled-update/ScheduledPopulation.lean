import FixedHorizonRisk
import ScheduledBayes
import ScheduledCertificate

namespace PilotFeedback.Scheduled
noncomputable section
open MeasureTheory Ordered
open scoped ENNReal
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.SharpRMS ThresholdHC.SharpRMS.LargeBudget ThresholdHC.SharpRMS.Pilot

/-- The seed selects a plan. The estimator's output may use its seed and the whole tape. -/
def OneUpdate {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) : Prop :=
  ∀ r, ∃ P : Plan, A.policy r = policy P

theorem four_lower {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (hc : OneUpdate A) :
    ENNReal.ofReal ((186960371/1000000000 : ℝ)^2) ≤ fourRisk A := by
  apply FixedHorizon.lower_of_word_bound A (fun r => by
    obtain ⟨P,h⟩ := hc r
    exact ⟨label P,h⟩) _ (sq_nonneg _)
  intro r X
  obtain ⟨P,h⟩ := hc r
  rw [h]
  simpa only [←expect P _ (prob_mem _) _] using bayes_lower certified certificate_total P X

theorem rms_lower {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (hc : OneUpdate A) :
    ENNReal.ofReal (186960371/1000000000 : ℝ) ≤ maximalRMSRisk (Measure.dirac fifthGap) A := by
  let loss (q : SignLaw) := squaredRisk (experimentLaw (Measure.dirac fifthGap) A q)
    (populationOutput A) (signMean (Measure.dirac fifthGap) q.val)
  have h : fourRisk A ≤ ⨆ q, loss q := iSup_le fun i =>
    le_iSup loss (⟨fun _ => prob i,measurable_const,fun _ => prob_mem i⟩ : SignLaw)
  have root := ENNReal.rpow_le_rpow ((four_lower A hc).trans h) (by norm_num : (0:ℝ) ≤ 1/2)
  rwa [ofReal_square_rpow_half _ (by norm_num),ENNReal.iSup_rpow_of_pos (by norm_num) loss] at root

theorem rms_separation {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (hc : OneUpdate A) :
    maximalRMSRisk (Measure.dirac fifthGap) pilotEstimator <
      maximalRMSRisk (Measure.dirac fifthGap) A := by
  have upper : maximalRMSRisk (Measure.dirac fifthGap) pilotEstimator ≤ ENNReal.ofReal bound := by
    apply iSup_le
    intro q
    exact HardBudget.rms_from_square _ _ _ _ (by norm_num) (pilot_squared_risk q)
  exact upper.trans_lt (((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).2
    (by norm_num [bound] : bound < (186960371/1000000000 : ℝ))).trans_le (rms_lower A hc))

end
end PilotFeedback.Scheduled
