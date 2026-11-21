import ThresholdHC.PilotFeedback.Specification
import ThresholdHC.PilotFeedback.OrderedPopulation
import ThresholdHC.PilotFeedback.OrderedReduction
import ThresholdHC.PilotFeedback.ScheduledPopulation

/-! The pilot-feedback separations at the gap `1/5` with budget `25`: every
precommitted algorithm has worst RMS risk at least `0.18735887`, every
one-update algorithm at least `0.186960371`, and the adaptive witness stays
below `0.186752`. The precommitted bound is the square root of the four-point
Bayes bound of `Ordered.original_lower`. -/
noncomputable section
namespace ThresholdHC.PilotFeedback
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.SharpRMS ThresholdHC.SharpRMS.LargeBudget
open ThresholdHC.SharpRMS.Pilot
open scoped ENNReal

theorem precommitted_rms_lower : PrecommittedLowerStatement := by
  intro R _ A hc
  let loss (q : SignLaw) := squaredRisk (experimentLaw (Measure.dirac fifthGap) A q)
    (populationOutput A) (signMean (Measure.dirac fifthGap) q.val)
  have h : Ordered.fourRisk A ≤ ⨆ q, loss q := iSup_le fun i =>
    le_iSup loss (⟨fun _ => Ordered.prob i, measurable_const, fun _ => Ordered.prob_mem i⟩ : SignLaw)
  have root := ENNReal.rpow_le_rpow ((Ordered.original_lower A hc).trans h)
    (by norm_num : (0:ℝ) ≤ 1/2)
  rwa [ofReal_square_rpow_half _ (by norm_num), ENNReal.iSup_rpow_of_pos (by norm_num) loss] at root

theorem precommitted_rms_separation : PrecommittedSeparationStatement := by
  intro R _ A hc
  have upper : maximalRMSRisk (Measure.dirac fifthGap) pilotEstimator ≤ ENNReal.ofReal bound :=
    iSup_le fun q => HardBudget.rms_from_square _ _ _ _ (by norm_num) (pilot_squared_risk q)
  exact upper.trans_lt (((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).2
    (by norm_num [bound] : bound < (18735887/100000000 : ℝ))).trans_le (precommitted_rms_lower A hc))

theorem one_update_rms_lower : OneUpdateLowerStatement := by
  intro R _ A hc
  exact Scheduled.rms_lower A hc

theorem one_update_rms_separation : OneUpdateSeparationStatement := by
  intro R _ A hc
  exact Scheduled.rms_separation A hc

end ThresholdHC.PilotFeedback
