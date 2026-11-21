import ThresholdHC.ClippedOutput.Clip
import ThresholdHC.UpperScale.Full

/-! Clipping the output to `[0,1]` can only help, stated against the
specification, with two consequences: the minimax RMS risk over
`[0,1]`-valued estimators equals `minimaxRisk`, and the clipped blind family
`unitClip (UpperScale.scaledFamily B)` keeps the uniform budget `B` and has RMS
risk at most `min 1 (12*ω(B^{-1/2}))`. The simulated clipped constants of the
source are not stated. -/
noncomputable section
namespace ThresholdHC.ClippedOutput
open MeasureTheory ThresholdHC.Tier6
open scoped ENNReal

theorem unit_clip_monotone : UnitClipMonotoneStatement := by
  intro R _ A
  refine ⟨unitClip A, rfl, rfl, fun z => rfl, ?_⟩
  intro μ _
  exact ⟨fun q => unitClip_expectedWork μ A q, fun B => unitClip_uniformBudget μ A B,
    fun q => unitClip_rootMeanRisk_le μ A q, unitClip_maximalRMSRisk_le μ A⟩

theorem unit_output_minimax : UnitOutputMinimaxStatement := by
  intro μ _ B
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨R, mR, A, hb, rfl⟩
    exact sInf_le_of_le
      ⟨R, mR, unitClip A, (unitClip_uniformBudget μ A B).2 hb, unitClip_output_range A, rfl⟩
      ((unitClip_maximalRMSRisk_le μ A).trans (min_le_right _ _))
  · apply sInf_le_sInf
    rintro _ ⟨R, mR, A, hb, -, rfl⟩
    exact ⟨R, mR, A, hb, rfl⟩

theorem clipped_blind_upper_12 : ClippedBlindUpper12Statement := by
  refine ⟨BlindUpper.BatchSeed, inferInstance, fun B => unitClip (UpperScale.scaledFamily B),
    fun B z => unitClip_output_range _ z, ?_⟩
  intro B hB μ _
  exact ⟨(unitClip_uniformBudget μ _ B).2 (UpperScale.scaledFamily_uniformBudget B μ),
    (unitClip_maximalRMSRisk_le μ _).trans
      (min_le_min_left 1 (UpperScale.scaledFamily_maximalRMSRisk B hB μ))⟩

end ThresholdHC.ClippedOutput
