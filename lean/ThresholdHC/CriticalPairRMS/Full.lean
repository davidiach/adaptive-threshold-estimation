import ThresholdHC.CriticalPairRMS.Specification
import ThresholdHC.ConfidenceTransfer.CriticalRate
import ThresholdHC.RMSLocalization.CommonPair

/-! The critical common pair fed to the generic RMS transfer. -/
noncomputable section
namespace ThresholdHC.CriticalPairRMS
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open scoped ENNReal

theorem critical_pair_rms : CriticalPairRMSStatement := by
  obtain ⟨a, ha, hpair⟩ := ThresholdHC.ConfidenceTransfer.critical_common_pair_bound
  refine ⟨a, ha, ?_⟩
  intro ρ B hρ hρ4 hB R _ A hw
  have hL := ThresholdHC.CriticalEntropy.criticalLogFactor_pos ρ hρ (by linarith)
  exact ThresholdHC.RMSLocalization.rms_rate_of_common_pair
    ThresholdHC.ConfidenceTransfer.criticalPositiveLaw A
    (by positivity : 0 < ρ/32) (mul_pos ha (mul_pos hρ hL)) hB (hpair ρ hρ hρ4) hw

theorem critical_pair_minimax_rms : CriticalPairMinimaxRMSStatement := by
  obtain ⟨a, ha, h⟩ := critical_pair_rms
  refine ⟨a, ha, fun ρ B hρ hρ4 hB => ?_⟩
  apply le_sInf
  rintro t ⟨R, mR, A, hw, rfl⟩
  exact h ρ B hρ hρ4 hB R A hw

end ThresholdHC.CriticalPairRMS
