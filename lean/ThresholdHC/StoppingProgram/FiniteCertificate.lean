import ThresholdHC.StoppingProgram.CertificateCap
import ThresholdHC.StoppingProgram.BernoulliFloor
import ThresholdHC.StoppingProgram.TruncationComparison
import ThresholdHC.StoppingProgram.ProgramUpper

/-! The unchanged factor-sixteen finite-certificate statement, for the original
observable minimax experiment and the prescribed explicit finite cap. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem finite_certificate : FiniteCertificateStatement := by
  intro μ _ ρ B hρ hρquarter hB
  have hhalf : ρ ≤ 1/2 := by linarith
  constructor
  · exact minimax_le_program μ hρ hhalf hB.le _ (certificateCap_pos ρ B hB)
  · have he : ENNReal.ofReal (ρ/2*Real.sqrt (B/((certificateCap ρ B:ℝ)+1))) ≤
        rareMinimaxRisk μ ρ B :=
      (ENNReal.ofReal_le_ofReal (certificateCap_error ρ B hρ hB)).trans
        (bernoulli_label_minimax_floor μ ρ B hρ hρquarter hB)
    calc
      _ ≤ 8*(rareMinimaxRisk μ ρ B+
          ENNReal.ofReal (ρ/2*Real.sqrt (B/((certificateCap ρ B:ℝ)+1)))) :=
        program_le_minimax_truncation μ ρ B hρ hhalf hB _
      _ ≤ 8*(rareMinimaxRisk μ ρ B+rareMinimaxRisk μ ρ B) :=
        mul_le_mul_right (add_le_add le_rfl he) 8
      _ = 16*rareMinimaxRisk μ ρ B := by
        rw [← two_mul,← mul_assoc]
        norm_num

end ThresholdHC.StoppingProgram
