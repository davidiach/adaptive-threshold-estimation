import ThresholdHC.StoppingProgram.CertificateRealization
import ThresholdHC.StoppingProgram.PrimalAttainment
import ThresholdHC.StoppingProgram.Specification

/-! The stopping program upper bounds the original unrestricted observable
minimax risk. The feasible certificate is realized, rather than assumed. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem minimax_le_certificate {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (C : Certificate N) (hC : Feasible μ ρ B C) (hN : 0 < N) :
    rareMinimaxRisk μ ρ B ≤ certificateSquared C^(1/(2:ℝ)) := by
  obtain ⟨R,m,A,hBudget,hRisk⟩ := certificate_realization μ ρ B C hC hN
  have hrare : rareRisk μ A ρ ≤ certificateSquared C^(1/(2:ℝ)) := by
    apply iSup_le
    intro q
    apply iSup_le
    intro hq
    exact ENNReal.rpow_le_rpow (hRisk q hq) (by norm_num)
  exact (sInf_le (show rareRisk μ A ρ ∈ {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    RareBudget μ A ρ B ∧ r = rareRisk μ A ρ} from ⟨R,m,A,hBudget,rfl⟩)).trans hrare

theorem minimax_le_program (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 ≤ B) (N : ℕ) (hN : 0 < N) :
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N := by
  obtain ⟨C,hC,hvalue⟩ := programSquared_attained N μ hρ hρhalf hB
  have h := minimax_le_certificate μ ρ B C hC hN
  rwa [hvalue] at h

theorem program_upper : ProgramUpperStatement := by
  intro μ _ ρ B N hρ hρquarter hB hN
  exact minimax_le_program μ hρ (by linarith) hB.le N hN

end ThresholdHC.StoppingProgram
