import ThresholdHC.StoppingProgram.PrefixModulus
import ThresholdHC.StoppingProgram.TruncationRisk

/-! Truncation comparison with the original unrestricted minimax risk. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem program_le_risk_truncation {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B)
    (hbudget : RareBudget μ A ρ B) (N : ℕ) :
    programValue μ ρ B N ≤ 8*(rareRisk μ A ρ+
      ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1)))) := by
  apply prefix_program_bound μ A ρ B hρ hρhalf hB hbudget N
    (prefixTruncation A ρ N) (measurable_prefixTruncation A ρ N)
  intro q hq
  have hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ ρ :=
    ⟨integral_nonneg (fun d => (q.property.2 d).1),hq⟩
  exact (prefixTruncation_rmsRisk μ A q ρ (signMean μ q.val) B hρ.le hθ hB.le N
    (hbudget q hq)).trans (add_le_add
      (le_iSup_of_le q (le_iSup_of_le hq le_rfl)) le_rfl)

theorem program_le_minimax_truncation (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) (N : ℕ) :
    programValue μ ρ B N ≤ 8*(rareMinimaxRisk μ ρ B+
      ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1)))) := by
  let e := ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1)))
  have h : programValue μ ρ B N/8-e ≤ rareMinimaxRisk μ ρ B := by
    apply le_sInf
    rintro t ⟨R,mR,A,hbudget,rfl⟩
    letI := mR
    apply tsub_le_iff_right.mpr
    apply (ENNReal.div_le_iff (by norm_num : (8:ℝ≥0∞) ≠ 0) (by norm_num : (8:ℝ≥0∞) ≠ ⊤)).mpr
    simpa only [mul_comm] using program_le_risk_truncation μ A ρ B hρ hρhalf hB hbudget N
  have hh := tsub_le_iff_right.mp h
  have hhh := (ENNReal.div_le_iff (by norm_num : (8:ℝ≥0∞) ≠ 0)
    (by norm_num : (8:ℝ≥0∞) ≠ ⊤)).mp hh
  simpa only [mul_comm] using hhh

end ThresholdHC.StoppingProgram
