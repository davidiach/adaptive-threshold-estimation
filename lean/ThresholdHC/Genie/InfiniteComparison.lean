import ThresholdHC.Genie.Model
import ThresholdHC.StoppingProgram.TruncationComparison
import ThresholdHC.StoppingProgram.TruncationLimit
import ThresholdHC.StoppingProgram.ProgramUpper
import ThresholdHC.StoppingProgram.BernoulliFloor

/-! The infinite-cap primal value is within factor eight of the original
minimax risk, directly from finite-prefix truncation and realization. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram

theorem infinite_program_comparison (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) :
    rareMinimaxRisk μ ρ B ≤ infiniteProgramValue μ ρ B ∧
      infiniteProgramValue μ ρ B ≤ 8*rareMinimaxRisk μ ρ B := by
  constructor
  · apply le_iInf
    intro N
    exact minimax_le_program μ hρ hρhalf hB.le _ (by omega)
  · have hbound (N : ℕ) : infiniteProgramValue μ ρ B/8 ≤ rareMinimaxRisk μ ρ B+
        ENNReal.ofReal (ρ/2*Real.sqrt (B/(((N+1:ℕ):ℝ)+1))) := by
      apply (ENNReal.div_le_iff (by norm_num : (8:ℝ≥0∞) ≠ 0)
        (by norm_num : (8:ℝ≥0∞) ≠ ⊤)).mpr
      have h := (iInf_le (fun n : ℕ => programValue μ ρ B (n+1)) N).trans
        (program_le_minimax_truncation μ ρ B hρ hρhalf hB (N+1))
      simpa only [infiniteProgramValue,mul_comm] using h
    have he : Tendsto (fun N : ℕ => ENNReal.ofReal (ρ/2*Real.sqrt (B/(((N+1:ℕ):ℝ)+1))))
        atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).mpr (truncation_error_tendsto ρ B)
    have ht : Tendsto (fun N : ℕ => rareMinimaxRisk μ ρ B+
        ENNReal.ofReal (ρ/2*Real.sqrt (B/(((N+1:ℕ):ℝ)+1)))) atTop (𝓝 (rareMinimaxRisk μ ρ B)) := by
      simpa only [add_zero] using tendsto_const_nhds.add he
    have hh := ge_of_tendsto ht (Eventually.of_forall hbound)
    have h := (ENNReal.div_le_iff (by norm_num : (8:ℝ≥0∞) ≠ 0)
      (by norm_num : (8:ℝ≥0∞) ≠ ⊤)).mp hh
    simpa only [mul_comm] using h

theorem infinite_program_positive (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρquarter : ρ ≤ 1/4) (hB : 0 < B) :
    0 < infiniteProgramValue μ ρ B := by
  have hpos : 0 < ENNReal.ofReal ((1/16:ℝ)*min ρ (Real.sqrt (ρ/B))) := by positivity
  exact hpos.trans_le ((bernoulli_label_minimax_floor μ ρ B hρ hρquarter hB).trans
    (infinite_program_comparison μ ρ B hρ (by linarith) hB).1)

end ThresholdHC.Genie
