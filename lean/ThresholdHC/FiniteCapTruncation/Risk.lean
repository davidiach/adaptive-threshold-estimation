import ThresholdHC.FiniteCapTruncation.Full
import ThresholdHC.Genie.InfiniteComparison

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.FiniteCapTruncation
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram ThresholdHC.Genie

/-- The ordinary cap alone gives an explicit relative minimax certificate.
This does not assert the same rate for the genie lower program. -/
theorem ordinary_cap_minimax (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B)
    (N : ℕ) (hN : 0 < N) :
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
      programValue μ ρ B N ≤ ENNReal.ofReal (8*(1+Real.sqrt (B/((N:ℝ)+1)))) *
        rareMinimaxRisk μ ρ B := by
  have h := ordinary_cap_rate μ ρ hB.le N hN
  have hr := infinite_program_comparison μ ρ B hρ hρhalf hB
  refine ⟨hr.1.trans h.1, ?_⟩
  have hu := h.2.trans (mul_le_mul_right hr.2 (ENNReal.ofReal (1+Real.sqrt (B/((N:ℝ)+1)))))
  convert hu using 1
  rw [← mul_assoc, ← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1+Real.sqrt (B/((N:ℝ)+1)))]
  congr 2
  ring

theorem ordinary_linear_cap (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B)
    (N : ℕ) (hN : 0 < N) (hcap : B ≤ (N:ℝ)+1) :
    programValue μ ρ B N ≤ 16 * rareMinimaxRisk μ ρ B := by
  have h := (ordinary_cap_minimax μ hρ hρhalf hB N hN).2
  have hs : Real.sqrt (B/((N:ℝ)+1)) ≤ 1 := by
    apply (Real.sqrt_le_one).mpr
    exact (div_le_one (by positivity : 0 < (N:ℝ)+1)).mpr hcap
  apply h.trans
  apply mul_le_mul_left
  rw [← ENNReal.ofReal_ofNat 16]
  apply ENNReal.ofReal_le_ofReal
  linarith

end ThresholdHC.FiniteCapTruncation

