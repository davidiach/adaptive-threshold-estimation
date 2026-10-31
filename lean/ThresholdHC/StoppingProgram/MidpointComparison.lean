import ThresholdHC.StoppingProgram.AbsorptionRatio
import ThresholdHC.StoppingProgram.DualTheorem

/-! The two-prior midpoint modulus is within factor three of the actual
robust stopping-program value. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.RareAboveTwo

def midpointSquared (μ : Measure Gap) (ρ B : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨆ (q : SignLaw) (r : SignLaw) (_ : RarePrior μ ρ q) (_ : RarePrior μ ρ r),
    dualRatio μ B N (midpointFourPriors q r)

def midpointValue (μ : Measure Gap) (ρ B : ℝ) (N : ℕ) : ℝ≥0∞ :=
  midpointSquared μ ρ B N ^ (1/(2:ℝ))

theorem midpointSquared_le_dualValue (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (N : ℕ) : midpointSquared μ ρ B N ≤ dualValue μ ρ B N := by
  apply iSup_le
  intro q
  apply iSup_le
  intro r
  apply iSup_le
  intro hq
  apply iSup_le
  intro hr
  exact le_iSup_of_le (midpointFourPriors q r)
    (le_iSup_of_le (midpointFourPriors_admissible μ q r hq hr) le_rfl)

theorem dualValue_le_nine_midpointSquared (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (N : ℕ) : dualValue μ ρ B N ≤ 9*midpointSquared μ ρ B N := by
  apply iSup_le
  intro Q
  apply iSup_le
  intro hQ
  have hA := absorbedPriors_admissible μ Q hQ
  have hd : dualRatio μ B N (absorbedPriors Q) ≤ midpointSquared μ ρ B N :=
    le_iSup_of_le (absorbedLow Q) (le_iSup_of_le (absorbedHigh Q)
      (le_iSup_of_le hA.1 (le_iSup_of_le hA.2.1 le_rfl)))
  exact (absorbedPriors_dualRatio μ B N Q).trans (mul_le_mul_right hd 9)

theorem midpoint_comparison (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (N : ℕ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) :
    midpointValue μ ρ B N ≤ programValue μ ρ B N ∧
      programValue μ ρ B N ≤ 3*midpointValue μ ρ B N := by
  have he := (strong_four_prior_duality N μ hρ hρhalf hB).1
  change midpointSquared μ ρ B N ^ (1/(2:ℝ)) ≤ programSquared μ ρ B N ^ (1/(2:ℝ)) ∧ _
  rw [he]
  constructor
  · exact ENNReal.rpow_le_rpow (midpointSquared_le_dualValue μ ρ B N) (by norm_num)
  · unfold programValue midpointValue
    rw [he]
    have hh := ENNReal.rpow_le_rpow (dualValue_le_nine_midpointSquared μ ρ B N) (show (0:ℝ) ≤ 1/2 by norm_num)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hh
    have h9 : (9:ℝ≥0∞) ^ (1/(2:ℝ)) = 3 := by
      have hsq : (9:ℝ≥0∞) = (3:ℝ≥0∞)^(2:ℝ) := by rw [ENNReal.rpow_two]; norm_num
      rw [hsq,← ENNReal.rpow_mul]
      norm_num
    simpa only [h9] using hh

end ThresholdHC.StoppingProgram
