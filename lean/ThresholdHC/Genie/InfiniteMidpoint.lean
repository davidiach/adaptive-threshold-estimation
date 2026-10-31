import ThresholdHC.Genie.InfiniteDuality
import ThresholdHC.StoppingProgram.MidpointComparison

/-! The equal-third reference absorption applies simultaneously to all caps,
so the two-prior midpoint modulus retains the same factor-three comparison. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram

def infiniteMidpointSquared (μ : Measure Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  ⨆ (q : SignLaw) (r : SignLaw) (_ : RarePrior μ ρ q) (_ : RarePrior μ ρ r),
    infiniteDualRatio μ B (midpointFourPriors q r)

def infiniteMidpointValue (μ : Measure Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  infiniteMidpointSquared μ ρ B ^ (1/(2:ℝ))

theorem absorbedPriors_infiniteInformation_le (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) :
    infiniteInformationRatio μ (absorbedPriors Q) ≤ infiniteInformationRatio μ Q :=
  iSup_mono (fun N => absorbedPriors_informationRatio_le μ (N+1) Q)

theorem absorbedPriors_infiniteDualRatio (μ : Measure Gap) [IsProbabilityMeasure μ]
    (B : ℝ) (Q : FourPriors) :
    infiniteDualRatio μ B Q ≤ 9*infiniteDualRatio μ B (absorbedPriors Q) := by
  rw [infiniteDualRatio_eq_iInf,infiniteDualRatio_eq_iInf,
    ENNReal.mul_iInf (fun h => (by norm_num at h))]
  exact iInf_mono (fun N => absorbedPriors_dualRatio μ B (N+1) Q)

theorem infinite_midpoint_squared_comparison (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) : infiniteMidpointSquared μ ρ B ≤ infiniteDualValue μ ρ B ∧
      infiniteDualValue μ ρ B ≤ 9*infiniteMidpointSquared μ ρ B := by
  constructor
  · apply iSup_le
    intro q
    apply iSup_le
    intro r
    apply iSup_le
    intro hq
    apply iSup_le
    intro hr
    exact le_iSup_of_le (midpointFourPriors q r)
      (le_iSup_of_le (midpointFourPriors_admissible μ q r hq hr) le_rfl)
  · apply iSup_le
    intro Q
    apply iSup_le
    intro hQ
    have hA := absorbedPriors_admissible μ Q hQ
    have hd : infiniteDualRatio μ B (absorbedPriors Q) ≤ infiniteMidpointSquared μ ρ B :=
      le_iSup_of_le (absorbedLow Q) (le_iSup_of_le (absorbedHigh Q)
        (le_iSup_of_le hA.1 (le_iSup_of_le hA.2.1 le_rfl)))
    exact (absorbedPriors_infiniteDualRatio μ B Q).trans (mul_le_mul_right hd 9)

theorem infinite_midpoint_comparison (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) :
    infiniteMidpointValue μ ρ B ≤ infiniteProgramValue μ ρ B ∧
      infiniteProgramValue μ ρ B ≤ 3*infiniteMidpointValue μ ρ B := by
  have he : infiniteDualValue μ ρ B ^ (1/(2:ℝ)) = infiniteProgramValue μ ρ B := by
    rw [← (infinite_four_prior_duality μ hρ hρhalf hB).1,
      ← ENNReal.rpow_two,← ENNReal.rpow_mul]
    norm_num
  have hs := infinite_midpoint_squared_comparison μ ρ B
  constructor
  · rw [←he]
    exact ENNReal.rpow_le_rpow hs.1 (by norm_num)
  · rw [←he]
    have hh := ENNReal.rpow_le_rpow hs.2 (show (0:ℝ) ≤ 1/2 by norm_num)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hh
    have h9 : (9:ℝ≥0∞) ^ (1/(2:ℝ)) = 3 := by
      have hsq : (9:ℝ≥0∞) = (3:ℝ≥0∞)^(2:ℝ) := by rw [ENNReal.rpow_two]; norm_num
      rw [hsq,← ENNReal.rpow_mul]
      norm_num
    simpa only [h9,infiniteMidpointValue] using hh

end ThresholdHC.Genie
