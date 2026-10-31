import ThresholdHC.StoppingProgram.MidpointInformation

/-! Symmetric contraction of endpoint priors preserves their midpoint and
scales the actual information/work ratio quadratically, including zero scale. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

def contractPrior (q r : SignLaw) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) : SignLaw :=
  mixPrior q (midpointPrior q r) s hs

theorem midpointPrior_comm (q r : SignLaw) : midpointPrior q r = midpointPrior r q := by
  apply Subtype.ext
  funext d
  dsimp only [midpointPrior,mixPrior]
  ring

theorem contractPrior_midpoint (q r : SignLaw) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) :
    midpointPrior (contractPrior q r s hs) (contractPrior r q s hs) = midpointPrior q r := by
  apply Subtype.ext
  funext d
  dsimp only [contractPrior,midpointPrior,mixPrior]
  ring

theorem contractPrior_rare (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ}
    (q r : SignLaw) (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r)
    (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) : RarePrior μ ρ (contractPrior q r s hs) :=
  mixPrior_rare μ q (midpointPrior q r) hq (mixPrior_rare μ q r hq hr (1/2) (by norm_num)) s hs

theorem contractPrior_gap (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) :
    signMean μ (contractPrior r q s hs).val-signMean μ (contractPrior q r s hs).val =
      s*(signMean μ r.val-signMean μ q.val) := by
  simp only [contractPrior,mixPrior_mean,midpointPrior_mean]
  ring

theorem contractPrior_contrast {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) (i : CountState N) :
    countCoefficient μ (contractPrior r q s hs) i-countCoefficient μ (contractPrior q r s hs) i =
      s*(countCoefficient μ r i-countCoefficient μ q i) := by
  simp only [contractPrior,mixPrior_countCoefficient,midpointPrior_countCoefficient]
  ring

theorem perspective_scale_contrast (x y s : ℝ) :
    perspective (s*x) y = ENNReal.ofReal (s^2)*perspective x y := by
  by_cases hy : 0 < y
  · rw [perspective_pos hy,perspective_pos hy,← ENNReal.ofReal_mul (sq_nonneg s)]
    congr 1
    ring
  · by_cases hs : s = 0
    · subst s
      simp [perspective,hy]
    · by_cases hx : x = 0
      · subst x
        simp [perspective,hy]
      · have hs2 : ENNReal.ofReal (s^2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_ne_zero hs)
        simp [perspective,hy,hx,mul_ne_zero hs hx,ENNReal.mul_top,hs2]

theorem contractPrior_information {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) (f : Flow N) :
    flowInformation μ (midpointFourPriors (contractPrior q r s hs) (contractPrior r q s hs)) f =
      ENNReal.ofReal (s^2)*flowInformation μ (midpointFourPriors q r) f := by
  unfold flowInformation
  simp only [midpointFourPriors,contractPrior_contrast,contractPrior_midpoint,perspective_scale_contrast]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ac_rfl

theorem contractPrior_informationRatio (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (q r : SignLaw) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) :
    informationRatio μ N (midpointFourPriors (contractPrior q r s hs) (contractPrior r q s hs)) =
      ENNReal.ofReal (s^2)*informationRatio μ N (midpointFourPriors q r) := by
  unfold informationRatio
  simp_rw [contractPrior_information]
  simp only [midpointFourPriors,contractPrior_midpoint]
  simp_rw [mul_div_assoc]
  rw [ENNReal.mul_iSup]
  congr 1
  funext f
  rw [ENNReal.mul_iSup]
  congr 1
  funext hf
  rw [ENNReal.mul_iSup]

end ThresholdHC.StoppingProgram
