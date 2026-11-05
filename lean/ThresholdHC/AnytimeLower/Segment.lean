import ThresholdHC.ConfidenceProgram.Midpoint

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram

/-- The middle half of a prior segment dominates half its original midpoint. -/
theorem segment_midpoint_coefficient {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hm : 1/2 ≤ a+b ∧ a+b ≤ 3/2) (i : CountState N) :
    (1/2)*countCoefficient μ (midpointPrior q r) i ≤
      countCoefficient μ (midpointPrior (mixPrior q r a ha) (mixPrior q r b hb)) i := by
  simp only [midpointPrior_countCoefficient,mixPrior_countCoefficient]
  have hq := countCoefficient_nonneg μ q i
  have hr := countCoefficient_nonneg μ r i
  nlinarith only [mul_nonneg (by linarith : 0 ≤ a+b-1/2) hq,
    mul_nonneg (by linarith : 0 ≤ 3/2-a-b) hr]

theorem segment_contrast {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (i : CountState N) :
    countCoefficient μ (mixPrior q r b hb) i-countCoefficient μ (mixPrior q r a ha) i =
      (a-b)*(countCoefficient μ r i-countCoefficient μ q i) := by
  simp only [mixPrior_countCoefficient]
  ring

theorem segment_information {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hm : 1/2 ≤ a+b ∧ a+b ≤ 3/2) (f : Flow N) :
    flowInformation μ (midpointFourPriors (mixPrior q r a ha) (mixPrior q r b hb)) f ≤
      ENNReal.ofReal (2*(a-b)^2)*flowInformation μ (midpointFourPriors q r) f := by
  unfold flowInformation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hden := segment_midpoint_coefficient μ q r a b ha hb hm i
  have hp := perspective_antitone_reference
    (countCoefficient μ (mixPrior q r b hb) i-countCoefficient μ (mixPrior q r a ha) i)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) (countCoefficient_nonneg μ (midpointPrior q r) i)) hden
  rw [segment_contrast] at hp
  have he : perspective ((a-b)*(countCoefficient μ r i-countCoefficient μ q i))
      ((1/2)*countCoefficient μ (midpointPrior q r) i) =
      ENNReal.ofReal (2*(a-b)^2)*perspective (countCoefficient μ r i-countCoefficient μ q i)
        (countCoefficient μ (midpointPrior q r) i) := by
    rw [show (a-b)*(countCoefficient μ r i-countCoefficient μ q i) =
      (1/2)*((2*(a-b))*(countCoefficient μ r i-countCoefficient μ q i)) by ring,
      perspective_scale _ _ (by norm_num : (0:ℝ) ≤ 1/2),perspective_scale_contrast,
      ← mul_assoc,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    congr 2
    ring
  rw [he] at hp
  dsimp only [midpointFourPriors]
  rw [segment_contrast]
  calc
    _ ≤ ENNReal.ofReal (f.stopWeight i)*(ENNReal.ofReal (2*(a-b)^2)*
        perspective (countCoefficient μ r i-countCoefficient μ q i)
          (countCoefficient μ (midpointPrior q r) i)) := mul_le_mul_right hp _
    _ = _ := by ac_rfl

theorem segment_work {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hm : 1/2 ≤ a+b ∧ a+b ≤ 3/2) (f : Flow N) (hf : FlowCone f) :
    (1/2)*countMean μ (midpointPrior q r) f.continueWeight ≤
      countMean μ (midpointPrior (mixPrior q r a ha) (mixPrior q r b hb)) f.continueWeight := by
  unfold countMean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (segment_midpoint_coefficient μ q r a b ha hb hm i) (hf.continue_nonneg i)

/-- Information per unit of work is quadratic along every central prior segment.
The inequality also covers identical priors, zero scale and infinite information. -/
theorem segment_informationRatio (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (q r : SignLaw) (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hm : 1/2 ≤ a+b ∧ a+b ≤ 3/2) :
    informationRatio μ N (midpointFourPriors (mixPrior q r a ha) (mixPrior q r b hb)) ≤
      ENNReal.ofReal (4*(a-b)^2)*informationRatio μ N (midpointFourPriors q r) := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  have hw := ENNReal.ofReal_le_ofReal (segment_work μ q r a b ha hb hm f hf)
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)] at hw
  calc
    _ ≤ (ENNReal.ofReal (2*(a-b)^2)*flowInformation μ (midpointFourPriors q r) f)/
        (ENNReal.ofReal (1/2)*ENNReal.ofReal (countMean μ (midpointPrior q r) f.continueWeight)) :=
      ENNReal.div_le_div (segment_information μ q r a b ha hb hm f) hw
    _ = ENNReal.ofReal (4*(a-b)^2)*
        (flowInformation μ (midpointFourPriors q r) f/
          ENNReal.ofReal (countMean μ (midpointPrior q r) f.continueWeight)) := by
      rw [show ENNReal.ofReal (2*(a-b)^2) =
        ENNReal.ofReal (1/2)*ENNReal.ofReal (4*(a-b)^2) by
          rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
          congr 1
          ring, mul_assoc, ENNReal.mul_div_mul_left _ _ (by norm_num) ENNReal.ofReal_ne_top,
        mul_div_assoc]
    _ ≤ _ := by
      have hbound : flowInformation μ (midpointFourPriors q r) f /
          ENNReal.ofReal (countMean μ (midpointFourPriors q r).work f.continueWeight) ≤
          informationRatio μ N (midpointFourPriors q r) :=
        le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hi le_rfl))
      exact mul_le_mul_right hbound _

end ThresholdHC.AnytimeLower
