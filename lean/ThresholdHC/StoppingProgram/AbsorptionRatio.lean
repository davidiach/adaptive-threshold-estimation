import ThresholdHC.StoppingProgram.AbsorbedPriors
import ThresholdHC.StoppingProgram.InformationBound

/-! Reference absorption decreases the extended information/work ratio,
including infinite ratios and singular reference states. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)

theorem absorbedPriors_information_le {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (f : Flow N) :
    flowInformation μ (absorbedPriors Q) f ≤ ENNReal.ofReal (1/3)*flowInformation μ Q f := by
  unfold flowInformation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    _ ≤ ENNReal.ofReal (f.stopWeight s)*(ENNReal.ofReal (1/3)*
        perspective (countCoefficient μ Q.high s-countCoefficient μ Q.low s)
          (countCoefficient μ Q.variance s)) := mul_le_mul_right (absorbedPriors_perspective_le μ Q s) _
    _ = _ := by ac_rfl

theorem absorbedPriors_mean_work_ge {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (f : Flow N) (hf : FlowCone f) :
    (1/3)*countMean μ Q.work f.continueWeight ≤ countMean μ (absorbedPriors Q).work f.continueWeight := by
  unfold countMean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (absorbedPriors_work_ge μ Q s) (hf.continue_nonneg s)

theorem absorbedPriors_informationRatio_le (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) : informationRatio μ N (absorbedPriors Q) ≤ informationRatio μ N Q := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  have hw := ENNReal.ofReal_le_ofReal (absorbedPriors_mean_work_ge μ Q f hf)
  rw [ENNReal.ofReal_mul (show (0:ℝ) ≤ 1/3 by norm_num)] at hw
  calc
    _ ≤ (ENNReal.ofReal (1/3)*flowInformation μ Q f)/
        (ENNReal.ofReal (1/3)*ENNReal.ofReal (countMean μ Q.work f.continueWeight)) :=
      ENNReal.div_le_div (absorbedPriors_information_le μ Q f) hw
    _ = flowInformation μ Q f/ENNReal.ofReal (countMean μ Q.work f.continueWeight) :=
      ENNReal.mul_div_mul_left _ _ (by norm_num) ENNReal.ofReal_ne_top
    _ ≤ informationRatio μ N Q := le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hi le_rfl))

theorem absorbedPriors_dualRatio (μ : Measure Gap) [IsProbabilityMeasure μ]
    (B : ℝ) (N : ℕ) (Q : FourPriors) :
    dualRatio μ B N Q ≤ 9*dualRatio μ B N (absorbedPriors Q) := by
  unfold dualRatio
  rw [absorbedPriors_gap,ENNReal.ofReal_mul (show (0:ℝ) ≤ 1/3 by norm_num),mul_pow]
  have hden : 4+ENNReal.ofReal B*informationRatio μ N (absorbedPriors Q) ≤
      4+ENNReal.ofReal B*informationRatio μ N Q :=
    add_le_add le_rfl (mul_le_mul_right (absorbedPriors_informationRatio_le μ N Q) _)
  calc
    _ ≤ (ENNReal.ofReal (ThresholdHC.Tier6.signMean μ Q.high.val-ThresholdHC.Tier6.signMean μ Q.low.val))^2/
        (4+ENNReal.ofReal B*informationRatio μ N (absorbedPriors Q)) := ENNReal.div_le_div_left hden _
    _ = _ := by
      rw [← mul_div_assoc,← mul_assoc]
      have hc : (9:ℝ≥0∞)*ENNReal.ofReal (1/3)^2 = 1 := by
        rw [← ENNReal.ofReal_pow (by norm_num),← ENNReal.ofReal_ofNat 9,
          ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      rw [hc,one_mul]

end ThresholdHC.StoppingProgram
