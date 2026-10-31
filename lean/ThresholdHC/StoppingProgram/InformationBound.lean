import ThresholdHC.StoppingProgram.FlowOperations

/-! Every cone flow is controlled by the unit-root information/work ratio,
including zero intensity and extended-valued null-reference perspectives. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)

theorem flowInformation_zero_of_intensity_zero {N : ℕ} (μ : Measure Gap) (Q : FourPriors)
    (f : Flow N) (hf : FlowCone f) (hi : intensity f = 0) : flowInformation μ Q f = 0 := by
  unfold flowInformation
  apply Finset.sum_eq_zero
  intro s _
  rw [(flow_zero_intensity f hf hi s).1,ENNReal.ofReal_zero,zero_mul]

theorem flowInformation_le_ratio_work {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (f : Flow N) (hf : FlowCone f) :
    flowInformation μ Q f ≤ informationRatio μ N Q*ENNReal.ofReal (countMean μ Q.work f.continueWeight) := by
  by_cases hi0 : intensity f = 0
  · rw [flowInformation_zero_of_intensity_zero μ Q f hf hi0]
    exact bot_le
  have hi : 0 < intensity f := lt_of_le_of_ne (hf.continue_nonneg (rootState N)) (Ne.symm hi0)
  let r := (intensity f)⁻¹
  have hr : 0 < r := inv_pos.mpr hi
  have hn := normalized_flow f hf hi
  have hratio : flowInformation μ Q (scaleFlow r f)/
      ENNReal.ofReal (countMean μ Q.work (scaleFlow r f).continueWeight) ≤ informationRatio μ N Q :=
    le_iSup_of_le (scaleFlow r f) (le_iSup_of_le hn.1 (le_iSup_of_le hn.2 le_rfl))
  rw [flowInformation_scale μ Q f hr.le] at hratio
  change ENNReal.ofReal r*flowInformation μ Q f /
    ENNReal.ofReal (countMean μ Q.work (fun s => r*f.continueWeight s)) ≤ _ at hratio
  rw [countMean_scale,ENNReal.ofReal_mul hr.le,
    ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top] at hratio
  have hw : 0 < countMean μ Q.work f.continueWeight := hi.trans_le (flow_work_ge_intensity μ Q.work f hf)
  exact (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hw) ENNReal.ofReal_ne_top).mp hratio

theorem flowInformation_le_ratio_budget {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (f : Flow N) (hf : FlowCone f) {B : ℝ}
    (hB : countMean μ Q.work f.continueWeight ≤ B) :
    flowInformation μ Q f ≤ informationRatio μ N Q*ENNReal.ofReal B :=
  (flowInformation_le_ratio_work μ Q f hf).trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal hB) _)

theorem flowInformation_finite_of_ratio_finite {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (f : Flow N) (hf : FlowCone f) (hK : informationRatio μ N Q ≠ ⊤) :
    flowInformation μ Q f ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top) (flowInformation_le_ratio_work μ Q f hf)

theorem flowInformation_toReal_le {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (f : Flow N) (hf : FlowCone f) (hK : informationRatio μ N Q ≠ ⊤)
    {B : ℝ} (hB : 0 ≤ B) (hw : countMean μ Q.work f.continueWeight ≤ B) :
    (flowInformation μ Q f).toReal ≤ (informationRatio μ N Q).toReal*B := by
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top)
    (flowInformation_le_ratio_budget μ Q f hf hw)
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hB] using hh

end ThresholdHC.StoppingProgram
