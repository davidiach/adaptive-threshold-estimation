import ThresholdHC.ContinuousObserved.UniformGaps

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier6

theorem uniformGaps_real_law :
    uniformGaps.map (fun d : Gap => (d : ℝ)) =
      (4 : ℝ≥0∞) • volume.restrict (Ioc (0 : ℝ) (1 / 4)) := by
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Iic,Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iic]
  have hi : Iic x ∩ Ioc (0 : ℝ) (1 / 4) = Ioc 0 (min x (1 / 4)) := by
    ext d
    simp only [mem_inter_iff,mem_Iic,mem_Ioc,le_min_iff]
    tauto
  rw [hi,Real.volume_Ioc]
  change uniformGaps {d : Gap | (d : ℝ) ≤ x} = 4 * ENNReal.ofReal (min x (1 / 4) - 0)
  rw [sub_zero]
  by_cases hx : 0 < x
  · have hc : uniformGaps {d : Gap | (d : ℝ) ≤ x} = ENNReal.ofReal (min 1 (4 * x)) := by
      rw [← uniformGaps_cdf hx]
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    rw [hc]
    have hm : min 1 (4 * x) = 4 * min x (1 / 4) := by
      by_cases ha : x ≤ 1 / 4
      · rw [min_eq_left ha,min_eq_right (by linarith : 4 * x ≤ 1)]
      · rw [min_eq_right (le_of_lt (lt_of_not_ge ha)),min_eq_left (by linarith : 1 ≤ 4 * x)]
        ring
    rw [hm,ENNReal.ofReal_mul (by norm_num)]
    norm_num
  · have hx' : x ≤ 0 := le_of_not_gt hx
    have he : {d : Gap | (d : ℝ) ≤ x} = ∅ := by
      ext d
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      exact not_le_of_gt (lt_of_le_of_lt hx' d.property.1)
    rw [he,measure_empty,ENNReal.ofReal_eq_zero.mpr ((min_le_left _ _).trans hx')]
    simp

end ThresholdHC.ContinuousObserved
