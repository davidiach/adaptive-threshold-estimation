import ThresholdHC.SelectionStability.Grid
import ThresholdHC.SelectionStability.MapCosts
import ThresholdHC.Tier6.HardPair

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.ObservedState
open ThresholdHC.Tier6 ThresholdHC.SelectionStability

def raiseGap (h d : Gap) : Gap := if d ≤ h then h else d

theorem measurable_raiseGap (h : Gap) : Measurable (raiseGap h) :=
  Measurable.ite measurableSet_Iic measurable_const measurable_id

theorem raiseGap_bounds (h d : Gap) : h ≤ raiseGap h d ∧ d ≤ raiseGap h d := by
  by_cases hd : d ≤ h
  · simp [raiseGap,hd]
  · simp [raiseGap,hd,le_of_not_ge hd]

theorem raiseGap_clipped (h d : Gap) :
    clippedGap h (raiseGap h d) = clippedGap h d := by
  by_cases hd : d ≤ h
  · simp only [raiseGap,ite_eq_left hd]
    rw [clippedGap,clippedGap,div_self h.property.1.ne',min_self]
    symm
    exact min_eq_left ((one_le_div d.property.1).mpr hd)
  · simp only [raiseGap,ite_eq_right hd]

/-- The existing finite grid supplies an upward rounding that loses at most
a factor two in the clipped modulus, including gaps below the cutoff. -/
theorem finite_upward_rounding (h : Gap) :
    ∃ T : Gap → Gap, Measurable T ∧ (Set.range T).Finite ∧
      (∀ d : Gap, d ≤ T d) ∧
      (∀ d : Gap, clippedGap h d ≤ 2 * clippedGap h (T d)) := by
  obtain ⟨T,hm,hb,_,hF⟩ := finite_rounding_grid h (by norm_num : (1 : ℝ) < 2)
  refine ⟨T ∘ raiseGap h,hm.comp (measurable_raiseGap h),?_,?_,?_⟩
  · apply hF.subset
    rintro _ ⟨d,rfl⟩
    exact mem_image_of_mem T (raiseGap_bounds h d).1
  · intro d
    exact (raiseGap_bounds h d).2.trans (hb (raiseGap h d)).1
  · intro d
    rw [← raiseGap_clipped h d]
    exact (rounding_kernels (by norm_num : (1 : ℝ) ≤ 2) h.property.1.le
      (hb (raiseGap h d)).1 (hb (raiseGap h d)).2).2.2.2

theorem rounded_cdf_le (μ : Measure Gap) (T : Gap → Gap) (hm : Measurable T)
    (hup : ∀ d, d ≤ T d) (x : ℝ) :
    (μ.map T) {d : Gap | (d : ℝ) ≤ x} ≤ μ {d : Gap | (d : ℝ) ≤ x} := by
  rw [Measure.map_apply hm (measurableSet_le measurable_subtype_coe measurable_const)]
  exact measure_mono (fun d hd => (show (d : ℝ) ≤ (T d : ℝ) from hup d).trans hd)

theorem rounded_modulus_lower (μ : Measure Gap) [IsProbabilityMeasure μ]
    (h : Gap) (T : Gap → Gap) (hm : Measurable T)
    (hb : ∀ d, clippedGap h d ≤ 2 * clippedGap h (T d)) :
    modulus μ h / 2 ≤ modulus (μ.map T) h := by
  have hi : Integrable (clippedGap h ∘ T) μ :=
    ((integrable_map_measure (measurable_clippedGap (h : ℝ)).aestronglyMeasurable hm.aemeasurable).mp
      (integrable_clippedGap (μ.map T) h.property.1.le))
  have hp := integral_mono (integrable_clippedGap μ h.property.1.le) (hi.const_mul 2) hb
  rw [integral_const_mul] at hp
  simp only [Function.comp_apply] at hp
  unfold modulus
  rw [integral_map hm.aemeasurable (measurable_clippedGap (h : ℝ)).aestronglyMeasurable]
  change (∫ d, clippedGap h d ∂μ) / 2 ≤ ∫ d, clippedGap h (T d) ∂μ
  linarith

end ThresholdHC.ObservedState
