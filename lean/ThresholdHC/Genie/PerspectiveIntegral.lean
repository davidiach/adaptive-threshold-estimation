import ThresholdHC.StoppingProgram.Perspective

/-! The extended quadratic perspective is the supremum of affine quadratic
tests. This representation gives integral data processing even when the
reference density vanishes or the information is infinite. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.StoppingProgram

theorem quadratic_test_le_perspective (x y t : ℝ) (hy : 0 ≤ y) :
    ENNReal.ofReal (2*t*x-t^2*y) ≤ perspective x y := by
  by_cases hy0 : y = 0
  · subst y
    by_cases hx : x = 0
    · simp [hx,perspective]
    · simp [perspective,hx]
  · have hpos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    rw [perspective_pos hpos]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ hpos).mpr
    nlinarith [sq_nonneg (x-t*y)]

theorem perspective_eq_iSup_test (x y : ℝ) (hy : 0 ≤ y) :
    perspective x y = ⨆ t : ℝ, ENNReal.ofReal (2*t*x-t^2*y) := by
  apply le_antisymm
  · by_cases hy0 : y = 0
    · subst y
      by_cases hx : x = 0
      · simp [hx,perspective]
      · have he : (⨆ t : ℝ, ENNReal.ofReal (2*t*x-t^2*0)) = ⊤ := by
          apply iSup_eq_top.mpr
          intro b hb
          refine ⟨(b.toReal+1)/(2*x),?_⟩
          have hcalc : 2*((b.toReal+1)/(2*x))*x-((b.toReal+1)/(2*x))^2*0 = b.toReal+1 := by
            field_simp
            <;> ring
          rw [hcalc]
          calc
            b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb.ne).symm
            _ < ENNReal.ofReal (b.toReal+1) :=
              (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
        rw [he]
        exact le_top
    · have hpos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
      calc
        perspective x y = ENNReal.ofReal (2*(x/y)*x-(x/y)^2*y) := by
          rw [perspective_pos hpos]
          congr 1
          field_simp
          <;> ring
        _ ≤ _ := le_iSup (fun t : ℝ => ENNReal.ofReal (2*t*x-t^2*y)) (x/y)
  · exact iSup_le (fun t => quadratic_test_le_perspective x y t hy)

theorem measurable_perspective {X : Type*} [MeasurableSpace X] (f g : X → ℝ)
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => perspective (f x) (g x)) := by
  unfold perspective
  exact Measurable.ite (measurableSet_lt measurable_const hg)
    (ENNReal.measurable_ofReal.comp ((hf.pow_const 2).div hg))
    (Measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const measurable_const)

theorem ofReal_integral_le_lintegral_positive {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have hm : Integrable (fun x => max (f x) 0) μ := hf.sup (integrable_zero _ _ _)
  calc
    _ ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂μ) :=
      ENNReal.ofReal_le_ofReal (integral_mono hf hm (fun x => le_max_left _ _))
    _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hm (Filter.Eventually.of_forall (fun x => le_max_right _ _))
    _ = _ := by simp

theorem perspective_integral_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hg0 : ∀ x, 0 ≤ g x) :
    perspective (∫ x, f x ∂μ) (∫ x, g x ∂μ) ≤
      ∫⁻ x, perspective (f x) (g x) ∂μ := by
  rw [perspective_eq_iSup_test _ _ (integral_nonneg hg0)]
  apply iSup_le
  intro t
  have hi : Integrable (fun x => 2*t*f x-t^2*g x) μ :=
    (hf.const_mul (2*t)).sub (hg.const_mul (t^2))
  calc
    _ = ENNReal.ofReal (∫ x, 2*t*f x-t^2*g x ∂μ) := by
      rw [integral_sub (hf.const_mul _) (hg.const_mul _),integral_const_mul,integral_const_mul]
    _ ≤ ∫⁻ x, ENNReal.ofReal (2*t*f x-t^2*g x) ∂μ :=
      ofReal_integral_le_lintegral_positive μ _ hi
    _ ≤ _ := lintegral_mono (fun x => quadratic_test_le_perspective (f x) (g x) t (hg0 x))

end ThresholdHC.Genie
