import ThresholdHC.EntropyTailAssembly.OrdinaryKernels

/-! Ordinary kernels controlled by the selected inverse-square moment and
the resolved tail's inverse moment. These are component estimates; they
impose no inverse-moment assumption on the original population. -/

noncomputable section
open MeasureTheory Set Real

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6 ThresholdHC.EntropyTailUpper

theorem min_one_sq_le {x : ℝ} (hx : 0 ≤ x) : min 1 (x^2) ≤ x := by
  by_cases h : x ≤ 1
  · exact (min_le_right _ _).trans (by nlinarith)
  · exact (min_le_left _ _).trans (le_of_not_ge h)

theorem ordinaryErrorKernel_le_inverseSquare {M : ℝ} (hM : 0 < M) (d : Gap) :
    ordinaryErrorKernel M (d:ℝ) ≤ M⁻¹ * (d:ℝ)⁻¹^2 := by
  have h := min_one_sq_le (x := (M*(d:ℝ)^2)⁻¹) (by positivity [d.property.1])
  simpa only [ordinaryErrorKernel, mul_inv_rev, inv_pow, mul_comm] using h

theorem ordinaryErrorKernel_le_inverse {M : ℝ} (hM : 0 < M) (d : Gap) :
    ordinaryErrorKernel M (d:ℝ) ≤ (sqrt M)⁻¹ * (d:ℝ)⁻¹ := by
  have hs : 0 < sqrt M := sqrt_pos_of_pos hM
  have he : M⁻¹ * (d:ℝ)⁻¹^2 = ((sqrt M)⁻¹ * (d:ℝ)⁻¹)^2 := by
    simp only [mul_pow, inv_pow, sq_sqrt hM.le]
  calc
    _ ≤ min 1 (M⁻¹ * (d:ℝ)⁻¹^2) :=
      le_min (min_le_left _ _) (ordinaryErrorKernel_le_inverseSquare hM d)
    _ = min 1 (((sqrt M)⁻¹ * (d:ℝ)⁻¹)^2) := by rw [he]
    _ ≤ _ := min_one_sq_le (by positivity [d.property.1])

theorem eta_le_inverseSquare (ξ : Measure Gap) [IsFiniteMeasure ξ]
    (hI : Integrable (fun d : Gap => (d:ℝ)⁻¹^2) ξ) {M : ℝ} (hM : 0 < M) :
    eta ξ M ≤ (∫ d : Gap, (d:ℝ)⁻¹^2 ∂ξ) / M := by
  have h := integral_mono (integrable_ordinaryErrorKernel ξ M) (hI.const_mul M⁻¹)
    (ordinaryErrorKernel_le_inverseSquare hM)
  rw [integral_const_mul] at h
  simpa only [eta, div_eq_mul_inv, mul_comm] using h

theorem eta_le_inverse (ξ : Measure Gap) [IsFiniteMeasure ξ]
    (hI : Integrable (fun d : Gap => (d:ℝ)⁻¹) ξ) {M : ℝ} (hM : 0 < M) :
    eta ξ M ≤ (∫ d : Gap, (d:ℝ)⁻¹ ∂ξ) / sqrt M := by
  have h := integral_mono (integrable_ordinaryErrorKernel ξ M) (hI.const_mul (sqrt M)⁻¹)
    (ordinaryErrorKernel_le_inverse hM)
  rw [integral_const_mul] at h
  simpa only [eta, div_eq_mul_inv, mul_comm] using h

theorem ordinaryWorkKernel_le_inverse {M : ℝ} (hM : 0 < M) (d : Gap) :
    ordinaryWorkKernel M (d:ℝ) ≤ 34 * sqrt M * (d:ℝ)⁻¹ := by
  have hd := d.property.1
  have hs : 0 < sqrt M := sqrt_pos_of_pos hM
  have hx : 0 < sqrt M * (d:ℝ) := mul_pos hs hd
  have hm : M*(d:ℝ)^2 = (sqrt M*(d:ℝ))^2 := by
    rw [mul_pow, sq_sqrt hM.le]
  by_cases h : sqrt M*(d:ℝ) ≤ 1
  · have hb : M ≤ sqrt M * (d:ℝ)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hd]
      nlinarith [mul_le_mul_of_nonneg_left h hs.le, sq_sqrt hM.le]
    exact (min_le_left _ _).trans (hb.trans (by nlinarith [inv_pos.mpr hd]))
  · have hx1 : 1 ≤ sqrt M*(d:ℝ) := le_of_not_ge h
    have hl0 : 0 ≤ log (M*(d:ℝ)^2) := by
      apply log_nonneg
      rw [hm]
      nlinarith
    have hl : 1 + max 0 (log (M*(d:ℝ)^2)) ≤ 2*(sqrt M*(d:ℝ)) := by
      rw [max_eq_right hl0, hm, log_pow]
      norm_num
      linarith [log_le_sub_one_of_pos hx]
    calc
      _ ≤ 17*(d:ℝ)⁻¹^2*(1+max 0 (log (M*(d:ℝ)^2))) := min_le_right _ _
      _ ≤ 17*(d:ℝ)⁻¹^2*(2*(sqrt M*(d:ℝ))) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ = _ := by field_simp; ring

theorem ordinaryCost_le_inverse (ξ : Measure Gap) [IsFiniteMeasure ξ]
    (hI : Integrable (fun d : Gap => (d:ℝ)⁻¹) ξ) {M : ℝ} (hM : 0 < M) :
    ordinaryCost ξ M ≤ 34 * sqrt M * (∫ d : Gap, (d:ℝ)⁻¹ ∂ξ) := by
  have h := integral_mono (integrable_ordinaryWorkKernel ξ hM.le)
    (hI.const_mul (34*sqrt M)) (ordinaryWorkKernel_le_inverse hM)
  rw [integral_const_mul] at h
  exact h

end ThresholdHC.EntropyTailAssembly
