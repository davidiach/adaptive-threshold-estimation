import ThresholdHC.SmoothDensity.Densities

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.SmoothDensity

theorem perturbation_reciprocal_lower (s : ℕ) {t x : ℝ}
    (ht : 0 < t) (hx : t ≤ x) :
    t ^ (s + 1) / (16 * x) ≤ perturbation s t x := by
  have hx0 : 0 < x := ht.trans_le hx
  rw [perturbation_rational s ht]
  apply (div_le_div_iff₀ (by positivity : 0 < 16 * x)
    (by positivity : 0 < 8 * (x ^ 2 + t ^ 2))).mpr
  have hsq : t ^ 2 ≤ x ^ 2 := sq_le_sq₀ ht.le hx0.le |>.mpr hx
  nlinarith [mul_nonneg (pow_nonneg ht.le (s + 1)) (sub_nonneg.mpr hsq)]

theorem log_scale_lower {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 64) :
    Real.log (1 / t) / 2 ≤ Real.log ((1 / 8) / t) := by
  have hlog : Real.log t ≤ Real.log (1 / 64 : ℝ) :=
    Real.log_le_log ht ht1
  have hc : Real.log (1 / 64 : ℝ) = 2 * Real.log (1 / 8 : ℝ) := by
    rw [show (1 / 64 : ℝ) = (1 / 8 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hc] at hlog
  rw [Real.log_div (by norm_num) (ne_of_gt ht), Real.log_one,
    Real.log_div (by norm_num) (ne_of_gt ht)]
  linarith

/-- The positive half of the perturbation has logarithmic mass. -/
theorem half_perturbation_lower (s : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 64) :
    t ^ (s + 1) / 32 * Real.log (1 / t) ≤
      ∫ x in Ioi (0 : ℝ), baseDensity x * perturbation s t x := by
  have hta : t ≤ (1 / 8 : ℝ) := by linarith
  have hi := perturbation_integrable s t
  have hsmall : IntervalIntegrable (fun x : ℝ => t ^ (s + 1) / 16 * (1 / x))
      volume t (1 / 8) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.mul
    exact continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt
      (ht.trans_le ((uIcc_of_le hta ▸ hx).1)))
  have hpoint : ∀ x ∈ Icc t (1 / 8), t ^ (s + 1) / 16 * (1 / x) ≤
      baseDensity x * perturbation s t x := by
    intro x hx
    have hx0 : 0 < x := ht.trans_le hx.1
    have hg : 1 ≤ baseDensity x := baseDensity_core (by
      rw [abs_of_pos hx0]
      exact hx.2)
    have hp := perturbation_nonneg s ht.le hx0.le
    have he := perturbation_reciprocal_lower s ht hx.1
    calc
      _ = t ^ (s + 1) / (16 * x) := by ring
      _ ≤ perturbation s t x := he
      _ ≤ baseDensity x * perturbation s t x := by nlinarith
  have hm := intervalIntegral.integral_mono_on hta hsmall
    (hi.intervalIntegrable) hpoint
  rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos ht (by norm_num)] at hm
  have hset : (∫ x in t..(1 / 8 : ℝ), baseDensity x * perturbation s t x) ≤
      ∫ x in Ioi (0 : ℝ), baseDensity x * perturbation s t x := by
    rw [intervalIntegral.integral_of_le hta]
    apply setIntegral_mono_set hi.integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (baseDensity_nonneg x) (perturbation_nonneg s ht.le hx.le)
    · exact ae_of_all _ (fun x hx => ht.trans hx.1)
  have hl := mul_le_mul_of_nonneg_left (log_scale_lower ht ht1)
    (by positivity : 0 ≤ t ^ (s + 1) / 16)
  nlinarith [hm.trans hset]

theorem centered_pair_separation (s : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 64) :
    t ^ (s + 1) / 8 * Real.log (1 / t) ≤
      (∫ x in Ioi (0 : ℝ), centeredDensity s t 2 x) -
        ∫ x in Ioi (0 : ℝ), centeredDensity s t (-2) x := by
  have hi := perturbation_integrable s t
  simp only [centeredDensity,
    integral_add baseDensity_integrable.integrableOn (hi.const_mul _).integrableOn,
    integral_const_mul]
  have h := half_perturbation_lower s ht ht1
  linarith

end ThresholdHC.SmoothDensity
