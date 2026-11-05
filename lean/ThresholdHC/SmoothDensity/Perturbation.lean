import ThresholdHC.SmoothDensity.Rational

noncomputable section
open scoped ContDiff
namespace ThresholdHC.SmoothDensity

/-- The amplitude is chosen so that derivatives through order `s` stay bounded. -/
def perturbation (s : ℕ) (t x : ℝ) : ℝ :=
  t ^ s / 8 * profile (t⁻¹ * x)

theorem perturbation_contDiff (s : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (perturbation s t) :=
  contDiff_const.mul (profile_contDiff.comp (contDiff_const.mul contDiff_id))

theorem perturbation_rational (s : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    perturbation s t x = t ^ (s + 1) * x / (8 * (x ^ 2 + t ^ 2)) := by
  unfold perturbation profile
  field_simp [ne_of_gt ht]
  ring

theorem perturbation_odd (s : ℕ) (t x : ℝ) :
    perturbation s t (-x) = -perturbation s t x := by
  simp only [perturbation, profile, mul_neg, neg_sq, neg_div]

theorem perturbation_nonneg (s : ℕ) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ perturbation s t x := by
  unfold perturbation profile
  positivity

theorem perturbation_abs_le (s : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : ℝ) :
    |perturbation s t x| ≤ 1 / 8 := by
  have hp : |profile (t⁻¹ * x)| ≤ 1 := by
    simpa using profile_derivative_bound 0 (t⁻¹ * x)
  have hs : t ^ s ≤ 1 := pow_le_one₀ ht ht1
  calc
    |perturbation s t x| = t ^ s / 8 * |profile (t⁻¹ * x)| := by
      rw [perturbation, abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ t ^ s / 8 * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ 1 / 8 := by linarith

theorem gap_mul_perturbation_le (s : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    x * perturbation s t x ≤ t ^ (s + 1) / 8 := by
  rw [perturbation_rational s ht]
  have hden : 0 < x ^ 2 + t ^ 2 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity : 0 < 8 * (x ^ 2 + t ^ 2))
    (by norm_num : (0 : ℝ) < 8)).mpr
  nlinarith [mul_nonneg (pow_nonneg ht.le (s + 1)) (sq_nonneg t)]

theorem perturbation_derivative_bound {s k : ℕ} (hk : k ≤ s) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (x : ℝ) :
    |iteratedDeriv k (perturbation s t) x| ≤ k.factorial / 8 := by
  have hd : ContDiff ℝ k profile := profile_contDiff.of_le (by simp)
  have he : iteratedDeriv k (perturbation s t) x =
      t ^ s / 8 * (t⁻¹ ^ k * iteratedDeriv k profile (t⁻¹ * x)) := by
    change iteratedDeriv k (fun y => t ^ s / 8 * profile (t⁻¹ * y)) x = _
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul hd]
  rw [he, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t ^ s / 8),
    abs_of_nonneg (by positivity : 0 ≤ t⁻¹ ^ k)]
  have hc : t ^ s / 8 * t⁻¹ ^ k ≤ 1 / 8 := by
    have hh : t ^ s * t⁻¹ ^ k = t ^ (s - k) := by
      simpa only [div_eq_mul_inv, inv_pow] using (pow_sub₀ t (ne_of_gt ht) hk).symm
    have hp := pow_le_one₀ ht.le ht1 (n := s - k)
    nlinarith
  calc
    _ = (t ^ s / 8 * t⁻¹ ^ k) * |iteratedDeriv k profile (t⁻¹ * x)| := by ring
    _ ≤ (t ^ s / 8 * t⁻¹ ^ k) * k.factorial :=
      mul_le_mul_of_nonneg_left (profile_derivative_bound k _) (by positivity)
    _ ≤ k.factorial / 8 := by nlinarith

end ThresholdHC.SmoothDensity
