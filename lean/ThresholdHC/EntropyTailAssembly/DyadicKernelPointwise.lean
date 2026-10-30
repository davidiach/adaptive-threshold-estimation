import ThresholdHC.EntropyTailAssembly.KernelMoments
import ThresholdHC.EntropyTail.EntropyMoment

/-! Pointwise dyadic envelopes for the homogeneous kernel sum. -/

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6 ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTail

def scaledKernel (k : ℕ) (d : ℝ) : ℝ :=
  ((2:ℝ)^k * ordinaryErrorKernel (4^k) d + (2:ℝ)⁻¹^k * ordinaryWorkKernel (4^k) d)/2

theorem four_pow_eq_two (k : ℕ) : (4:ℝ)^k = (2^k)^2 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem scaledKernel_nonneg (k : ℕ) (d : ℝ) : 0 ≤ scaledKernel k d := by
  unfold scaledKernel
  positivity [ordinaryErrorKernel_nonneg (4^k) d, ordinaryWorkKernel_nonneg (by positivity : (0:ℝ) ≤ 4^k) d]

theorem scaledKernel_le_cap (k : ℕ) (d : ℝ) : scaledKernel k d ≤ (2:ℝ)^k := by
  have he := mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) ((4^k*d^2)⁻¹^2))
    (by positivity : (0:ℝ) ≤ 2^k)
  have hw := mul_le_mul_of_nonneg_left
    (min_le_left ((4:ℝ)^k) (17*d⁻¹^2*(1+max 0 (log (4^k*d^2)))))
    (by positivity : (0:ℝ) ≤ (2:ℝ)⁻¹^k)
  have hi : (2:ℝ)⁻¹^k * 4^k = 2^k := by
    rw [four_pow_eq_two, inv_pow]
    field_simp
  rw [hi] at hw
  unfold scaledKernel ordinaryErrorKernel ordinaryWorkKernel
  linarith

theorem band_inverse_bound (j : ℕ) (d : Gap) (hd : d ∈ band j) :
    (d:ℝ)⁻¹ ≤ 2*(2:ℝ)^(j+1) := by
  have hb : bandEdge j / 2 = (2*(2:ℝ)^(j+1))⁻¹ := by
    unfold bandEdge
    rw [inv_pow]
    field_simp
  have hdl := hd.1
  rw [hb] at hdl
  have hh := inv_anti₀ (by positivity : (0:ℝ) < (2*(2:ℝ)^(j+1))⁻¹) hdl.le
  simpa using hh

theorem band_scaled_gap_le_one (j : ℕ) (d : Gap) (hd : d ∈ band j) :
    (2:ℝ)^(j+1)*(d:ℝ) ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left hd.2 (by positivity : (0:ℝ) ≤ 2^(j+1))
  simpa [bandEdge, inv_pow] using h

theorem band_large_log (j r : ℕ) (d : Gap) (hd : d ∈ band j) :
    1+max 0 (log ((4:ℝ)^(j+1+(r+1))*(d:ℝ)^2)) ≤ 2*(1+(r+1:ℕ)) := by
  have hg := band_scaled_gap_le_one j d hd
  have hy : 0 ≤ (2:ℝ)^(j+1)*(d:ℝ) := by positivity [d.property.1]
  have hsq : ((2:ℝ)^(j+1)*(d:ℝ))^2 ≤ 1 := by nlinarith
  have he : (4:ℝ)^(j+1+(r+1))*(d:ℝ)^2 =
      4^(r+1)*((2:ℝ)^(j+1)*(d:ℝ))^2 := by
    rw [pow_add, four_pow_eq_two (j+1)]
    ring
  have hx : (4:ℝ)^(j+1+(r+1))*(d:ℝ)^2 ≤ 4^(r+1) := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ 4^(r+1))]
  have hl := log_le_log (by positivity [d.property.1]) hx
  rw [log_pow] at hl
  have hlog : log (4:ℝ) ≤ 2 := by
    have he : (4:ℝ) = 2^2 := by norm_num
    rw [he, log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hr : (0:ℝ) ≤ (r+1:ℕ) := by positivity
  have hb : log ((4:ℝ)^(j+1+(r+1))*(d:ℝ)^2) ≤ 2*(r+1:ℕ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hr]
  have hm : max 0 (log ((4:ℝ)^(j+1+(r+1))*(d:ℝ)^2)) ≤ 2*(r+1:ℕ) :=
    max_le (by positivity) hb
  push_cast at hm ⊢
  linarith

theorem band_large_scaledKernel (j r : ℕ) (d : Gap) (hd : d ∈ band j) :
    scaledKernel (j+1+(r+1)) (d:ℝ) ≤ (2:ℝ)^(j+1) *
      (8*((1/8:ℝ)^(r+1)) + 68*((1/2:ℝ)^(r+1))*(1+(r+1:ℕ))) := by
  have hi := band_inverse_bound j d hd
  have hdi : 0 ≤ (d:ℝ)⁻¹ := by positivity [d.property.1]
  have hi2 := pow_le_pow_left₀ hdi hi 2
  have hi4 := pow_le_pow_left₀ hdi hi 4
  have he : ordinaryErrorKernel ((4:ℝ)^(j+1+(r+1))) (d:ℝ) ≤
      ((4:ℝ)^(j+1+(r+1)))⁻¹^2 * (2*(2:ℝ)^(j+1))^4 := by
    calc
      _ ≤ (((4:ℝ)^(j+1+(r+1)))*(d:ℝ)^2)⁻¹^2 := min_le_right _ _
      _ = ((4:ℝ)^(j+1+(r+1)))⁻¹^2 * (d:ℝ)⁻¹^4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hi4 (by positivity)
  have hw : ordinaryWorkKernel ((4:ℝ)^(j+1+(r+1))) (d:ℝ) ≤
      17*(2*(2:ℝ)^(j+1))^2*(2*(1+(r+1:ℕ))) := by
    apply (min_le_right _ _).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hi2 (by norm_num))
      (band_large_log j r d hd) (by positivity) (by positivity)
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ 2^(j+1+(r+1))))
    (mul_le_mul_of_nonneg_left hw (by positivity : (0:ℝ) ≤ (2:ℝ)⁻¹^(j+1+(r+1))))
  unfold scaledKernel
  apply (div_le_div_of_nonneg_right hh (by norm_num)).trans_eq
  have he8 : (1/8:ℝ)^(r+1) = ((2:ℝ)^(r+1))⁻¹^3 := by
    rw [← inv_pow, ← pow_mul, Nat.mul_comm (r+1) 3, pow_mul]
    norm_num
  rw [he8]
  simp only [pow_add, four_pow_eq_two, one_div, inv_pow]
  field_simp
  ring

end ThresholdHC.EntropyTailAssembly
