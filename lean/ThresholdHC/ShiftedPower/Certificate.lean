import ThresholdHC.ShiftedPower.Allocated

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.ShiftedPower
open ThresholdHC.EntropyTailUpper

def amplitude (α a : ℝ) (k : ℕ) : ℝ := sqrt ((2:ℝ)^k)*massBound α a k

theorem amplitude_pos {α a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < amplitude α a k :=
  mul_pos (by positivity) (mass_positive ha k)

theorem amplitude_succ {α a : ℝ} (ha : 0 < a) (k : ℕ) :
    amplitude α a (k+1) = amplitude α a k*summationRatio α := by
  unfold amplitude summationRatio
  rw [pow_succ,Real.sqrt_mul (by positivity : 0 ≤ (2:ℝ)^k),mass_succ ha]
  ring

theorem amplitude_add {α a : ℝ} (ha : 0 < a) (k j : ℕ) :
    amplitude α a (k+j) = amplitude α a k*(summationRatio α)^j := by
  induction j with
  | zero => simp
  | succ j hj => rw [Nat.add_succ,amplitude_succ ha,hj,pow_succ,mul_assoc]

theorem certificate_formula {α a : ℝ} (hα : 0 < α) (hu : α < 2) (ha : 0 < a) (k J : ℕ) :
    allocationCertificate (varianceWeights α a k J) (costWeights α a k J) =
      4*sqrt (workConstant α)*amplitude α a k*(∑ i : Fin (J+1), (summationRatio α)^i.val) := by
  have hW := (workConstant_pos hα hu).le
  unfold allocationCertificate
  have ht (i : Fin (J+1)) :
      sqrt (varianceWeights α a k J i*costWeights α a k J i) =
        4*sqrt (workConstant α)*amplitude α a k*(summationRatio α)^i.val := by
    rw [show varianceWeights α a k J i*costWeights α a k J i =
        (4*sqrt (workConstant α)*amplitude α a (k+i.val))^2 by
      unfold varianceWeights costWeights amplitude
      rw [work_formula]
      simp only [mul_pow,Real.sq_sqrt hW,Real.sq_sqrt (show 0 ≤ (2:ℝ)^(k+i.val) by positivity)]
      ring]
    rw [Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _)) (amplitude_pos ha _).le),
      amplitude_add ha]
    ring
  simp only [ht,Finset.mul_sum]

theorem linear_certificate {a : ℝ} (ha : 0 < a) (k J : ℕ) :
    allocationCertificate (varianceWeights 1 a k J) (costWeights 1 a k J) =
      4*sqrt (workConstant 1)/a*(J+1) := by
  rw [certificate_formula (by norm_num) (by norm_num) ha,ratio_eq_one]
  have he : amplitude 1 a k = 1/a := by
    unfold amplitude massBound resolution
    rw [Real.rpow_one]
    field_simp
  rw [he]
  simp only [one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,mul_one]
  ring

theorem finite_geom_sum {s : ℝ} (hs : 0 ≤ s) (hu : s < 1) (J : ℕ) :
    (∑ i : Fin (J+1), s^i.val) ≤ 1/(1-s) := by
  rw [Fin.sum_univ_eq_sum_range]
  apply (le_div_iff₀ (sub_pos.mpr hu)).mpr
  have he := geom_sum_mul s (J+1)
  nlinarith only [he,pow_nonneg hs (J+1)]

theorem intermediate_certificate {α a : ℝ} (hα : 1 < α) (hu : α < 2) (ha : 0 < a) (k J : ℕ) :
    allocationCertificate (varianceWeights α a k J) (costWeights α a k J) ≤
      4*sqrt (workConstant α)*amplitude α a k/(1-summationRatio α) := by
  rw [certificate_formula (by linarith) hu ha]
  have hs : 0 ≤ summationRatio α := mul_nonneg (sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hnonneg : 0 ≤ 4*sqrt (workConstant α)*amplitude α a k :=
    mul_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _)) (amplitude_pos ha k).le
  have h := mul_le_mul_of_nonneg_left (finite_geom_sum hs (ratio_lt_one hα) J) hnonneg
  simpa only [mul_one_div] using h

end ThresholdHC.ShiftedPower
