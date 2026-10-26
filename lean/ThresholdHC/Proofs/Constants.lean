import ThresholdHC.Statements

namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory

private lemma r_bounds : 0 ≤ rLevel ∧ rLevel ≤ (442/625 : ℝ) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hslower : (7071/5000 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  constructor
  · unfold rLevel; positivity
  · unfold rLevel
    apply (inv_le_iff_one_le_mul₀ hspos).2
    nlinarith

theorem constant_second_moment : ThresholdHC.Targets.constant_second_moment := by
  change 5 / (1-rLevel) * (1/(1-rLevel) + 1/(1-rLevel^3)) < 85
  obtain ⟨hr0, hr⟩ := r_bounds
  have hpow : rLevel ^ 3 ≤ (442/625 : ℝ) ^ 3 := pow_le_pow_left₀ hr0 hr 3
  have h1 : 1/(1-rLevel) ≤ 1/(1-(442/625 : ℝ)) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h3 : 1/(1-rLevel^3) ≤ 1/(1-(442/625 : ℝ)^3) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h5 : 5/(1-rLevel) ≤ 5/(1-(442/625 : ℝ)) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 5 by norm_num)
  have hpos : 0 ≤ 1/(1-rLevel) + 1/(1-rLevel^3) := by
    have : 0 < 1-rLevel := by linarith
    have : 0 < 1-rLevel^3 := by norm_num at hpow ⊢; linarith
    positivity
  calc
    _ ≤ 5/(1-(442/625 : ℝ)) * (1/(1-(442/625 : ℝ)) + 1/(1-(442/625 : ℝ)^3)) :=
      mul_le_mul h5 (add_le_add h1 h3) hpos (by norm_num)
    _ < 85 := by norm_num

theorem constant_work : ThresholdHC.Targets.constant_work := by
  change 34 * (2 + Real.log 2 + rLevel * Real.log 2 / (1-rLevel)) < 149
  obtain ⟨hr0, hr⟩ := r_bounds
  have hrden : 0 < 1-rLevel := by linarith
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : Real.log 2 ≤ (173287/250000 : ℝ) := by linarith [Real.log_two_lt_d9]
  have h1 : 1/(1-rLevel) ≤ 1/(1-(442/625 : ℝ)) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hprod : rLevel * Real.log 2 / (1-rLevel) ≤
      (442/625 : ℝ) * (173287/250000) * (1/(1-(442/625 : ℝ))) := by
    rw [div_eq_mul_inv]
    apply mul_le_mul
    · exact mul_le_mul hr hlog hlog0 (by norm_num)
    · simpa using h1
    · positivity
    · norm_num
  calc
    _ ≤ 34 * (2 + (173287/250000 : ℝ) + (442/625 : ℝ) * (173287/250000) * (1/(1-(442/625 : ℝ)))) := by linarith
    _ < 149 := by norm_num

theorem kl_delta_identity : ThresholdHC.Targets.kl_delta_identity := by
  intro δ hδ hδlt
  have hd : δ ≠ 0 := ne_of_gt hδ
  have h1d : 1 - δ ≠ 0 := ne_of_gt (by linarith)
  dsimp [klB]
  simp only [sub_sub_cancel]
  rw [Real.log_div h1d hd, Real.log_div hd h1d]
  ring

theorem kl_delta_lower : ThresholdHC.Targets.kl_delta_lower := by
  intro δ hδ hδle
  have hd : δ ≠ 0 := ne_of_gt hδ
  have h1d : 0 < 1-δ := by linarith
  have hs : δ ≤ (1-δ)^2 := by nlinarith
  have hlog := Real.log_le_log hδ hs
  rw [Real.log_pow] at hlog
  have hratio : 1 ≤ (1-δ)/δ := (one_le_div hδ).2 (by linarith)
  have hlogratio : 0 ≤ Real.log ((1-δ)/δ) := Real.log_nonneg hratio
  have hmul := mul_le_mul_of_nonneg_right (show (1/2 : ℝ) ≤ 1-2*δ by linarith) hlogratio
  rw [Real.log_div (ne_of_gt h1d) hd] at hmul
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hd, Real.log_one,
    Real.log_div (ne_of_gt h1d) hd]
  norm_num at hlog
  nlinarith

end ThresholdHC.Proofs
