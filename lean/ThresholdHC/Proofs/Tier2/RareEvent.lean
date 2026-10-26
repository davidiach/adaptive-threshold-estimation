import ThresholdHC.Statements2

noncomputable section

namespace ThresholdHC.Proofs

open ThresholdHC Real

theorem rare_sqrt_tangent (h t d v : ℝ) (hh : 0 ≤ h) (ht : 0 < t)
    (hd : 0 < d) (hv : 0 ≤ v) :
    h * Real.sqrt v / d ≤ h * t / d ^ 2 +
      (h / (2 * t)) * (v - t ^ 2 / d ^ 2) := by
  have hc : 2 * t * d * Real.sqrt v ≤ d ^ 2 * v + t ^ 2 := by
    have hs := Real.sq_sqrt hv
    nlinarith [sq_nonneg (d * Real.sqrt v - t)]
  have hb := mul_le_mul_of_nonneg_left hc hh
  have hden : 0 < 2 * t * d ^ 2 := by positivity
  have hm := (div_le_div_iff_of_pos_right hden).2 hb
  convert hm using 1 <;> field_simp <;> ring

theorem rare_saturated_tangent (h t d v : ℝ) (hh : 0 < h) (ht : h < t)
    (hd : 0 < d) (hdt : d ≤ t) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    min v (h * Real.sqrt v / d) ≤ min 1 (h / d) + (h / (2 * t)) * (v - 1) := by
  have ht0 : 0 < t := lt_trans hh ht
  have hlambda : h / (2 * t) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * t)).2
    linarith
  have hlin : v ≤ 1 + (h / (2 * t)) * (v - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlambda) (sub_nonneg.mpr hv1)]
  have hs : Real.sqrt v ≤ (v + 1) / 2 := by
    have hsq := Real.sq_sqrt hv
    nlinarith [sq_nonneg (Real.sqrt v - 1)]
  have hroot := mul_le_mul_of_nonneg_left hs (div_nonneg hh.le hd.le)
  have hderiv : h / (2 * t) ≤ h / (2 * d) := by
    exact div_le_div_of_nonneg_left hh.le (by positivity) (by linarith)
  have hnegative := mul_le_mul_of_nonpos_right hderiv (sub_nonpos.mpr hv1)
  have hother : h * Real.sqrt v / d ≤ h / d + (h / (2 * t)) * (v - 1) := by
    have hid : (h / d) * ((v + 1) / 2) = h / d + (h / (2 * d)) * (v - 1) := by ring
    rw [hid] at hroot
    have hsame : (h / d) * Real.sqrt v = h * Real.sqrt v / d := by ring
    rw [hsame] at hroot
    linarith
  by_cases hh1 : 1 ≤ h / d
  · rw [min_eq_left hh1]
    exact (min_le_left _ _).trans hlin
  · rw [min_eq_right (le_of_not_ge hh1)]
    exact (min_le_right _ _).trans hother

theorem rare_supporting_line (h t d v : ℝ) (hh : 0 < h) (ht : h < t)
    (hd : 0 < d) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    min v (h * Real.sqrt v / d) ≤
      min (min 1 (t ^ 2 / d ^ 2))
        (h * Real.sqrt (min 1 (t ^ 2 / d ^ 2)) / d) +
      (h / (2 * t)) * (v - min 1 (t ^ 2 / d ^ 2)) := by
  have ht0 : 0 < t := lt_trans hh ht
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  by_cases hdt : d ≤ t
  · have hc : 1 ≤ t ^ 2 / d ^ 2 := by
      apply (le_div_iff₀ hd2).2
      nlinarith
    rw [min_eq_left hc]
    simpa using rare_saturated_tangent h t d v hh ht hd hdt hv hv1
  · have htd : t < d := lt_of_not_ge hdt
    have hc : t ^ 2 / d ^ 2 ≤ 1 := by
      apply (div_le_iff₀ hd2).2
      nlinarith
    have hroot : Real.sqrt (t ^ 2 / d ^ 2) = t / d := by
      rw [Real.sqrt_div (sq_nonneg t), Real.sqrt_sq ht0.le, Real.sqrt_sq hd.le]
    have hbranch : h * (t / d) / d ≤ t ^ 2 / d ^ 2 := by
      have hn := mul_le_mul_of_nonneg_right ht.le ht0.le
      have := div_le_div_of_nonneg_right hn hd2.le
      convert this using 1 <;> field_simp <;> ring
    rw [min_eq_right hc, hroot, min_eq_right hbranch]
    have hb := rare_sqrt_tangent h t d v hh.le ht0 hd hv
    have heq : h * (t / d) / d = h * t / d ^ 2 := by field_simp
    rw [heq]
    exact (min_le_right _ _).trans hb

theorem psi_optimizer_atomic : ThresholdHC.Targets.psi_optimizer_atomic := by
  intro k w d v ρ t h hw hwtotal hd hρ hρ1 hh ht hmass hv hbudget
  have hlambda : 0 ≤ h / (2 * t) := by
    have ht0 : 0 < t := lt_trans hh ht
    positivity
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    mul_le_mul_of_nonneg_left
      (rare_supporting_line h t (d j) (v j) hh ht (hd j).1 (hv j).1 (hv j).2)
      (hw j).le)
  have hbudget' : (∑ j, w j * (v j - min 1 (t ^ 2 / d j ^ 2))) ≤ 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [hmass]
    linarith
  have hpenalty := mul_nonpos_of_nonneg_of_nonpos hlambda hbudget'
  have heq : (∑ j, w j *
      (min (min 1 (t ^ 2 / d j ^ 2))
          (h * Real.sqrt (min 1 (t ^ 2 / d j ^ 2)) / d j) +
        (h / (2 * t)) * (v j - min 1 (t ^ 2 / d j ^ 2)))) =
      (∑ j, w j * min (min 1 (t ^ 2 / d j ^ 2))
          (h * Real.sqrt (min 1 (t ^ 2 / d j ^ 2)) / d j)) +
      (h / (2 * t)) * (∑ j, w j * (v j - min 1 (t ^ 2 / d j ^ 2))) := by
    simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq] at hs
  linarith

end ThresholdHC.Proofs

