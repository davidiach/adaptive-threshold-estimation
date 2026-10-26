import ThresholdHC.Statements

namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory

private lemma sym_kl_hellinger_ordered (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : y ≤ x) :
    4 * (Real.sqrt x - Real.sqrt y)^2 ≤ (x-y) * Real.log (x/y) := by
  have ha : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hb : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hab : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hxy
  have habsum : Real.sqrt x + Real.sqrt y ≠ 0 := ne_of_gt (add_pos ha hb)
  have hratio : 0 ≤ Real.sqrt x / Real.sqrt y - 1 := by
    apply sub_nonneg.mpr
    exact (one_le_div hb).2 hab
  have hlog := Real.le_log_one_add_of_nonneg hratio
  have har : 1 + (Real.sqrt x / Real.sqrt y - 1) = Real.sqrt x / Real.sqrt y := by ring
  rw [har, Real.log_div (ne_of_gt ha) (ne_of_gt hb), Real.log_sqrt hx.le,
      Real.log_sqrt hy.le] at hlog
  have hfrac :
      2 * (Real.sqrt x / Real.sqrt y - 1) / (Real.sqrt x / Real.sqrt y - 1 + 2)
        = 2 * (Real.sqrt x - Real.sqrt y) / (Real.sqrt x + Real.sqrt y) := by
    field_simp
    <;> nlinarith
  rw [hfrac] at hlog
  have hlog2 : 4 * (Real.sqrt x - Real.sqrt y) / (Real.sqrt x + Real.sqrt y)
      ≤ Real.log (x/y) := by
    rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)]
    convert mul_le_mul_of_nonneg_left hlog (show (0:ℝ) ≤ 2 by norm_num) using 1 <;> ring
  calc
    4 * (Real.sqrt x - Real.sqrt y)^2 =
        (x-y) * (4 * (Real.sqrt x - Real.sqrt y) / (Real.sqrt x + Real.sqrt y)) := by
      rw [← mul_div_assoc]
      apply (eq_div_iff habsum).2
      calc
        4 * (Real.sqrt x - Real.sqrt y)^2 * (Real.sqrt x + Real.sqrt y)
            = ((Real.sqrt x)^2 - (Real.sqrt y)^2) * (4 * (Real.sqrt x - Real.sqrt y)) := by ring
        _ = _ := by rw [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog2 (sub_nonneg.mpr hxy)

theorem sym_kl_hellinger_pointwise : ThresholdHC.Targets.sym_kl_hellinger_pointwise := by
  intro x y hx hy
  rcases le_total y x with hxy | hxy
  · exact sym_kl_hellinger_ordered x y hx hy hxy
  · have h := sym_kl_hellinger_ordered y x hy hx hxy
    rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)]
    rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx)] at h
    nlinarith

private lemma kl_term_lower (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * (a - Real.sqrt (a*b)) ≤ a * Real.log (a/b) := by
  have hra : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hroot : a * Real.sqrt (b/a) = Real.sqrt (a*b) := by
    rw [Real.sqrt_div (le_of_lt hb), Real.sqrt_mul (le_of_lt ha)]
    have hsqa : (Real.sqrt a)^2 = a := Real.sq_sqrt (le_of_lt ha)
    rw [← mul_div_assoc, div_eq_iff (ne_of_gt hra)]
    calc
      a * Real.sqrt b = (Real.sqrt a)^2 * Real.sqrt b := by rw [hsqa]
      _ = _ := by ring
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (div_pos hb ha))
  rw [Real.log_sqrt (le_of_lt (div_pos hb ha)), Real.log_div (ne_of_gt hb) (ne_of_gt ha)] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog (le_of_lt ha)
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
  nlinarith

theorem kl_ge_two_hell_finite : ThresholdHC.Targets.kl_ge_two_hell_finite := by
  intro n p q hp hq hp1 hq1
  calc
    2 * hell2 p q = ∑ i, 2 * (p i - Real.sqrt (p i * q i)) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hp1]
      rfl
    _ ≤ klFin p q := Finset.sum_le_sum (fun i _ => kl_term_lower (p i) (q i) (hp i) (hq i))

private lemma sqrt_distance_sum {n : ℕ} (p q : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    (∑ i, (Real.sqrt (p i) - Real.sqrt (q i))^2) = 2 * hell2 p q := by
  calc
    (∑ i, (Real.sqrt (p i) - Real.sqrt (q i))^2) =
        ∑ i, (p i + q i - 2 * Real.sqrt (p i * q i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.sqrt_mul (hp i)]
      nlinarith [Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
    _ = 2 * hell2 p q := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hq1]
      unfold hell2
      ring

theorem sym_kl_ge_eight_hell_finite : ThresholdHC.Targets.sym_kl_ge_eight_hell_finite := by
  intro n p q hp hq hp1 hq1
  calc
    8 * hell2 p q = ∑ i, 4 * (Real.sqrt (p i) - Real.sqrt (q i))^2 := by
      rw [← Finset.mul_sum, sqrt_distance_sum p q (fun i => (hp i).le)
        (fun i => (hq i).le) hp1 hq1]
      ring
    _ ≤ ∑ i, (p i - q i) * Real.log (p i / q i) :=
      Finset.sum_le_sum (fun i _ => sym_kl_hellinger_pointwise (p i) (q i) (hp i) (hq i))
    _ = klFin p q + klFin q p := by
      unfold klFin
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.log_div (ne_of_gt (hp i)) (ne_of_gt (hq i)),
        Real.log_div (ne_of_gt (hq i)) (ne_of_gt (hp i))]
      ring

private lemma centered_second {n : ℕ} (p Y : Fin n → ℝ)
    (hp1 : ∑ i, p i = 1) (c : ℝ) :
    (∑ i, p i * (Y i - c)^2) = varFin p Y + (meanFin p Y - c)^2 := by
  calc
    (∑ i, p i * (Y i - c)^2) = ∑ i,
        (p i * (Y i - meanFin p Y)^2 +
          2 * (meanFin p Y - c) * (p i * Y i) +
          (c^2 - (meanFin p Y)^2) * p i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp1, mul_one]
      unfold varFin meanFin
      ring

theorem two_point_variance_finite : ThresholdHC.Targets.two_point_variance_finite := by
  intro n p q Y hp hq hp1 hq1
  let c := (meanFin p Y + meanFin q Y) / 2
  have hdiff :
      (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) *
        ((Y i - c) * (Real.sqrt (p i) + Real.sqrt (q i))))
        = meanFin p Y - meanFin q Y := by
    calc
      _ = ∑ i, (p i - q i) * (Y i - c) := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = ((Real.sqrt (p i))^2 - (Real.sqrt (q i))^2) * (Y i - c) := by ring
          _ = _ := by rw [Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
      _ = _ := by
        simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
          ← Finset.mul_sum, hp1, hq1, one_mul, mul_one]
        unfold meanFin
        ring
  have hcenter : (∑ i, (Y i-c)^2 * (p i+q i)) =
      varFin p Y + varFin q Y + (meanFin p Y - meanFin q Y)^2 / 2 := by
    calc
      _ = (∑ i, p i * (Y i-c)^2) + (∑ i, q i * (Y i-c)^2) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [centered_second p Y hp1 c, centered_second q Y hq1 c]
        dsimp [c]
        ring
  have hbound :
      (∑ i, ((Y i-c) * (Real.sqrt (p i) + Real.sqrt (q i)))^2)
        ≤ 2 * (∑ i, (Y i-c)^2 * (p i+q i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hs : (Real.sqrt (p i) + Real.sqrt (q i))^2 ≤ 2 * (p i + q i) := by
      nlinarith [Real.sq_sqrt (hp i), Real.sq_sqrt (hq i),
        sq_nonneg (Real.sqrt (p i) - Real.sqrt (q i))]
    calc
      _ = (Y i-c)^2 * (Real.sqrt (p i) + Real.sqrt (q i))^2 := by ring
      _ ≤ (Y i-c)^2 * (2 * (p i+q i)) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
      _ = _ := by ring
  have hfactor : 0 ≤ 2 * hell2 p q := by
    rw [← sqrt_distance_sum p q hp hq hp1 hq1]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n => Real.sqrt (p i) - Real.sqrt (q i))
    (fun i : Fin n => (Y i-c) * (Real.sqrt (p i) + Real.sqrt (q i)))
  rw [hdiff, sqrt_distance_sum p q hp hq hp1 hq1] at hcs
  have hscaled := mul_le_mul_of_nonneg_left hbound hfactor
  rw [hcenter] at hscaled
  nlinarith

end ThresholdHC.Proofs
