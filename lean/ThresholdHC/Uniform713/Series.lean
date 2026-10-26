import ThresholdHC.Uniform713.Common
import ThresholdHC.Uniform713.Arithmetic

/-!
Geometric-series estimates for the uniform variance-work bound.
The explicit classifier envelopes imply summable second moments with constant 23
and summable expected work with constant 31. Probability-model assumptions are
discharged in other modules; the statements here are deterministic inequalities.
-/
set_option maxHeartbeats 800000
noncomputable section
namespace ThresholdHC.Uniform713
open Real Finset

/-- The envelope for the second moment of the single-term estimator at one level. -/
def secondMomentEnvelope (l : ℕ) (d : ℝ) : ℝ :=
  min 1 (3 / (cap l * d ^ 2) ^ 2) / levelProb l

private lemma r_sq : rLevel ^ 2 = (1/2 : ℝ) := by
  unfold rLevel
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

private lemma cap_mul_r_sq (l : ℕ) : cap l * (rLevel ^ l)^2 = 1 := by
  rw [← pow_mul, Nat.mul_comm l 2, pow_mul, r_sq]
  unfold cap
  rw [← mul_pow]
  norm_num

private lemma cap_eq_inv_r_sq (l : ℕ) : cap l = (rLevel ^ l)⁻¹ ^ 2 := by
  have h := cap_mul_r_sq l
  have hr : rLevel ^ l ≠ 0 := ne_of_gt (pow_pos rLevel_pos l)
  field_simp
  exact h

private lemma inverse_geom_sum (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n : ℕ) :
    (1-r) * (∑ k ∈ range (n+1), (r^k)⁻¹) = (r^n)⁻¹-r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, pow_succ]
    have hn : r^n ≠ 0 := ne_of_gt (pow_pos hr n)
    field_simp
    <;> ring

private lemma inverse_geom_sum_le (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n : ℕ) :
    ∑ k ∈ range (n+1), (r^k)⁻¹ ≤ (r^n)⁻¹/(1-r) := by
  apply (le_div_iff₀ (sub_pos.mpr hr1)).2
  rw [mul_comm, inverse_geom_sum r hr hr1]
  linarith

private lemma envelope_nonneg (l : ℕ) (d : ℝ) : 0 ≤ secondMomentEnvelope l d := by
  unfold secondMomentEnvelope
  apply div_nonneg
  · apply le_min (by norm_num)
    exact div_nonneg (by norm_num) (sq_nonneg _)
  · exact (levelProb_pos l).le

private lemma envelope_prefix (l : ℕ) (d : ℝ) :
    secondMomentEnvelope l d ≤ (1-rLevel)⁻¹ * (rLevel^l)⁻¹ := by
  unfold secondMomentEnvelope levelProb
  have h := (div_le_div_of_nonneg_right (min_le_left (1:ℝ) (3 / (cap l * d ^ 2) ^ 2)) (levelProb_pos l).le)
  simpa [levelProb, one_div, mul_inv_rev, mul_comm] using h

private lemma envelope_tail (l : ℕ) (d : ℝ) (hd : 0 < d) :
    secondMomentEnvelope l d ≤ (1-rLevel)⁻¹ * (3/(d^4)) * (rLevel^3)^l := by
  unfold secondMomentEnvelope
  calc
    _ ≤ (3/(cap l*d^2)^2)/levelProb l :=
      div_le_div_of_nonneg_right (min_le_right _ _) (levelProb_pos l).le
    _ = _ := by
      rw [cap_eq_inv_r_sq]
      unfold levelProb
      have hr : rLevel^l ≠ 0 := ne_of_gt (pow_pos rLevel_pos l)
      have hr1 : 1-rLevel ≠ 0 := ne_of_gt (sub_pos.mpr rLevel_lt_one)
      have hd0 : d ≠ 0 := ne_of_gt hd
      rw [← pow_mul, Nat.mul_comm 3 l, pow_mul]
      field_simp
      <;> ring


private lemma r_cube_lt_one : rLevel^3 < 1 :=
  pow_lt_one₀ rLevel_pos.le rLevel_lt_one (by norm_num)

/-- Absolute convergence of the weighted classifier error envelope. -/
theorem summable_secondMomentEnvelope (d : ℝ) (hd : 0 < d) :
    Summable (fun l => secondMomentEnvelope l d) := by
  exact Summable.of_nonneg_of_le (fun l => envelope_nonneg l d)
    (fun l => envelope_tail l d hd)
    ((summable_geometric_of_lt_one (pow_nonneg rLevel_pos.le 3) r_cube_lt_one).mul_left _)

/-- The dyadic classifier error envelope gives a second-moment constant below 23. -/
theorem tsum_secondMomentEnvelope_lt (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1/2) :
    (∑' l, secondMomentEnvelope l d) < 23 / d := by
  have hr0 : 0 ≤ rLevel := rLevel_pos.le
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one
    (show 0 < 3*d/4 by positivity) (show 3*d/4 ≤ 1 by linarith)
    rLevel_pos rLevel_lt_one
  have hr1 : 0 < 1-rLevel := sub_pos.mpr rLevel_lt_one
  have hr3 : 0 < 1-rLevel^3 := sub_pos.mpr r_cube_lt_one
  have hdp : (rLevel^n)⁻¹ ≤ 4/(3*d) := by
    have h := one_div_le_one_div_of_le (show 0 < 3*d/4 by positivity) hnhi
    simpa [one_div, inv_div] using h
  have hpre : (∑ l ∈ range (n+1), secondMomentEnvelope l d) ≤
      (4/(3*d)) * (1-rLevel)⁻¹ * (1-rLevel)⁻¹ := by
    calc
      _ ≤ ∑ l ∈ range (n+1), (1-rLevel)⁻¹ * (rLevel^l)⁻¹ :=
        sum_le_sum (fun l _ => envelope_prefix l d)
      _ = (1-rLevel)⁻¹ * (∑ l ∈ range (n+1), (rLevel^l)⁻¹) := by rw [mul_sum]
      _ ≤ (1-rLevel)⁻¹ * ((rLevel^n)⁻¹/(1-rLevel)) :=
        mul_le_mul_of_nonneg_left (inverse_geom_sum_le _ rLevel_pos rLevel_lt_one n)
          (inv_nonneg.mpr hr1.le)
      _ ≤ (1-rLevel)⁻¹ * ((4/(3*d))/(1-rLevel)) := by gcongr
      _ = _ := by ring
  have hcoef : (3/d^4) * (rLevel^3)^(n+1) ≤ 4/(3*d) := by
    rw [← pow_mul, Nat.mul_comm 3 (n+1), pow_mul]
    have hc := pow_le_pow_left₀ (pow_pos rLevel_pos (n+1)).le hnlo.le 3
    calc
      _ ≤ (3/d^4) * (3*d/4)^3 := mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ 4/(3*d) := by
        apply (le_div_iff₀ (show 0 < 3*d by positivity)).2
        field_simp
        nlinarith [pow_pos hd 4]
  have ht : ∀ k, secondMomentEnvelope (k+(n+1)) d ≤
      ((1-rLevel)⁻¹ * (4/(3*d))) * (rLevel^3)^k := by
    intro k
    calc
      _ ≤ (1-rLevel)⁻¹ * (3/d^4) * (rLevel^3)^(k+(n+1)) := envelope_tail _ d hd
      _ = ((1-rLevel)⁻¹ * ((3/d^4)*(rLevel^3)^(n+1))) * (rLevel^3)^k := by
        rw [pow_add]; ring
      _ ≤ _ := by gcongr
  have hs := summable_secondMomentEnvelope d hd
  have htbound : (∑' k, secondMomentEnvelope (k+(n+1)) d) ≤
      (4/(3*d)) * (1-rLevel)⁻¹ * (1-rLevel^3)⁻¹ := by
    have hsum := (hasSum_geometric_of_lt_one (pow_nonneg rLevel_pos.le 3)
      r_cube_lt_one).mul_left ((1-rLevel)⁻¹ * (4/(3*d)))
    calc
      _ ≤ ∑' k, ((1-rLevel)⁻¹ * (4/(3*d))) * (rLevel^3)^k :=
        Summable.tsum_le_tsum ht ((summable_nat_add_iff (n+1)).2 hs) hsum.summable
      _ = _ := by rw [hsum.tsum_eq]; ring
  rw [← hs.sum_add_tsum_nat_add (n+1)]
  have hscalar := Arithmetic.geometric_second_moment_factor_lt
  have hfactor : 0 < 4/(3*d) := by positivity
  calc
    _ ≤ (4/(3*d)) * ((1/(1-rLevel)) * (1/(1-rLevel)+1/(1-rLevel^3))) := by
      convert add_le_add hpre htbound using 1 <;> ring
    _ < (4/(3*d)) * 17 := mul_lt_mul_of_pos_left hscalar hfactor
    _ < 23/d := by
      apply (lt_div_iff₀ hd).2
      have hd0 := ne_of_gt hd
      field_simp
      norm_num


private lemma work_nonneg (l : ℕ) (d : ℝ) : 0 ≤ workEnvelope l d := by
  unfold workEnvelope
  apply le_min (cap_pos l).le
  positivity

private lemma weighted_work_prefix (l : ℕ) (d : ℝ) :
    levelProb l * workEnvelope l d ≤ (1-rLevel) * (rLevel^l)⁻¹ := by
  calc
    _ ≤ levelProb l * cap l := mul_le_mul_of_nonneg_left (min_le_left _ _) (levelProb_pos l).le
    _ = _ := by
      rw [cap_eq_inv_r_sq]
      unfold levelProb
      have hr : rLevel^l ≠ 0 := ne_of_gt (pow_pos rLevel_pos l)
      field_simp

private lemma work_tail_log (d : ℝ) (hd : 0 < d) (n : ℕ) (hn : d ≤ rLevel^n) (k : ℕ) :
    max 0 (Real.log (cap (k+(n+1))*d^2)) ≤ ((k:ℝ)+1)*Real.log 2 := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hx0 : cap (n+1)*d^2 ≤ 2 := by
    rw [cap_succ, cap_eq_inv_r_sq]
    have hs := pow_le_pow_left₀ hd.le hn 2
    have hp : 0 < rLevel^n := pow_pos rLevel_pos n
    have h := (div_le_one (sq_pos_of_pos hp)).2 hs
    convert mul_le_mul_of_nonneg_left h (show (0:ℝ) ≤ 2 by norm_num) using 1 <;> ring
  have hx : cap (k+(n+1))*d^2 ≤ (2:ℝ)^(k+1) := by
    have h := mul_le_mul_of_nonneg_left hx0 (show 0 ≤ (2:ℝ)^k by positivity)
    simpa [cap, pow_add, pow_succ, mul_assoc] using h
  have hp : 0 < cap (k+(n+1))*d^2 := mul_pos (cap_pos _) (sq_pos_of_pos hd)
  have h := Real.log_le_log hp hx
  rw [Real.log_pow] at h
  push_cast at h
  exact max_le (by positivity) h

private lemma weighted_work_tail (d : ℝ) (hd : 0 < d) (n : ℕ)
    (hnlo : rLevel^(n+1) ≤ d) (hnhi : d ≤ rLevel^n) (k : ℕ) :
    levelProb (k+(n+1)) * workEnvelope (k+(n+1)) d ≤
      ((1-rLevel)/d) * (rLevel^k * (1+((k:ℝ)+1)*Real.log 2)) := by
  have hr0 : 0 ≤ rLevel := rLevel_pos.le
  have hr1 : 0 ≤ 1-rLevel := (sub_pos.mpr rLevel_lt_one).le
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcoef : (rLevel^(n+1)) * (d⁻¹)^2 ≤ d⁻¹ := by
    calc
      _ ≤ d * (d⁻¹)^2 := mul_le_mul_of_nonneg_right hnlo (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ ≤ levelProb (k+(n+1)) * ((d⁻¹)^2 *
        (1+max 0 (Real.log (cap (k+(n+1))*d^2)))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (levelProb_pos _).le
    _ ≤ levelProb (k+(n+1)) * ((d⁻¹)^2 * (1+((k:ℝ)+1)*Real.log 2)) := by
      apply mul_le_mul_of_nonneg_left _ (levelProb_pos _).le
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      linarith [work_tail_log d hd n hnhi k]
    _ = ((1-rLevel) * (rLevel^k * (1+((k:ℝ)+1)*Real.log 2))) *
        (rLevel^(n+1) * (d⁻¹)^2) := by
      unfold levelProb
      rw [pow_add]
      ring
    _ ≤ ((1-rLevel) * (rLevel^k * (1+((k:ℝ)+1)*Real.log 2))) * d⁻¹ := by
      apply mul_le_mul_of_nonneg_left hcoef
      positivity
    _ = _ := by ring

private lemma hasSum_work_majorant (d : ℝ) (hd : 0 < d) :
    HasSum (fun k : ℕ => ((1-rLevel)/d) *
      (rLevel^k * (1+((k:ℝ)+1)*Real.log 2)))
      ((1+Real.log 2+rLevel*Real.log 2/(1-rLevel))/d) := by
  have h0 := (hasSum_geometric_of_lt_one rLevel_pos.le rLevel_lt_one).mul_left (1+Real.log 2)
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one
    (show ‖rLevel‖ < 1 by simpa [Real.norm_eq_abs, abs_of_pos rLevel_pos] using rLevel_lt_one)).mul_left (Real.log 2)
  convert (h0.add h1).mul_left ((1-rLevel)/d) using 1
  · ext k
    ring
  · have hne := ne_of_gt (sub_pos.mpr rLevel_lt_one)
    field_simp
    <;> ring

private lemma work_sum_bound (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1/2) :
    Summable (fun l => levelProb l * workEnvelope l d) ∧
    (∑' l, levelProb l * workEnvelope l d) ≤
      (2+Real.log 2+rLevel*Real.log 2/(1-rLevel))/d := by
  have hr0 : 0 ≤ rLevel := rLevel_pos.le
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hd (by linarith : d ≤ 1)
    rLevel_pos rLevel_lt_one
  have hr1 : 0 < 1-rLevel := sub_pos.mpr rLevel_lt_one
  have hpre : (∑ l ∈ range (n+1), levelProb l * workEnvelope l d) ≤ 1/d := by
    calc
      _ ≤ ∑ l ∈ range (n+1), (1-rLevel) * (rLevel^l)⁻¹ :=
        sum_le_sum (fun l _ => weighted_work_prefix l d)
      _ = (1-rLevel) * (∑ l ∈ range (n+1), (rLevel^l)⁻¹) := by rw [mul_sum]
      _ ≤ (1-rLevel) * ((rLevel^n)⁻¹/(1-rLevel)) :=
        mul_le_mul_of_nonneg_left (inverse_geom_sum_le _ rLevel_pos rLevel_lt_one n) hr1.le
      _ = 1/(rLevel^n) := by field_simp
      _ ≤ 1/d := one_div_le_one_div_of_le hd hnhi
  have hsTail : Summable (fun k => levelProb (k+(n+1)) * workEnvelope (k+(n+1)) d) := by
    apply Summable.of_nonneg_of_le (fun k => mul_nonneg (levelProb_pos _).le (work_nonneg _ _))
      (weighted_work_tail d hd n hnlo.le hnhi)
    exact (hasSum_work_majorant d hd).summable
  have hs : Summable (fun l => levelProb l * workEnvelope l d) :=
    (summable_nat_add_iff (f := fun l => levelProb l * workEnvelope l d) (n+1)).1 hsTail
  refine ⟨hs, ?_⟩
  rw [← hs.sum_add_tsum_nat_add (n+1)]
  have ht : (∑' k, levelProb (k+(n+1)) * workEnvelope (k+(n+1)) d) ≤
      (1+Real.log 2+rLevel*Real.log 2/(1-rLevel))/d := by
    calc
      _ ≤ ∑' k : ℕ, ((1-rLevel)/d) * (rLevel^k * (1+((k:ℝ)+1)*Real.log 2)) :=
        Summable.tsum_le_tsum (weighted_work_tail d hd n hnlo.le hnhi) hsTail
          (hasSum_work_majorant d hd).summable
      _ = _ := (hasSum_work_majorant d hd).tsum_eq
  convert add_le_add hpre ht using 1 <;> ring

/-- Absolute convergence of the weighted stopping-work envelope. -/
theorem summable_weightedWorkEnvelope (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1/2) :
    Summable (fun l => levelProb l * (7 * workEnvelope l d)) := by
  convert (work_sum_bound d hd hdhalf).1.mul_left 7 using 1
  ext l
  ring

/-- The dyadic stopping-work envelope gives an expected-work constant below 31. -/
theorem tsum_weightedWorkEnvelope_lt (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1/2) :
    (∑' l, levelProb l * (7 * workEnvelope l d)) < 31/d := by
  have h0 := (work_sum_bound d hd hdhalf).1
  have h1 := (work_sum_bound d hd hdhalf).2
  calc
    _ = 7 * (∑' l, levelProb l * workEnvelope l d) := by
      rw [← h0.tsum_mul_left]
      congr 1
      ext l
      ring
    _ ≤ 7 * ((2+Real.log 2+rLevel*Real.log 2/(1-rLevel))/d) := by linarith
    _ = (7*(2+Real.log 2+rLevel*Real.log 2/(1-rLevel)))/d := by ring
    _ < 31/d := div_lt_div_of_pos_right Arithmetic.work_scalar_lt hd


/-- Transfer the explicit summable envelope to any nonnegative level second moments. -/
theorem secondMomentSeries_bound (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1/2)
    (e : ℕ → ℝ) (he0 : ∀ l, 0 ≤ e l)
    (he : ∀ l, e l ≤ min 1 (3/(cap l*d^2)^2)) :
    Summable (fun l => e l / levelProb l) ∧ (∑' l, e l / levelProb l) < 23/d := by
  have hle : ∀ l, e l / levelProb l ≤ secondMomentEnvelope l d := by
    intro l
    exact div_le_div_of_nonneg_right (he l) (levelProb_pos l).le
  have hs := Summable.of_nonneg_of_le (fun l => div_nonneg (he0 l) (levelProb_pos l).le)
    hle (summable_secondMomentEnvelope d hd)
  exact ⟨hs, lt_of_le_of_lt (Summable.tsum_le_tsum hle hs (summable_secondMomentEnvelope d hd))
    (tsum_secondMomentEnvelope_lt d hd hdhalf)⟩

/-- Transfer the explicit summable envelope to any nonnegative expected level work. -/
theorem workSeries_bound (d : ℝ) (hd : 0 < d) (hdhalf : d ≤ 1/2)
    (w : ℕ → ℝ) (hw0 : ∀ l, 0 ≤ w l) (hw : ∀ l, w l ≤ 7*workEnvelope l d) :
    Summable (fun l => levelProb l * w l) ∧ (∑' l, levelProb l * w l) < 31/d := by
  have hle : ∀ l, levelProb l * w l ≤ levelProb l * (7*workEnvelope l d) := by
    intro l
    exact mul_le_mul_of_nonneg_left (hw l) (levelProb_pos l).le
  have hs := Summable.of_nonneg_of_le (fun l => mul_nonneg (levelProb_pos l).le (hw0 l))
    hle (summable_weightedWorkEnvelope d hd hdhalf)
  exact ⟨hs, lt_of_le_of_lt (Summable.tsum_le_tsum hle hs
    (summable_weightedWorkEnvelope d hd hdhalf)) (tsum_weightedWorkEnvelope_lt d hd hdhalf)⟩

end ThresholdHC.Uniform713

#print axioms ThresholdHC.Uniform713.summable_secondMomentEnvelope
#print axioms ThresholdHC.Uniform713.tsum_secondMomentEnvelope_lt
#print axioms ThresholdHC.Uniform713.summable_weightedWorkEnvelope
#print axioms ThresholdHC.Uniform713.tsum_weightedWorkEnvelope_lt
#print axioms ThresholdHC.Uniform713.secondMomentSeries_bound
#print axioms ThresholdHC.Uniform713.workSeries_bound











