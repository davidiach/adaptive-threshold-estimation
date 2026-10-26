import ThresholdHC.Statements

namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory Set

theorem kl_hasDerivAt {x v : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hv : 0 < v) (hv1 : v < 1) :
    HasDerivAt (fun t => klB t v)
      (Real.log (x / v) - Real.log ((1 - x) / (1 - v))) x := by
  have hxn : x ≠ 0 := ne_of_gt hx
  have hxm : 1-x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hvn : v ≠ 0 := ne_of_gt hv
  have hvm : 1-v ≠ 0 := ne_of_gt (sub_pos.mpr hv1)
  have ha := ((hasDerivAt_id x).div_const v).log (div_ne_zero hxn hvn)
  have hb := (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).div_const
    (1-v)).log (div_ne_zero hxm hvm)
  convert ((hasDerivAt_id x).mul ha).add
    (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).mul hb) using 1
  · rfl
  · dsimp
    field_simp
    <;> ring

theorem kl_logdiff_hasDerivAt {x v : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hv : 0 < v) (hv1 : v < 1) :
    HasDerivAt (fun t => Real.log (t / v) - Real.log ((1-t)/(1-v)))
      (1 / (x * (1-x))) x := by
  have hxn : x ≠ 0 := ne_of_gt hx
  have hxm : 1-x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hvn : v ≠ 0 := ne_of_gt hv
  have hvm : 1-v ≠ 0 := ne_of_gt (sub_pos.mpr hv1)
  have ha := ((hasDerivAt_id x).div_const v).log (div_ne_zero hxn hvn)
  have hb := (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).div_const
    (1-v)).log (div_ne_zero hxm hvm)
  convert ha.sub hb using 1
  · rfl
  · dsimp
    field_simp
    <;> ring

theorem bern_variance_min {u v x : ℝ} (hx : x ∈ uIcc u v) :
    min (u * (1-u)) (v * (1-v)) ≤ x * (1-x) := by
  have hm1 := min_le_left (u * (1-u)) (v * (1-v))
  have hm2 := min_le_right (u * (1-u)) (v * (1-v))
  rcases le_total u v with huv | hvu
  · rw [uIcc_of_le huv] at hx
    by_cases hh : x ≤ 1/2
    · have hp : 0 ≤ (x-u)*(1-x-u) := mul_nonneg (sub_nonneg.mpr hx.1) (by linarith [hx.1])
      nlinarith
    · have hp : 0 ≤ (v-x)*(v+x-1) := mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.2])
      nlinarith
  · rw [uIcc_of_ge hvu] at hx
    by_cases hh : x ≤ 1/2
    · have hp : 0 ≤ (x-v)*(1-x-v) := mul_nonneg (sub_nonneg.mpr hx.1) (by linarith [hx.1])
      nlinarith
    · have hp : 0 ≤ (u-x)*(u+x-1) := mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.2])
      nlinarith

theorem kl_taylor_bound : ThresholdHC.Targets.kl_taylor_bound := by
  intro u v hu hu1 hv hv1
  let m := min (u*(1-u)) (v*(1-v))
  have hm : 0 < m := lt_min (mul_pos hu (sub_pos.mpr hu1)) (mul_pos hv (sub_pos.mpr hv1))
  let f := fun t : ℝ => (t-v)^2/(2*m) - klB t v
  let f' := fun t : ℝ => (t-v)/m - (Real.log (t/v)-Real.log ((1-t)/(1-v)))
  let f'' := fun t : ℝ => 1/m - 1/(t*(1-t))
  have hmem : ∀ x ∈ uIcc u v, 0 < x ∧ x < 1 := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_min hu hv) hx.1,
      lt_of_le_of_lt hx.2 (max_lt hu1 hv1)⟩
  have hd : ∀ x ∈ uIcc u v, HasDerivAt f (f' x) x := by
    intro x hx
    obtain ⟨hx0,hx1⟩ := hmem x hx
    convert ((((hasDerivAt_id x).sub_const v).pow 2).div_const (2*m)).sub
      (kl_hasDerivAt hx0 hx1 hv hv1) using 1
    · rfl
    · dsimp [f']
      field_simp
      <;> ring
  have hd' : ∀ x ∈ uIcc u v, HasDerivAt f' (f'' x) x := by
    intro x hx
    obtain ⟨hx0,hx1⟩ := hmem x hx
    convert (((hasDerivAt_id x).sub_const v).div_const m).sub
      (kl_logdiff_hasDerivAt hx0 hx1 hv hv1) using 1
    · rfl
  have hconv : ConvexOn ℝ (uIcc u v) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_uIcc u v)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => (hd' x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hm (bern_variance_min (interior_subset hx)))
  have hvf : f v = 0 := by
    simp [f, klB, ne_of_gt hv, ne_of_gt (sub_pos.mpr hv1)]
  have hvf' : f' v = 0 := by
    simp [f', ne_of_gt hv, ne_of_gt (sub_pos.mpr hv1)]
  have hdv : HasDerivAt f 0 v := by simpa [hvf'] using hd v right_mem_uIcc
  have hnonneg : 0 ≤ f u := by
    rcases lt_trichotomy v u with h | h | h
    · have hs := hconv.le_slope_of_hasDerivAt right_mem_uIcc left_mem_uIcc h hdv
      rw [slope_def_field, hvf] at hs
      have := (le_div_iff₀ (sub_pos.mpr h)).mp hs
      simpa using this
    · simpa [← h, hvf]
    · have hs := hconv.slope_le_of_hasDerivAt left_mem_uIcc right_mem_uIcc h hdv
      rw [slope_def_field, hvf] at hs
      have := (div_le_iff₀ (sub_pos.mpr h)).mp hs
      linarith
  exact sub_nonneg.mp hnonneg

/-- B2. -/
theorem lemmaA_forward : ThresholdHC.Targets.lemmaA_forward := by
  sorry

/-- B3. -/
theorem lemmaA_reverse : ThresholdHC.Targets.lemmaA_reverse := by
  sorry

/-- B4. -/
theorem lemmaA_sharp_at_one : ThresholdHC.Targets.lemmaA_sharp_at_one := by
  sorry

/-- B5. -/
theorem hardpair_step_kl : ThresholdHC.Targets.hardpair_step_kl := by
  sorry

end ThresholdHC.Proofs
