import ThresholdHC.Proofs.Algebra

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

theorem lemmaA_sharp_at_one : ThresholdHC.Targets.lemmaA_sharp_at_one := by
  intro d hd hd1
  let f : ℝ → ℝ := fun η => Real.log (1/2+2*d*η) - Real.log (1/2-2*d*η)
  have hplus : HasDerivAt (fun η : ℝ => 1/2+2*d*η) (2*d) 0 := by
    convert (hasDerivAt_const 0 (1/2 : ℝ)).add ((hasDerivAt_id 0).const_mul (2*d)) using 1
    · rfl
    · simp
  have hminus : HasDerivAt (fun η : ℝ => 1/2-2*d*η) (-2*d) 0 := by
    convert (hasDerivAt_const 0 (1/2 : ℝ)).sub ((hasDerivAt_id 0).const_mul (2*d)) using 1
    · rfl
    · simp
      <;> ring
  have hf : HasDerivAt f (8*d) 0 := by
    convert (hplus.log (by norm_num)).sub (hminus.log (by norm_num)) using 1
    <;> norm_num
    <;> ring
  have hs : Filter.Tendsto (fun η => f η / η) (nhdsWithin 0 (Ioi 0)) (nhds (8*d)) := by
    simpa [f, smul_eq_mul, div_eq_mul_inv, mul_comm] using hf.tendsto_slope_zero_right
  have he : Continuous (fun η : ℝ => (1-4*η^2)^2) := by fun_prop
  have het : Filter.Tendsto (fun η : ℝ => (1-4*η^2)^2)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa using (he.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds : nhdsWithin (0:ℝ) (Ioi 0) ≤ nhds 0)
  have hlim : Filter.Tendsto (fun η => ((1-4*η^2)^2 * (f η / η)) / (8*d))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa [ne_of_gt hd] using (het.mul hs).div_const (8*d)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0:ℝ)<1/4 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with η hη hsmall
  have hη0 : 0 < η := hη
  have hp : 0 < 1/2+2*d*η := by positivity
  have hq : 0 < 1/2-2*d*η := by nlinarith
  have hc : 0 < 1-4*η^2 := by nlinarith
  have hrp : rhoPlus η 1 = 1/2+η := by dsimp [rhoPlus]; ring_nf
  have hrm : rhoMinus η 1 = 1/2-η := by dsimp [rhoMinus]; ring_nf
  have hpp : pred d (rhoPlus η 1) = 1/2+2*d*η := by rw [hrp]; dsimp [pred]; ring
  have hpm : pred d (rhoMinus η 1) = 1/2-2*d*η := by rw [hrm]; dsimp [pred]; ring
  rw [hpp,hpm]
  have hk : klB (1/2+2*d*η) (1/2-2*d*η) = 4*d*η*f η := by
    dsimp [klB, f]
    have he1 : 1-(1/2+2*d*η) = 1/2-2*d*η := by ring
    have he2 : 1-(1/2-2*d*η) = 1/2+2*d*η := by ring
    rw [he1,he2, Real.log_div (ne_of_gt hp) (ne_of_gt hq),
      Real.log_div (ne_of_gt hq) (ne_of_gt hp)]
    ring
  rw [hk]
  field_simp
  <;> ring




theorem posterior_square_bounds (η L : ℝ) (hη : 0 ≤ η) (hη1 : η < 1/2)
    (hL : 0 < L) :
    (rhoPlus η L-rhoMinus η L)^2 ≤
      (16*η^2/(1-4*η^2)^2) * (rhoPlus η L*(1-rhoPlus η L)) ∧
    (rhoPlus η L-rhoMinus η L)^2 ≤
      (16*η^2/(1-4*η^2)^2) * (rhoMinus η L*(1-rhoMinus η L)) := by
  let a : ℝ := 1/2+η
  let b : ℝ := 1/2-η
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hA : 0 < b+a*L := by positivity
  have hB : 0 < a+b*L := by positivity
  have hc : 0 < 1-4*η^2 := by nlinarith
  obtain ⟨hm, hmp, hp1⟩ := posterior_mem η L hη hη1 hL
  have hp : 0 < rhoPlus η L := lt_of_lt_of_le hm hmp
  have hm1 : rhoMinus η L < 1 := lt_of_le_of_lt hmp hp1
  have hcp : 0 ≤ 4*η^2/(a*b) := by positivity
  constructor
  · have hid : (rhoPlus η L-rhoMinus η L)^2 =
        (4*η^2/(a*b)) * (L/(a+b*L)^2) * (rhoPlus η L*(1-rhoPlus η L)) := by
      change (a*L/(b+a*L)-b*L/(a+b*L))^2 =
        (4*η^2/(a*b)) * (L/(a+b*L)^2) * (a*L/(b+a*L)*(1-a*L/(b+a*L)))
      field_simp
      dsimp [a,b]
      ring
    rw [hid]
    calc
      _ ≤ (4*η^2/(a*b)) * (1/(4*b*a)) * (rhoPlus η L*(1-rhoPlus η L)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (ratio_bound b a L hb ha hL) hcp) (le_of_lt (mul_pos hp (sub_pos.mpr hp1)))
      _ = _ := by field_simp; dsimp [a,b]; ring
  · have hid : (rhoPlus η L-rhoMinus η L)^2 =
        (4*η^2/(a*b)) * (L/(b+a*L)^2) * (rhoMinus η L*(1-rhoMinus η L)) := by
      change (a*L/(b+a*L)-b*L/(a+b*L))^2 =
        (4*η^2/(a*b)) * (L/(b+a*L)^2) * (b*L/(a+b*L)*(1-b*L/(a+b*L)))
      field_simp
      dsimp [a,b]
      ring
    rw [hid]
    calc
      _ ≤ (4*η^2/(a*b)) * (1/(4*a*b)) * (rhoMinus η L*(1-rhoMinus η L)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (ratio_bound a b L ha hb hL) hcp) (le_of_lt (mul_pos hm (sub_pos.mpr hm1)))
      _ = _ := by field_simp; dsimp [a,b]; ring

theorem pred_mem_of_mem (d ρ : ℝ) (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) : 0 < pred d ρ ∧ pred d ρ < 1 := by
  have hmul := mul_pos hd hρ
  have hmul' := mul_pos hd (sub_pos.mpr hρ1)
  dsimp [pred]
  constructor <;> nlinarith

theorem predictive_square_bound (d η L : ℝ) (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hη : 0 ≤ η) (hη1 : η < 1/2) (hL : 0 < L) :
    (pred d (rhoPlus η L)-pred d (rhoMinus η L))^2 /
      (2*min (pred d (rhoPlus η L)*(1-pred d (rhoPlus η L)))
        (pred d (rhoMinus η L)*(1-pred d (rhoMinus η L)))) ≤
      32*d^2*η^2/(1-4*η^2)^2 := by
  obtain ⟨hm,hmp,hp1⟩ := posterior_mem η L hη hη1 hL
  have hp := lt_of_lt_of_le hm hmp
  have hm1 := lt_of_le_of_lt hmp hp1
  obtain ⟨hxp,hxp1⟩ := pred_mem_of_mem d (rhoPlus η L) hd hd1 hp hp1
  obtain ⟨hxm,hxm1⟩ := pred_mem_of_mem d (rhoMinus η L) hd hd1 hm hm1
  have hden : 0 < 2*min (pred d (rhoPlus η L)*(1-pred d (rhoPlus η L)))
      (pred d (rhoMinus η L)*(1-pred d (rhoMinus η L))) := by positivity
  obtain ⟨hbplus,hbminus⟩ := posterior_square_bounds η L hη hη1 hL
  have hc : 0 ≤ 16*η^2/(1-4*η^2)^2 := by positivity
  have hbp := le_trans hbplus (mul_le_mul_of_nonneg_left
    (pred_variance_ge d (rhoPlus η L) (le_of_lt hd) hd1) hc)
  have hbm := le_trans hbminus (mul_le_mul_of_nonneg_left
    (pred_variance_ge d (rhoMinus η L) (le_of_lt hd) hd1) hc)
  have hb : (rhoPlus η L-rhoMinus η L)^2 ≤
      (16*η^2/(1-4*η^2)^2) *
      min (pred d (rhoPlus η L)*(1-pred d (rhoPlus η L)))
        (pred d (rhoMinus η L)*(1-pred d (rhoMinus η L))) := by
    rcases le_total (pred d (rhoPlus η L)*(1-pred d (rhoPlus η L)))
      (pred d (rhoMinus η L)*(1-pred d (rhoMinus η L))) with hmin | hmin
    · rw [min_eq_left hmin]
      exact hbp
    · rw [min_eq_right hmin]
      exact hbm
  apply (div_le_iff₀ hden).2
  calc
    _ = (4*d^2)*(rhoPlus η L-rhoMinus η L)^2 := by dsimp [pred]; ring
    _ ≤ (4*d^2) * ((16*η^2/(1-4*η^2)^2) *
      min (pred d (rhoPlus η L)*(1-pred d (rhoPlus η L)))
        (pred d (rhoMinus η L)*(1-pred d (rhoMinus η L)))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem lemmaA_forward : ThresholdHC.Targets.lemmaA_forward := by
  intro d η L hd hd1 hη hη1 hL
  obtain ⟨hm,hmp,hp1⟩ := posterior_mem η L hη hη1 hL
  obtain ⟨hxp,hxp1⟩ := pred_mem_of_mem d (rhoPlus η L) hd hd1 (lt_of_lt_of_le hm hmp) hp1
  obtain ⟨hxm,hxm1⟩ := pred_mem_of_mem d (rhoMinus η L) hd hd1 hm (lt_of_le_of_lt hmp hp1)
  exact le_trans (kl_taylor_bound _ _ hxp hxp1 hxm hxm1)
    (predictive_square_bound d η L hd hd1 hη hη1 hL)

theorem lemmaA_reverse : ThresholdHC.Targets.lemmaA_reverse := by
  intro d η L hd hd1 hη hη1 hL
  obtain ⟨hm,hmp,hp1⟩ := posterior_mem η L hη hη1 hL
  obtain ⟨hxp,hxp1⟩ := pred_mem_of_mem d (rhoPlus η L) hd hd1 (lt_of_lt_of_le hm hmp) hp1
  obtain ⟨hxm,hxm1⟩ := pred_mem_of_mem d (rhoMinus η L) hd hd1 hm (lt_of_le_of_lt hmp hp1)
  have ht := kl_taylor_bound _ _ hxm hxm1 hxp hxp1
  have heq : (pred d (rhoMinus η L)-pred d (rhoPlus η L))^2 =
      (pred d (rhoPlus η L)-pred d (rhoMinus η L))^2 := by ring
  rw [min_comm, heq] at ht
  exact le_trans ht (predictive_square_bound d η L hd hd1 hη hη1 hL)

theorem hardpair_step_kl : ThresholdHC.Targets.hardpair_step_kl := by
  intro d h L hd hd1 hh hL
  let e := etaHard h d
  have he0 : 0 ≤ e := by
    dsimp [e, etaHard]
    exact mul_nonneg (by norm_num) (le_min (by norm_num) (le_of_lt (div_pos hh hd)))
  have he1 : e ≤ 1/8 := by
    dsimp [e, etaHard]
    nlinarith [min_le_left (1:ℝ) (h/d)]
  have heh : 8*d*e ≤ h := by
    have hmin := (le_div_iff₀ hd).mp (min_le_right (1:ℝ) (h/d))
    dsimp [e, etaHard]
    nlinarith
  have hc : 15/16 ≤ 1-4*e^2 := by nlinarith
  have hcpos : 0 < 1-4*e^2 := by linarith
  have hc2 : 225/256 ≤ (1-4*e^2)^2 := by nlinarith
  have hnum : 32*d^2*e^2 ≤ h^2/2 := by
    have hp : 0 ≤ (h-8*d*e)*(h+8*d*e) := mul_nonneg (by linarith) (by positivity)
    nlinarith
  have hb : 32*d^2*e^2/(1-4*e^2)^2 ≤ (128/225)*h^2 := by
    apply (div_le_iff₀ (pow_pos hcpos 2)).2
    calc
      _ ≤ h^2/2 := hnum
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc2 (sq_nonneg h)]
  exact le_trans (lemmaA_forward d e L hd hd1 he0 (by linarith) hL) hb

end ThresholdHC.Proofs
