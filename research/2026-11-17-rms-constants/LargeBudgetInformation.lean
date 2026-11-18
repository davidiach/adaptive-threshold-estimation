import SharpInformation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Sharp fair-reference entropy price for symmetric alternatives with squared
bias at most two thirds. -/
noncomputable section
namespace ThresholdHC.SharpRMS.LargeBudget
open Real Set

private theorem ratio_antitone (F G f g : ℝ → ℝ)
    (df : ∀ x ∈ Ico (0:ℝ) 1, HasDerivAt F (f x) x)
    (dg : ∀ x ∈ Ico (0:ℝ) 1, HasDerivAt G (g x) x)
    (zf : F 0 = 0) (zg : G 0 = 0) (posG : ∀ x ∈ Ioo (0:ℝ) 1, 0 < G x)
    (posg : ∀ x ∈ Ioo (0:ℝ) 1, 0 < g x) (mono : AntitoneOn (fun x => f x/g x) (Ioo (0:ℝ) 1)) :
    AntitoneOn (fun x => F x/G x) (Ioo (0:ℝ) 1) := by
  have slope (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : f x/g x ≤ F x/G x := by
    have sub (v : ℝ) (hv : v ∈ Icc 0 x) : v ∈ Ico (0:ℝ) 1 := ⟨hv.1,hv.2.trans_lt hx.2⟩
    obtain ⟨v,hv,eq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope F f hx.1
      (fun v hv => (df v (sub v hv)).continuousAt.continuousWithinAt)
      (fun v hv => df v (sub v ⟨hv.1.le,hv.2.le⟩)) G g
      (fun v hv => (dg v (sub v hv)).continuousAt.continuousWithinAt)
      (fun v hv => dg v (sub v ⟨hv.1.le,hv.2.le⟩))
    have vv : v ∈ Ioo (0:ℝ) 1 := ⟨hv.1,hv.2.trans hx.2⟩
    rw [zf,zg,sub_zero,sub_zero] at eq
    exact (mono vv hx hv.2.le).trans_eq ((div_eq_div_iff (posg v vv).ne' (posG x hx).ne').2 (by linarith only [eq]))
  have der (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) :=
    (df x ⟨hx.1.le,hx.2⟩).div (dg x ⟨hx.1.le,hx.2⟩) (posG x hx).ne'
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo (0:ℝ) 1)
    (fun x hx => (der x hx).continuousAt.continuousWithinAt)
    (fun x hx => (der x (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  have h := interior_subset hx
  exact div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr ((div_le_div_iff₀ (posg x h) (posG x h)).mp (slope x h))) (sq_nonneg _)

private def curvature (u y : ℝ) := u*(1+u*y)*(1-y)^2/(1-u*y)^2

private theorem curvature_antitone (u : ℝ) (hu : 0 ≤ u) (hc : u ≤ 2/3) :
    AntitoneOn (curvature u) (Ioo 0 1) := by
  have den (y : ℝ) (hy : y ∈ Ioo (0:ℝ) 1) : 0 < 1-u*y := by nlinarith [hy.2,mul_nonneg (show 0≤1-u by linarith) hy.1.le]
  have der (y : ℝ) (hy : y ∈ Ioo (0:ℝ) 1) : HasDerivAt (curvature u)
      (u*(1-y)*(u*(1-y)*(1-u*y)-2*(1-u)*(1+u*y))/(1-u*y)^3) y := by
    unfold curvature
    convert (((((hasDerivAt_id y).const_mul u).const_add 1).const_mul u).mul
      (((hasDerivAt_id y).const_sub 1).pow 2)).div
      ((((hasDerivAt_id y).const_mul u).const_sub 1).pow 2) (pow_ne_zero 2 (den y hy).ne') using 1
    · rfl
    dsimp
    field_simp [(den y hy).ne']
    ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo (0:ℝ) 1)
    (fun y hy => (der y hy).continuousAt.continuousWithinAt)
    (fun y hy => (der y (interior_subset hy)).hasDerivWithinAt)
  intro y hy
  have h : y ∈ Ioo (0:ℝ) 1 := interior_subset hy
  have l : u*(1-y)*(1-u*y) ≤ u := by
    apply (mul_le_mul_of_nonneg_left (show 1-u*y ≤ 1 by nlinarith [mul_nonneg hu h.1.le]) (mul_nonneg hu (by linarith [h.2]))).trans
    nlinarith [mul_nonneg hu h.1.le]
  have r : u ≤ 2*(1-u)*(1+u*y) := by
    nlinarith [mul_nonneg (show 0≤1-u by linarith) (mul_nonneg hu h.1.le)]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu (by linarith [h.2]))
    (sub_nonpos.mpr (l.trans r))) (pow_nonneg (den y h).le _)

private def odds (x : ℝ) := (log (1+x)-log (1-x))/2

private theorem odds_eq (x : ℝ) (hx : |x|<1) : odds x = artanh x := by
  obtain ⟨hl,hr⟩ := abs_lt.mp hx
  rw [artanh_eq_half_log ⟨hl.le,hr.le⟩,log_div (by linarith) (by linarith)]
  unfold odds
  ring

private theorem odds_deriv (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) : HasDerivAt odds (1/(1-x^2)) x := by
  have h := (((hasDerivAt_id x).const_add 1).log (by dsimp; linarith [hx.1])).sub
    (((hasDerivAt_id x).const_sub 1).log (by dsimp; linarith [hx.2]))
  convert h.div_const 2 using 1
  · rfl
  dsimp
  field_simp [show 1+x≠0 by linarith [hx.1],show 1-x≠0 by linarith [hx.2],
    show 1-x^2≠0 by nlinarith [mul_pos (show 0<1+x by linarith [hx.1]) (show 0<1-x by linarith [hx.2])]]
  ring

/-- The ratio of the symmetric log likelihood cost to the Wald statistic
decreases with the magnitude of the fair posterior. -/
theorem log_wald_ratio (u : ℝ) (hu : 0 ≤ u) (hc : u ≤ 2/3) :
    AntitoneOn (fun x => -log (1-u*x^2)/(x*artanh x)) (Ioo (0:ℝ) 1) := by
  let N := fun x : ℝ => -log (1-u*x^2)
  let D := fun x : ℝ => x*odds x
  let n := fun x : ℝ => 2*u*x/(1-u*x^2)
  let d := fun x : ℝ => odds x+x/(1-x^2)
  let n' := fun x : ℝ => 2*u*(1+u*x^2)/(1-u*x^2)^2
  let d' := fun x : ℝ => 2/(1-x^2)^2
  have xp (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) : 0 < 1-x^2 := by
    nlinarith [mul_pos (show 0<1-x by linarith [hx.2]) (show 0<1+x by linarith [hx.1])]
  have up (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) : 0 < 1-u*x^2 := by
    nlinarith [xp x hx,mul_nonneg (show 0≤1-u by linarith) (sq_nonneg x)]
  have a (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) : HasDerivAt N (n x) x := by
    convert (((((hasDerivAt_id x).pow 2).const_mul u).const_sub 1).log ((up x hx).ne')).neg using 1
    · rfl
    dsimp [n]; ring
  have b (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) : HasDerivAt D (d x) x := by
    convert (hasDerivAt_id x).mul (odds_deriv x hx) using 1
    · rfl
    dsimp [d]; ring
  have a' (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) : HasDerivAt n (n' x) x := by
    convert ((hasDerivAt_id x).const_mul (2*u)).div ((((hasDerivAt_id x).pow 2).const_mul u).const_sub 1) ((up x hx).ne') using 1
    · rfl
    dsimp [n']; ring
  have b' (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) : HasDerivAt d (d' x) x := by
    convert (odds_deriv x hx).add ((hasDerivAt_id x).div (((hasDerivAt_id x).pow 2).const_sub 1) (xp x hx).ne') using 1
    · rfl
    dsimp [d']; field_simp [(xp x hx).ne']; ring
  have dr (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : 0<d x := by
    dsimp [d]; rw [odds_eq _ (by simpa only [abs_of_pos hx.1] using hx.2)]
    exact add_pos (artanh_pos hx) (div_pos hx.1 (xp x ⟨hx.1.le,hx.2⟩))
  have ratio := ratio_antitone n d n' d' a' b' (by simp [n]) (by simp [d,odds]) dr
    (fun x hx => div_pos (by norm_num) (sq_pos_of_pos (xp x ⟨hx.1.le,hx.2⟩))) (by
      intro x hx y hy hxy
      have lower := curvature_antitone u hu hc
        (a:=x^2) (b:=y^2) (by exact ⟨sq_pos_of_pos hx.1,by linarith [xp x ⟨hx.1.le,hx.2⟩]⟩)
        (by exact ⟨sq_pos_of_pos hy.1,by linarith [xp y ⟨hy.1.le,hy.2⟩]⟩) (pow_le_pow_left₀ hx.1.le hxy 2)
      convert lower using 1 <;> dsimp [n',d',curvature] <;> field_simp [(xp x ⟨hx.1.le,hx.2⟩).ne',(up x ⟨hx.1.le,hx.2⟩).ne',(xp y ⟨hy.1.le,hy.2⟩).ne',(up y ⟨hy.1.le,hy.2⟩).ne'])
  have result := ratio_antitone N D n d a b (by simp [N]) (by simp [D]) (fun x hx => by
    dsimp [D]; rw [odds_eq _ (by simpa only [abs_of_pos hx.1] using hx.2)]; exact mul_pos hx.1 (artanh_pos hx)) dr ratio
  intro x hx y hy hxy
  simpa only [N,D,odds_eq x (by simpa only [abs_of_pos hx.1] using hx.2),odds_eq y (by simpa only [abs_of_pos hy.1] using hy.2)] using result hx hy hxy

end ThresholdHC.SharpRMS.LargeBudget
