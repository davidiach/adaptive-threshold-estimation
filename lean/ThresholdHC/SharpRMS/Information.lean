import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Scalar information prices in the three-bias argument. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open Real Set

private def halfLogOdds (x : ℝ) := (log (1+x) - log (1-x))/2

private theorem halfLog_eq (x : ℝ) (hx : |x| < 1) : halfLogOdds x = artanh x := by
  obtain ⟨hl,hr⟩ := abs_lt.mp hx
  rw [artanh_eq_half_log ⟨hl.le, hr.le⟩, Real.log_div (by linarith) (by linarith)]
  unfold halfLogOdds
  ring

private theorem halfLog_deriv (x : ℝ) (hx : |x| < 1) :
    HasDerivAt halfLogOdds (1/(1-x^2)) x := by
  obtain ⟨hl,hr⟩ := abs_lt.mp hx
  have h₁ := ((hasDerivAt_id x).const_add 1).log (by dsimp; linarith)
  have h₂ := ((hasDerivAt_id x).const_sub 1).log (by dsimp; linarith)
  convert (h₁.sub h₂).div_const 2 using 1
  · rfl
  · dsimp
    field_simp [show 1+x ≠ 0 by linarith, show 1-x ≠ 0 by linarith,
      show 1-x^2 ≠ 0 by nlinarith [mul_pos (show 0 < 1+x by linarith) (show 0 < 1-x by linarith)]]
    ring

private theorem increasing_from_zero (f f' : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hd : ∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Icc 0 b, 0 ≤ f' x) : f 0 ≤ f b := by
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 b)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hn x (interior_subset hx))
  exact hm ⟨le_rfl, hb⟩ ⟨hb, le_rfl⟩ hb

private theorem le_halfLog (z : ℝ) (hz : 0 ≤ z) (hz' : z < 1) : z ≤ halfLogOdds z := by
  have hd (x : ℝ) (hx : x ∈ Icc 0 z) :=
    (halfLog_deriv x (by rw [abs_of_nonneg hx.1]; exact hx.2.trans_lt hz')).sub (hasDerivAt_id x)
  have h := increasing_from_zero _ _ z hz hd (fun x hx => by
    have hden : 0 < 1-x^2 := by nlinarith [hx.1, hx.2, mul_pos (show 0 < 1-x by linarith [hx.2]) (show 0 < 1+x by linarith [hx.1])]
    rw [sub_nonneg, le_div_iff₀ hden]
    nlinarith [sq_nonneg x])
  simpa [halfLogOdds] using h

private theorem log_cost_nonneg (u z : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1/2)
    (hz : 0 ≤ z) (hz' : z < 1) :
    -log (1-u*z^2) ≤ u*z*halfLogOdds z := by
  let F := fun x => u*x*halfLogOdds x + log (1-u*x^2)
  have hden (x : ℝ) (hx : x ∈ Icc 0 z) : 0 < 1-x^2 := by
    nlinarith [mul_pos (show 0 < 1-x by linarith [hx.2]) (show 0 < 1+x by linarith [hx.1])]
  have uden (x : ℝ) (hx : x ∈ Icc 0 z) : 0 < 1-u*x^2 := by
    nlinarith [hden x hx, mul_nonneg (show 0 ≤ 1-u by linarith) (sq_nonneg x)]
  have hd (x : ℝ) (hx : x ∈ Icc 0 z) : HasDerivAt F
      ((u*halfLogOdds x + u*x*(1/(1-x^2))) + (-(u*(2*x)))/(1-u*x^2)) x := by
    have hx' : |x| < 1 := by rw [abs_of_nonneg hx.1]; exact hx.2.trans_lt hz'
    have h₁ := ((hasDerivAt_id x).const_mul u).mul (halfLog_deriv x hx')
    have h₂ := ((((hasDerivAt_id x).pow 2).const_mul u).const_sub 1).log (uden x hx).ne'
    convert h₁.add h₂ using 1
    · rfl
    · dsimp
      ring
  have h := increasing_from_zero _ _ z hz hd (fun x hx => by
    have hl := mul_le_mul_of_nonneg_left (le_halfLog x hx.1 (hx.2.trans_lt hz')) hu
    have h₀ := hden x hx
    have h₁ := uden x hx
    have aux : 0 ≤ u*x + u*x*(1/(1-x^2)) + -(u*(2*x))/(1-u*x^2) := by
      field_simp
      nlinarith only [mul_nonneg (mul_nonneg hu hx.1)
        (mul_nonneg (sq_nonneg x) (show 0 ≤ 1-2*u+u*x^2 by nlinarith [mul_nonneg hu (sq_nonneg x)]))]
    linarith)
  simp [F,halfLogOdds] at h ⊢
  linarith

/-- The paired log likelihood cost is paid by the observed posterior times
its log odds. The parameter u is the squared separation of the two biases. -/
theorem paired_log_cost (u z : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1/2) (hz : |z| < 1) :
    -log (1-u*z^2) ≤ u*z*artanh z := by
  rw [← halfLog_eq z hz]
  rcases le_total 0 z with h | h
  · exact log_cost_nonneg u z hu hu' h ((le_abs_self z).trans_lt hz)
  have h₁ := log_cost_nonneg u (-z) hu hu' (by linarith) (by linarith [(abs_lt.mp hz).1])
  have h₂ : halfLogOdds (-z) = -halfLogOdds z := by
    simp [halfLogOdds, sub_eq_add_neg]
    ring
  rw [h₂] at h₁
  convert h₁ using 1 <;> ring_nf

/-- Exact rational cap used after enforcing s² B = 4. -/
theorem small_bias_price (s : ℝ) (hs : 0 < s) (hs' : s ≤ 2/5) :
    2*(7/10:ℝ)^2*artanh s/s ≤ 3283/3150 := by
  have h (x : ℝ) (hx : x ∈ Icc 0 s) : 0 < 1-x^2 := by
    nlinarith [mul_pos (show 0 < 1-x by linarith [hx.2]) (show 0 < 1+x by linarith [hx.1])]
  let F := fun x : ℝ => x+x^3/(3*(1-x^2))-halfLogOdds x
  have hd (x : ℝ) (hx : x ∈ Icc 0 s) :
      HasDerivAt F (2*x^4/(3*(1-x^2)^2)) x := by
    have h₁ := (hasDerivAt_id x).pow 3
    have h₂ := ((((hasDerivAt_id x).pow 2).const_sub 1).const_mul 3)
    have h₃ := halfLog_deriv x (by rw [abs_of_nonneg hx.1]; linarith [hx.2])
    convert ((hasDerivAt_id x).add (h₁.div h₂ (by dsimp; nlinarith [h x hx]))).sub h₃ using 1
    · rfl
    · dsimp
      field_simp [ne_of_gt (h x hx)]
      ring
  have hF := increasing_from_zero _ _ s hs.le hd (fun x _ => by positivity)
  change _ ≤ s+s^3/(3*(1-s^2))-halfLogOdds s at hF
  have hzero : F 0 = 0 := by simp [F,halfLogOdds]
  rw [hzero, halfLog_eq s (by rw [abs_of_pos hs]; linarith)] at hF
  have hh : 0 < 1-s^2 := h s ⟨hs.le,le_rfl⟩
  have hcap : s+s^3/(3*(1-s^2)) ≤ (67/63)*s := by
    field_simp
    nlinarith [mul_nonneg (mul_nonneg hs.le (show 0 ≤ 2/5-s by linarith)) (show 0 ≤ 2/5+s by linarith)]
  rw [div_le_iff₀ hs]
  linarith

end ThresholdHC.SharpRMS
