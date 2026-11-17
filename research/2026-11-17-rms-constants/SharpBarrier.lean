import Mathlib.Tactic

/-! Pointwise reduction of the intermediate-budget information price to
positive and negative net counts. -/
noncomputable section
namespace ThresholdHC.SharpRMS

/-- Fair posterior after k excess positive flips at bias s. -/
def barrierPosterior (s : ℝ) : ℕ → ℝ
  | 0 => 0
  | k+1 => (barrierPosterior s k + s)/(1+s*barrierPosterior s k)

theorem barrier_posterior_bounds (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    ∀ k, 0 ≤ barrierPosterior s k ∧ barrierPosterior s k < 1 ∧
      barrierPosterior s k ≤ k*s ∧ (0 < k → s ≤ barrierPosterior s k) := by
  intro k
  induction k with
  | zero => simp [barrierPosterior]
  | succ k ih =>
    let x := barrierPosterior s k
    have hx : 0 ≤ x := ih.1
    have hx' : x < 1 := ih.2.1
    have hxk : x ≤ k*s := ih.2.2.1
    have hd : 0 < 1+s*x := by positivity
    change 0 ≤ (x+s)/(1+s*x) ∧ _ ∧ _ ∧ _
    refine ⟨div_nonneg (by linarith) hd.le, (div_lt_one hd).2 ?_, (div_le_iff₀ hd).2 ?_,
      fun _ => (le_div_iff₀ hd).2 ?_⟩
    · nlinarith [mul_pos (sub_pos.mpr hs') (sub_pos.mpr hx')]
    · push_cast
      nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ (k:ℝ)+1 by positivity) hs.le) (mul_nonneg hs.le hx)]
    · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hs'.le) (show 0 ≤ 1+s by positivity)) hx]

/-- The reciprocal price P is admissible at every negative exit. All
denominators have been cleared except k/x and 1/s. -/
def admissibleExitPrice (s t P : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    let x := barrierPosterior s k
    P*(1+x/s) ≤ (1-t*x)*(1+t*s)*((k:ℝ)+1-t*((k:ℝ)/x-1/s))

def barrierOffset (s t P : ℝ) := s+t-P*s/(1+t*s)

/-- A terminal leaf with signed excess count K and fair posterior z.
Multiplying by its biased transcript mass and summing leaves gives the
information/work inequality once the centered score and Wald identities
are applied. -/
theorem barrier_leaf_price (s t P : ℝ) (hs : 0 < s) (hs' : s < 1) (ht : 0 ≤ t)
    (ht' : t < 1) (hP' : P ≤ 1) (hexit : admissibleExitPrice s t P)
    (k : ℕ) (e : ℝ) (he : e = -1 ∨ e = 1) :
    let z := e*barrierPosterior s k
    P*z^2/(1+t*z)^2 ≤ (s*(e*k)*(z+t)-barrierOffset s t P*z)/(1+t*z) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [barrierPosterior]
  let x := barrierPosterior s k
  have hb := barrier_posterior_bounds s hs hs' k
  have xs : s ≤ x := hb.2.2.2 hk
  have hx : 0 < x := hs.trans_le xs
  have x1 : x < 1 := hb.2.1
  have kx : x ≤ k*s := hb.2.2.1
  have den : 0 < 1+t*s := by positivity
  change P*(e*x)^2/(1+t*(e*x))^2 ≤ (s*(e*k)*(e*x+t)-barrierOffset s t P*(e*x))/(1+t*(e*x))
  rcases he with rfl | rfl
  · have htx : t*x < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left x1.le ht) (by simpa using ht')
    have pos := sub_pos.mpr htx
    have h := hexit k hk
    change P*(1+x/s) ≤ (1-t*x)*(1+t*s)*((k:ℝ)+1-t*((k:ℝ)/x-1/s)) at h
    field_simp [hs.ne',hx.ne'] at h
    simp only [neg_one_mul,mul_neg,← sub_eq_add_neg]
    rw [div_le_div_iff₀ (sq_pos_of_pos pos) pos]
    unfold barrierOffset
    field_simp
    nlinarith only [mul_nonneg (sub_nonneg.mpr h) pos.le]
  · simp only [one_mul]
    have pos : 0 < 1+t*x := by positivity
    have prod : 1 ≤ (1+t*x)*(1+t*s) := by
      nlinarith [mul_nonneg ht (le_of_lt hx),mul_nonneg ht hs.le,mul_nonneg (mul_nonneg ht hx.le) (mul_nonneg ht hs.le)]
    have adj : P*x/(1+t*x)-P*s/(1+t*s) ≤ x-s := by
      field_simp
      nlinarith only [mul_nonneg (sub_nonneg.mpr xs) (show 0 ≤ (1+t*x)*(1+t*s)-P by linarith)]
    have coarse : P*x/(1+t*x)+barrierOffset s t P ≤ x+t := by
      unfold barrierOffset; linarith
    have h := mul_le_mul_of_nonneg_right coarse hx.le
    have h' := mul_le_mul_of_nonneg_left kx (add_nonneg hx.le ht)
    have hstep : (P*x/(1+t*x)+barrierOffset s t P)*x ≤ s*k*(x+t) := by linarith only [h,h']
    rw [div_le_div_iff₀ (sq_pos_of_pos pos) pos]
    field_simp at hstep
    nlinarith only [mul_nonneg (sub_nonneg.mpr hstep) pos.le]

end ThresholdHC.SharpRMS
