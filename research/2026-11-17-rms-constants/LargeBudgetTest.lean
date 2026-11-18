import SharpEntropy
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Rational three-bias test. The two stationary points of its exponential
minorant are rational by the choice of the tangent at y=399/1000. -/
noncomputable section
namespace ThresholdHC.SharpRMS.LargeBudget
open Real MeasureTheory Set
open scoped Topology

abbrev bias : ℝ := 29/40
abbrev intercept : ℝ := 1/8
abbrev weight : ℝ := 29/4
abbrev tilt : ℝ := 11774928000/2595112129
abbrev floorLog : ℝ := 27401/10000

def testValue (t x : ℝ) := intercept+weight*(x-t)^2
theorem testValue_pos (t x : ℝ) : 0 < testValue t x := by
  unfold testValue; positivity

private def G (y : ℝ) := (intercept+weight*bias^2+weight*y)^2-4*weight^2*bias^2*y
private def H (y : ℝ) := G y*exp (tilt*y)
private abbrev firstRoot : ℝ := 208394053/1177492800
private abbrev secondRoot : ℝ := 399/1000

private theorem H_deriv (y : ℝ) : HasDerivAt H
    (weight^2*tilt*(y-firstRoot)*(y-secondRoot)*exp (tilt*y)) y := by
  let C := intercept+weight*bias^2
  have poly := ((((hasDerivAt_id y).const_mul weight).const_add C).pow 2).sub
    ((hasDerivAt_id y).const_mul (4*weight^2*bias^2))
  convert poly.mul (((hasDerivAt_id y).const_mul tilt).exp) using 1
  · rfl
  dsimp [C]
  ring

private theorem exp_test_at (y : ℝ) (hy : 0≤y) (hg : 0 ≤ G y)
    (cert : 1549/100 ≤ G y * ∑ j ∈ Finset.range 13, (tilt*y)^j/(j.factorial:ℝ)) :
    1549/100 ≤ H y :=
  cert.trans (mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (mul_nonneg (by norm_num) hy) 13) hg)

private theorem H_bound (y : ℝ) (hy : y ∈ Icc (0:ℝ) 1) : 1549/100 ≤ H y := by
  obtain ⟨v,hv,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1))
    (show ContinuousOn H (Icc 0 1) from fun u _ => (H_deriv u).continuousAt.continuousWithinAt)
  apply le_trans _ (hmin hy)
  rcases eq_or_lt_of_le hv.1 with eq | pos
  · rw [←eq]; norm_num [H,G]
  rcases eq_or_lt_of_le hv.2 with eq | lt
  · rw [eq]
    apply exp_test_at <;> norm_num [G,Finset.sum_range_succ,Nat.factorial]
  have loc : IsLocalMin H v := hmin.isLocalMin (Icc_mem_nhds pos lt)
  have zero := loc.deriv_eq_zero
  rw [(H_deriv v).deriv] at zero
  have roots : v=firstRoot ∨ v=secondRoot := by
    rcases mul_eq_zero.mp zero with hz | hz
    · rcases mul_eq_zero.mp hz with hz | hz
      · rcases mul_eq_zero.mp hz with hz | hz
        · norm_num at hz
        · exact Or.inl (sub_eq_zero.mp hz)
      · exact Or.inr (sub_eq_zero.mp hz)
    · exact False.elim ((exp_pos _).ne' hz)
  rcases roots with rfl | rfl <;> apply exp_test_at <;> norm_num [G,Finset.sum_range_succ,Nat.factorial]

private theorem rational_log : floorLog ≤ log (1549/100:ℝ) := by
  let d := 4*log 2-floorLog
  have hd : (3248/100000:ℝ) ≤ d := by dsimp [d]; linarith [Real.log_two_gt_d9]
  have dp : 0≤d := by linarith
  have he := Real.sum_le_exp_of_nonneg dp 3
  norm_num [Finset.sum_range_succ,Nat.factorial] at he
  have bound : (16:ℝ) ≤ 1549/100*exp d := by
    nlinarith only [he,hd,mul_self_le_mul_self (by norm_num : (0:ℝ)≤3248/100000) hd]
  apply (le_log_iff_exp_le (by norm_num)).2
  calc
    exp floorLog = 16/exp d := by
      apply (eq_div_iff (exp_pos d).ne').2
      rw [←exp_add,show floorLog+d=((4:ℕ):ℝ)*log 2 by dsimp [d]; ring,exp_nat_mul,exp_log (by norm_num)]
      norm_num
    _ ≤ _ := (div_le_iff₀ (exp_pos d)).2 bound

theorem log_tests (x : ℝ) (hx : |x| ≤ 1) :
    floorLog ≤ log (testValue bias x)+log (testValue (-bias) x)+tilt*x^2 := by
  have product : G (x^2) = testValue bias x*testValue (-bias) x := by unfold G testValue; ring
  have h := rational_log.trans (Real.log_le_log (by norm_num) (H_bound (x^2)
    ⟨sq_nonneg _,by nlinarith [sq_abs x,pow_le_pow_left₀ (abs_nonneg x) hx 2]⟩))
  rw [H,product,log_mul (mul_pos (testValue_pos _ _) (testValue_pos _ _)).ne' (exp_pos _).ne',
    log_mul (testValue_pos _ _).ne' (testValue_pos _ _).ne',log_exp] at h
  exact h

end ThresholdHC.SharpRMS.LargeBudget
