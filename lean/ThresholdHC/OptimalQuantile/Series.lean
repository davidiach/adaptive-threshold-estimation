import ThresholdHC.OptimalQuantile.PriceGeometry
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.OptimalQuantile

def exponentialTail (price : ℝ) : ℝ := ∑' j : ℕ, exp (1-price*(2 : ℝ)^j)

def partitionSeries (k u : ℝ) : ℝ :=
  exp (1-dualPrice k u/(2*u))+exponentialTail (dualPrice k u)

theorem power_two_lower (n : ℕ) : (n : ℝ)+1 ≤ (2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ,Nat.cast_succ]
    nlinarith only [ih,Nat.cast_nonneg (α := ℝ) n]

theorem exponential_term_bound {price : ℝ} (hp : 2 ≤ price) (n : ℕ) :
    exp (1-price*(2 : ℝ)^n) ≤ exp (-1)*(exp (-2))^n := by
  calc
    _ ≤ exp (-1+(n : ℝ)*(-2)) := by
      apply exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hp (show 0 ≤ (2 : ℝ)^n by positivity)
      nlinarith only [h,power_two_lower n]
    _ = _ := by rw [exp_add,exp_nat_mul]

theorem exponentialTail_summable {price : ℝ} (hp : 2 ≤ price) :
    Summable (fun n : ℕ => exp (1-price*(2 : ℝ)^n)) := by
  have hg : Summable (fun n : ℕ => (exp (-2))^n) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
      exact exp_lt_one_iff.mpr (by norm_num))
  exact Summable.of_nonneg_of_le (fun n => (exp_pos _).le)
    (fun n => exponential_term_bound hp n) (hg.mul_left (exp (-1)))

end ThresholdHC.OptimalQuantile
