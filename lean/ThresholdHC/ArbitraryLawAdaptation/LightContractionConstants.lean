import ThresholdHC.ArbitraryLawAdaptation.ProductEntropy
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A reference code and explicit numerical budgets for the light multiplier.
Each multiplier band can split into two destination bands. -/

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.ArbitraryLawAdaptation

def lightCostBound (n : ℕ) : ℝ := if n = 0 then 256 else 3*(1/64 : ℝ)^n

def lightReference (n : ℕ) : ℝ := if n = 0 then 7/16 else (1/2 : ℝ)^(n+4)

theorem lightCostBound_nonneg (n : ℕ) : 0 ≤ lightCostBound n := by
  unfold lightCostBound; split_ifs <;> positivity

theorem lightReference_pos (n : ℕ) : 0 < lightReference n := by
  unfold lightReference; split_ifs <;> positivity

theorem lightReference_le_one (n : ℕ) : lightReference n ≤ 1 := by
  unfold lightReference
  split_ifs
  · norm_num
  · exact pow_le_one₀ (by norm_num) (by norm_num)

theorem light_exponential_cost (n : ℕ) :
    (4 : ℝ)^(n+4)*(2*exp (-((4 : ℝ)^(n+2)/2))) ≤ 3*(1/64 : ℝ)^n := by
  have he := pow_div_factorial_le_exp (4^(n+2)/2) (by positivity : (0 : ℝ) ≤ 4^(n+2)/2) 4
  norm_num [Nat.factorial] at he
  have hpos : (0 : ℝ) < 4^n := by positivity
  have hp : (1/64 : ℝ)^n = ((4 : ℝ)^n)⁻¹^3 := by
    rw [← inv_pow, ← pow_mul, Nat.mul_comm n 3, pow_mul]
    norm_num
  rw [exp_neg, hp]
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 3*((4 : ℝ)^n)⁻¹^3)
  rw [← div_eq_mul_inv, ← mul_div_assoc, div_le_iff₀ (exp_pos _)]
  convert hm using 1
  simp only [pow_add, div_pow]
  field_simp
  ring

theorem lightReference_code_zero : 256*(1-log (lightReference 0)) ≤ 485 := by
  have hlog : log 2 ≤ (3/4 : ℝ) := by linarith [log_two_lt_d9]
  have hr := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8/7)
  have he : -log (7/16 : ℝ) = log (8/7 : ℝ)+log 2 := by
    rw [← log_mul (by norm_num : (8/7 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num [log_div]
  norm_num only [lightReference, ite_true]
  linarith

theorem lightReference_code_succ (n : ℕ) :
    lightCostBound (n+1)*(1-log (lightReference (n+1))) ≤ 9*(1/32 : ℝ)^(n+1) := by
  have hlog : log 2 ≤ 1 := by linarith [log_two_lt_d9]
  have hlin (m : ℕ) : (m : ℝ)+6 ≤ 6*(2 : ℝ)^m := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [pow_succ]
      push_cast
      have hp : 1 ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
      linarith
  have he : 1-log ((1/2 : ℝ)^(n+1+4)) ≤ 3*(2 : ℝ)^(n+1) := by
    have hhalf : log (1/2 : ℝ) = -log 2 := by norm_num [log_div]
    rw [log_pow, hhalf]
    push_cast
    have hm := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ ((n+1+4 : ℕ) : ℝ))
    push_cast at hm
    rw [pow_succ]
    linarith [hlin n]
  simp only [lightCostBound, lightReference, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
  calc
    _ ≤ 3*(1/64 : ℝ)^(n+1)*(3*(2 : ℝ)^(n+1)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [mul_mul_mul_comm, ← mul_pow]; norm_num

theorem lightReference_prefix (n : ℕ) : (∑ k : Fin n, lightReference k.val) ≤ 1/2 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, lightReference, ite_true, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ite_false]
    have he : (∑ k : Fin n, (1/2 : ℝ)^(k.val+1+4)) =
        (1/16 : ℝ)*(1-(1/2 : ℝ)^n) := by
      simp_rw [pow_add _ (Nat.add _ 1) 4]
      rw [← Finset.sum_mul, half_power_sum]
      norm_num
      ring
    rw [he]
    have hp : 0 ≤ (1/2 : ℝ)^n := by positivity
    linarith

theorem lightCostBound_prefix (n : ℕ) : (∑ k : Fin n, lightCostBound k.val) ≤ 257 := by
  have hg (m : ℕ) : (∑ k : Fin m, (1/64 : ℝ)^(k.val+1)) ≤ 1/63 := by
    have he (l : ℕ) : (∑ k : Fin l, (1/64 : ℝ)^(k.val+1)) =
        (1/63 : ℝ)*(1-(1/64 : ℝ)^l) := by
      induction l with
      | zero => simp
      | succ l ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih, pow_succ]
        ring
    rw [he]
    have hp : 0 ≤ (1/64 : ℝ)^m := by positivity
    linarith
  cases n with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, lightCostBound, ite_true, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ite_false, ← Finset.mul_sum]
    linarith [hg n]

theorem lightReference_code_prefix (n : ℕ) :
    (∑ k : Fin n, lightCostBound k.val*(1-log (lightReference k.val))) ≤ 486 := by
  have hg (m : ℕ) : (∑ k : Fin m, (1/32 : ℝ)^(k.val+1)) ≤ 1/31 := by
    have he (l : ℕ) : (∑ k : Fin l, (1/32 : ℝ)^(k.val+1)) =
        (1/31 : ℝ)*(1-(1/32 : ℝ)^l) := by
      induction l with
      | zero => simp
      | succ l ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih, pow_succ]
        ring
    rw [he]
    have hp : 0 ≤ (1/32 : ℝ)^m := by positivity
    linarith
  cases n with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
      (fun k _ => lightReference_code_succ k.val)
    rw [← Finset.mul_sum] at hs
    have hz : lightCostBound 0 = 256 := by norm_num [lightCostBound]
    rw [hz]
    linarith [hg n, lightReference_code_zero]

theorem duplicate_prefix (f : ℕ → ℝ) (n : ℕ) :
    (∑ k : Fin (2*n), f (k.val/2)) = 2*∑ k : Fin n, f k.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have he : (2*n+1)/2 = n := by omega
    have he' : (2*n)/2 = n := by omega
    rw [he, he']
    ring

theorem duplicate_prefix_le {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (n : ℕ) :
    (∑ k : Fin n, f (k.val/2)) ≤ 2*∑ k : Fin n, f k.val := by
  rw [← duplicate_prefix]
  have h : (∑ k ∈ Finset.range n, f (k/2)) ≤ ∑ k ∈ Finset.range (2*n), f (k/2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun k _ _ => hf (k/2))
  simpa only [Finset.sum_range] using h

theorem lightReference_duplicate_prefix (n : ℕ) :
    (∑ k : Fin n, lightReference (k.val/2)) ≤ 1 := by
  have h := duplicate_prefix_le (fun k => (lightReference_pos k).le) n
  linarith [lightReference_prefix n]

theorem lightReference_duplicate_code_prefix (n : ℕ) :
    (∑ k : Fin n, lightCostBound (k.val/2)*(1-log (lightReference (k.val/2)))) ≤ 1024 := by
  have h := duplicate_prefix_le (f := fun k => lightCostBound k*(1-log (lightReference k)))
    (fun k => mul_nonneg (lightCostBound_nonneg k) (by
      have hl := log_nonpos (lightReference_pos k).le (lightReference_le_one k)
      linarith)) n
  linarith [lightReference_code_prefix n]

end ThresholdHC.ArbitraryLawAdaptation
