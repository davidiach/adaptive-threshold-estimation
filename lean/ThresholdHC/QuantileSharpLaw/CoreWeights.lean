import ThresholdHC.OptimalQuantile.Endpoints
import ThresholdHC.QuantileSharpLaw.Coarsening

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

def coreWeight {n : ℕ} : Option (Fin n) → ℝ
  | none => 1
  | some j => (2 : ℝ)^j.val

def fullCoreCost (n : ℕ) (b : Option (Fin n) → ℝ) : ℝ := b none+dyadicCost n b

theorem coreWeight_ge_one {n : ℕ} (i : Option (Fin n)) : 1 ≤ coreWeight i := by
  cases i with
  | none => exact le_rfl
  | some j => exact one_le_pow₀ (by norm_num)

theorem fullCoreCost_eq_sum (n : ℕ) (b : Option (Fin n) → ℝ) :
    fullCoreCost n b = ∑ i, coreWeight i*b i := by
  rw [Fintype.sum_option]
  simp only [coreWeight,one_mul,fullCoreCost,dyadicCost]

theorem total_le_fullCoreCost {n : ℕ} {b : Option (Fin n) → ℝ} (hb : ∀ i, 0 ≤ b i) :
    costTotal b ≤ fullCoreCost n b := by
  rw [fullCoreCost_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (coreWeight_ge_one i) (hb i)

theorem core_exponential_mass : exp (-1)+exponentialTail 2 ≤ 1 := by
  have hg : Summable (fun n : ℕ => (exp (-2))^n) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
      exact exp_lt_one_iff.mpr (by norm_num))
  have hbound := Summable.tsum_le_tsum (fun n => exponential_term_bound (price := 2) le_rfl n)
    (exponentialTail_summable (price := 2) le_rfl) (hg.mul_left (exp (-1)))
  rw [tsum_mul_left,tsum_geometric_of_norm_lt_one] at hbound
  · have he1 : exp (-1 : ℝ) < 2/5 := by
      rw [exp_neg]
      have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 5/2)
        (show (5/2 : ℝ) < exp 1 by linarith [exp_one_gt_d9])
      norm_num at h ⊢
      exact h
    have he2 : exp (-2 : ℝ) < 1/5 := by
      rw [exp_neg]
      simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num) exp_two_gt_five
    have hd : 0 < 1-exp (-2 : ℝ) := by linarith
    have hquot : exp (-1 : ℝ)*(1-exp (-2))⁻¹ < 1/2 := by
      rw [← div_eq_mul_inv]
      apply (div_lt_iff₀ hd).mpr
      linarith
    change exponentialTail 2 ≤ _ at hbound
    linarith only [hbound,hquot,he1]
  · rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    exact exp_lt_one_iff.mpr (by norm_num)

theorem coreWeight_partition_bound (n : ℕ) :
    (∑ i : Option (Fin n), exp (1-2*coreWeight i)) ≤ 1 := by
  rw [Fintype.sum_option]
  simp only [coreWeight,mul_one]
  norm_num only
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => exp (1-2*(2 : ℝ)^j)) n]
  have hsum := (exponentialTail_summable (price := 2) le_rfl).sum_le_tsum
    (Finset.range n) (fun j _ => (exp_pos _).le)
  exact (add_le_add le_rfl hsum).trans core_exponential_mass

theorem costEntropy_le_twice_coreCost {n : ℕ} {b : Option (Fin n) → ℝ} (hb : ∀ i, 0 ≤ b i) :
    costEntropy b ≤ 2*fullCoreCost n b := by
  rw [fullCoreCost_eq_sum]
  exact (weighted_entropy_iff_partition (price := 2) (w := coreWeight)).mpr
    (coreWeight_partition_bound n) b hb

end ThresholdHC.QuantileSharpLaw
