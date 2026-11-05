import ThresholdHC.ConfidenceTransfer.Hybrid

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.TypedConfidence
open ThresholdHC.CriticalEntropy ThresholdHC.ConfidenceTransfer

/-- The log likelihood ratio at a reference-positive leaf is additive over slots. -/
theorem factor_leaf_log {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (p q : I → ℝ) (hs : ∀ i, q i = 0 → p i = 0) :
    let ref := a * ∏ i, p i
    ref * Real.log (ref / (a * ∏ i, q i)) =
      ∑ i, ref * Real.log (ref / (a * ∏ j, if j=i then q j else p j)) := by
  dsimp only
  by_cases h : a * ∏ i, p i = 0
  · simp [h]
  obtain ⟨ha,hp⟩ := mul_ne_zero_iff.mp h
  have hp' (i : I) : p i ≠ 0 := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  have hq' (i : I) : q i ≠ 0 := mt (hs i) (hp' i)
  have hlog (v : I → ℝ) (hv : ∀ i, v i ≠ 0) :
      Real.log ((a * ∏ i, p i)/(a * ∏ i, v i)) = ∑ i, (Real.log (p i)-Real.log (v i)) := by
    have hv' : ∏ i, v i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hv i
    rw [Real.log_div h (mul_ne_zero ha hv'),Real.log_mul ha hp,Real.log_mul ha hv',
      Real.log_prod (fun i _ => hp' i),Real.log_prod (fun i _ => hv i), Finset.sum_sub_distrib]
    ring
  have hsingle (i : I) : Real.log ((a * ∏ j, p j)/(a * ∏ j, if j=i then q j else p j)) =
      Real.log (p i)-Real.log (q i) := by
    rw [hlog (fun j => if j=i then q j else p j) (fun j => by split <;> first | exact hq' _ | exact hp' _)]
    simp only [apply_ite Real.log]
    simp_rw [sub_ite,sub_self]
    simp
  rw [hlog q hq',Finset.mul_sum]
  simp_rw [hsingle]

/-- Switching all slots has KL equal to the sum for switching one slot at a time
while keeping all other slots at the same reference law. The common multiplier
may be zero on inconsistent transcripts. -/
theorem factorized_kl_sum {I Z : Type} [Fintype I] [DecidableEq I] [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (a : Z → ℝ) (p q : I → Z → ℝ) (P Q : Z → ℝ) (H : I → Z → ℝ)
    (hP : ∀ z, P z = a z*∏ i, p i z) (hQ : ∀ z, Q z = a z*∏ i, q i z)
    (hH : ∀ i z, H i z = a z*∏ j, if j=i then q j z else p j z)
    (hs : ∀ i z, q i z = 0 → p i z = 0)
    (pn : (∀ z, 0 ≤ P z) ∧ ∑ z, P z = 1) (qn : (∀ z, 0 ≤ Q z) ∧ ∑ z, Q z = 1)
    (hn : ∀ i, (∀ z, 0 ≤ H i z) ∧ ∑ z, H i z = 1) :
    klDiv (finiteWeightMeasure P) (finiteWeightMeasure Q) =
      ∑ i, klDiv (finiteWeightMeasure P) (finiteWeightMeasure (H i)) := by
  classical
  have supp (R : Z → ℝ) (r : I → Z → ℝ) (hr : ∀ z, R z = a z*∏ i, r i z)
      (hsr : ∀ i z, r i z = 0 → p i z = 0) : ∀ z, R z = 0 → P z = 0 := by
    intro z hz
    rw [hr] at hz
    rw [hP]
    rcases mul_eq_zero.mp hz with h|h
    · simp [h]
    obtain ⟨i,hi,hzero⟩ := Finset.prod_eq_zero_iff.mp h
    rw [Finset.prod_eq_zero hi (hsr i z hzero), mul_zero]
  have hqs := supp Q q hQ hs
  have hhs (i) := supp (H i) (fun j z => if j=i then q j z else p j z) (hH i)
    (fun j z => by split <;> first | exact hs j z | exact id)
  rw [finite_weight_kl P Q pn.1 qn.1 pn.2 qn.2 hqs]
  simp_rw [fun i => finite_weight_kl P (H i) pn.1 (hn i).1 pn.2 (hn i).2 (hhs i)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => finite_weight_gibbs P (H i)
    pn.1 (hn i).1 pn.2 (hn i).2 (hhs i)), Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  simp only [hP,hQ,hH]
  exact factor_leaf_log (a z) (fun i => p i z) (fun i => q i z) (fun i => hs i z)

end ThresholdHC.TypedConfidence
