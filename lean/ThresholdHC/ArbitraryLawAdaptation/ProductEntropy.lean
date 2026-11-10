import ThresholdHC.ArbitraryLawAdaptation.CountableTransport

/-! Entropy of product-cost cells with a summable reference-code budget. -/

noncomputable section
open Real Filter
open scoped BigOperators ENNReal Topology
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.EntropyTailQuantile

theorem costEntropy_product_reference {ι κ : Type*} [Fintype ι] [Fintype κ]
    {a : ι → ℝ} {t p : κ → ℝ} (ha : ∀ i, 0 ≤ a i) (ht : ∀ k, 0 ≤ t k)
    (hp : ∀ k, 0 < p k) (hpsum : (∑ k, p k) ≤ 1) :
    costEntropy (fun x : ι × κ => a x.1*t x.2) ≤
      (∑ k, t k*(1-log (p k)))*costEntropy a := by
  rcases (costTotal_nonneg ha).eq_or_lt with hz | hA
  · have ha0 := eq_zero_of_costTotal_eq_zero ha hz.symm
    simp [ha0]
  let ref (x : ι × κ) := a x.1/costTotal a*p x.2
  have hmass : (∑ x, ref x) ≤ 1 := by
    simp only [ref, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div]
    change costTotal a/costTotal a*(∑ k, p k) ≤ 1
    simpa only [div_self hA.ne', one_mul] using hpsum
  have href := costEntropy_le_supported_reference
    (fun x : ι × κ => mul_nonneg (ha x.1) (ht x.2))
    (fun x : ι × κ => mul_nonneg (div_nonneg (ha x.1) hA.le) (hp x.2).le)
    (p := ref) (fun x hx => by
      have hai : 0 < a x.1 := lt_of_le_of_ne (ha x.1) (Ne.symm (left_ne_zero_of_mul hx))
      exact mul_pos (div_pos hai hA) (hp x.2)) hmass
  have he (i : ι) (k : κ) : a i*t k*(1-log (ref (i,k))) =
      t k*(a i*(1-log (a i/costTotal a)))+a i*(t k*(-log (p k))) := by
    by_cases hai : a i = 0
    · simp [hai]
    · dsimp [ref]
      rw [log_mul (div_ne_zero hai hA.ne') (hp k).ne']
      ring
  have hcode : 0 ≤ ∑ k, t k*(-log (p k)) := Finset.sum_nonneg fun k _ => by
    have hp1 := (Finset.single_le_sum (fun l _ => (hp l).le) (Finset.mem_univ k)).trans hpsum
    exact mul_nonneg (ht k) (neg_nonneg.mpr (log_nonpos (hp k).le hp1))
  calc
    _ ≤ ∑ x : ι × κ, a x.1*t x.2*(1-log (ref x)) := href
    _ = (∑ k, t k)*costEntropy a+costTotal a*(∑ k, t k*(-log (p k))) := by
      rw [Fintype.sum_prod_type]
      simp_rw [he, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      rw [← costEntropy_eq_reference_sum ha]
      rw [← Finset.sum_mul]
      rfl
    _ ≤ (∑ k, t k)*costEntropy a+costEntropy a*(∑ k, t k*(-log (p k))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (costTotal_le_costEntropy ha) hcode)
    _ = _ := by
      simp only [mul_sub, mul_one, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      ring

theorem countable_product_transport {a t p : ℕ → ℝ} {b : ℕ × ℕ → ℝ} {C : ℝ}
    (ha : ∀ i, 0 ≤ a i) (ht : ∀ k, 0 ≤ t k) (hb : ∀ x, 0 ≤ b x)
    (hp : ∀ k, 0 < p k) (hpsum : ∀ n, (∑ k : Fin n, p k.val) ≤ 1)
    (hcode : ∀ n, (∑ k : Fin n, t k.val*(1-log (p k.val))) ≤ C)
    (hC : 0 ≤ C) (hcost : ∀ x, b x ≤ a x.1*t x.2)
    (dest : ℕ × ℕ → ℕ)
    (hcol : ∀ j, Summable (fun x => if dest x = j then b x else 0)) :
    countableEntropy (fun j => ∑' x, if dest x = j then b x else 0) ≤
      ENNReal.ofReal C*countableEntropy a := by
  apply countableEntropy_limit_le (partialTransport_tendsto dest hcol)
  intro n
  apply iSup_le
  intro m
  have hmerge := costEntropy_finite_destination_prefix
    (fun x : Fin n × Fin n => hb (x.1.val,x.2.val))
    (fun x : Fin n × Fin n => dest (x.1.val,x.2.val)) m
  have hmono := costEntropy_mono (fun x : Fin n × Fin n => hb (x.1.val,x.2.val))
    (fun x : Fin n × Fin n => hcost (x.1.val,x.2.val))
  have hprod := costEntropy_product_reference (fun i : Fin n => ha i.val)
    (fun k : Fin n => ht k.val) (fun k : Fin n => hp k.val) (hpsum n)
  have hbound := hmerge.trans (hmono.trans (hprod.trans
    (mul_le_mul_of_nonneg_right (hcode n) (costEntropy_nonneg (fun i : Fin n => ha i.val)))))
  calc
    _ ≤ ENNReal.ofReal (C*costEntropy (fun i : Fin n => a i.val)) := ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal C*ENNReal.ofReal (costEntropy (fun i : Fin n => a i.val)) :=
      ENNReal.ofReal_mul hC
    _ ≤ _ := mul_le_mul_right (prefix_le_countableEntropy a n) _

end ThresholdHC.ArbitraryLawAdaptation
