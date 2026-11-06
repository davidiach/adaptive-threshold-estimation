import ThresholdHC.EntropyTailQuantile.CostEntropy

/-! Entropy comparisons for learned gap laws. These finite transport lemmas
allow zero source rows and zero reference weights off the transported support.
They are deterministic components, not the arbitrary-law statistical theorem. -/

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.EntropyTailQuantile

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Cross entropy with a subprobability reference; positivity is needed only
where the cost is nonzero. In particular, unused source rows may have weight zero. -/
theorem costEntropy_le_supported_reference {a p : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hp : ∀ i, 0 ≤ p i)
    (hsupport : ∀ i, a i ≠ 0 → 0 < p i) (hpsum : (∑ i, p i) ≤ 1) :
    costEntropy a ≤ ∑ i, a i * (1 - log (p i)) := by
  rcases (costTotal_nonneg ha).eq_or_lt with hz | hA
  · have ha0 := eq_zero_of_costTotal_eq_zero ha hz.symm
    simp [ha0]
  have hi (i : ι) : a i * log (costTotal a / a i) + a i * log (p i) ≤
      costTotal a * p i - a i := by
    rcases (ha i).eq_or_lt with hz | hai
    · rw [← hz]
      simp only [zero_mul, add_zero, sub_zero]
      exact mul_nonneg hA.le (hp i)
    have hpi := hsupport i hai.ne'
    have hlog := log_le_sub_one_of_pos (div_pos (mul_pos hA hpi) hai)
    have hm := mul_le_mul_of_nonneg_left hlog hai.le
    have harg : costTotal a * p i / a i = (costTotal a / a i) * p i := by ring
    rw [harg, log_mul (div_pos hA hai).ne' hpi.ne'] at hm
    have hc : a i * (costTotal a / a i * p i) = costTotal a * p i := by
      field_simp
    nlinarith only [hm, hc]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hmass := mul_le_mul_of_nonneg_left hpsum hA.le
  rw [costEntropy_eq_log_sum ha]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  unfold costTotal at *
  nlinarith only [hs, hmass]

theorem costEntropy_eq_reference_sum {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    costEntropy a = ∑ i, a i * (1 - log (a i / costTotal a)) := by
  rw [costEntropy_eq_log_sum ha]
  have hi (i : ι) : log (costTotal a / a i) = -log (a i / costTotal a) := by
    rw [← inv_div, log_inv]
  simp only [hi, mul_neg, mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  unfold costTotal
  ring

/-- A transport can split each source row across many cells. Its extra entropy
is bounded by the cost-weighted coding length of the destination reference. -/
theorem costEntropy_transport_bound {a : ι → ℝ} {b : ι × κ → ℝ} {p : κ → ℝ}
    {L : ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ x, 0 ≤ b x)
    (hp : ∀ k, 0 < p k) (hpsum : (∑ k, p k) ≤ 1)
    (hrow : ∀ i, (∑ k, b (i,k)) ≤ a i)
    (hcode : ∀ i, (∑ k, b (i,k) * (-log (p k))) ≤ L * a i) :
    costEntropy b ≤ costEntropy a + L * costTotal a := by
  rcases (costTotal_nonneg ha).eq_or_lt with hz | hA
  · have ha0 := eq_zero_of_costTotal_eq_zero ha hz.symm
    have hb0 : b = fun _ => 0 := by
      funext x
      have hsingle := Finset.single_le_sum (fun k _ => hb (x.1,k))
        (Finset.mem_univ x.2)
      have hr := hrow x.1
      simp only [ha0] at hr
      exact le_antisymm (hsingle.trans hr) (hb x)
    simp [ha0,hb0]
  let ref : ι × κ → ℝ := fun x => a x.1 / costTotal a * p x.2
  have hmass : (∑ x, ref x) ≤ 1 := by
    simp only [ref,Fintype.sum_prod_type,← Finset.mul_sum,← Finset.sum_mul,
      ← Finset.sum_div]
    change costTotal a / costTotal a * (∑ k, p k) ≤ 1
    simpa only [div_self hA.ne',one_mul] using hpsum
  have hsupport (x : ι × κ) (hx : b x ≠ 0) : 0 < ref x := by
    have hbpos : 0 < b x := lt_of_le_of_ne (hb x) (Ne.symm hx)
    have hsingle := Finset.single_le_sum (fun k _ => hb (x.1,k))
      (Finset.mem_univ x.2)
    have hai : 0 < a x.1 := hbpos.trans_le (hsingle.trans (hrow x.1))
    exact mul_pos (div_pos hai hA) (hp x.2)
  have href := costEntropy_le_supported_reference hb
    (fun x => mul_nonneg (div_nonneg (ha x.1) hA.le) (hp x.2).le) hsupport hmass
  have hrows (i : ι) :
      (∑ k, b (i,k) * (1-log (ref (i,k)))) ≤
        a i * (1-log (a i/costTotal a)) + L*a i := by
    rcases (ha i).eq_or_lt with hz | hai
    · have hb0 (k : κ) : b (i,k) = 0 := by
        have hs := Finset.single_le_sum (fun l _ => hb (i,l)) (Finset.mem_univ k)
        exact le_antisymm (by linarith [hrow i]) (hb (i,k))
      simp [hb0,← hz]
    have hlog : log (a i/costTotal a) ≤ 0 :=
      log_nonpos (div_nonneg hai.le hA.le) ((div_le_one hA).2 (le_costTotal ha i))
    have hbase := mul_le_mul_of_nonneg_right (hrow i) (by linarith :
      0 ≤ 1-log (a i/costTotal a))
    have he (k : κ) : b (i,k) * (1-log (ref (i,k))) =
        b (i,k)*(1-log (a i/costTotal a)) + b (i,k)*(-log (p k)) := by
      dsimp [ref]
      rw [log_mul (div_pos hai hA).ne' (hp k).ne']
      ring
    simp only [he,Finset.sum_add_distrib,← Finset.sum_mul]
    exact add_le_add hbase (hcode i)
  calc
    costEntropy b ≤ ∑ x, b x * (1-log (ref x)) := href
    _ = ∑ i, ∑ k, b (i,k) * (1-log (ref (i,k))) := Fintype.sum_prod_type _
    _ ≤ ∑ i, (a i*(1-log (a i/costTotal a)) + L*a i) :=
      Finset.sum_le_sum fun i _ => hrows i
    _ = costEntropy a + L*costTotal a := by
      rw [Finset.sum_add_distrib,← costEntropy_eq_reference_sum ha,← Finset.mul_sum]
      rfl

omit [Fintype ι] in
theorem negMulLog_sum_le (s : Finset ι) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    negMulLog (∑ i ∈ s, a i) ≤ ∑ i ∈ s, negMulLog (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (negMulLog_add_le (ha i) (Finset.sum_nonneg fun j _ => ha j)).trans
      (add_le_add le_rfl ih)

/-- Recombining transported cells into their destination bands can only reduce entropy. -/
theorem costEntropy_merge {b : ι × κ → ℝ} (hb : ∀ x, 0 ≤ b x) :
    costEntropy (fun k => ∑ i, b (i,k)) ≤ costEntropy b := by
  have ht : costTotal (fun k => ∑ i, b (i,k)) = costTotal b := by
    unfold costTotal
    rw [Fintype.sum_prod_type,Finset.sum_comm]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    negMulLog_sum_le Finset.univ (fun i => hb (i,k)))
  have he : (∑ k, ∑ i, negMulLog (b (i,k))) = ∑ x, negMulLog (b x) := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
  rw [he] at hs
  unfold costEntropy
  rw [ht]
  linarith

/-- Dimension-free bound from cellwise inverse-square contraction and a
weighted reference-code bound. This is the finite transport used before
taking countable band limits. -/
theorem costEntropy_contracting_transport {a : ι → ℝ} {f b : ι × κ → ℝ}
    {p r : κ → ℝ} {L : ℝ} (ha : ∀ i, 0 ≤ a i)
    (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, 0 ≤ b x)
    (hrow : ∀ i, (∑ k, f (i,k)) ≤ a i)
    (hcost : ∀ x, b x ≤ r x.2 * f x) (hr : ∀ k, r k ≤ 1)
    (hp : ∀ k, 0 < p k) (hpsum : (∑ k, p k) ≤ 1)
    (hL : 0 ≤ L) (hcode : ∀ k, r k * (-log (p k)) ≤ L) :
    costEntropy b ≤ costEntropy a + L*costTotal a := by
  have hrows (i : ι) : (∑ k, b (i,k)) ≤ a i := by
    apply (Finset.sum_le_sum (fun k _ => (hcost (i,k)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hr k) (hf (i,k))))).trans
    exact hrow i
  have hcodes (i : ι) : (∑ k, b (i,k)*(-log (p k))) ≤ L*a i := by
    have hp1 (k : κ) : p k ≤ 1 :=
      (Finset.single_le_sum (fun j _ => (hp j).le) (Finset.mem_univ k)).trans hpsum
    calc
      _ ≤ ∑ k, L*f (i,k) := Finset.sum_le_sum fun k _ => by
        have hlog := neg_nonneg.mpr (log_nonpos (hp k).le (hp1 k))
        calc
          _ ≤ (r k*f (i,k))*(-log (p k)) :=
            mul_le_mul_of_nonneg_right (hcost (i,k)) hlog
          _ = (r k*(-log (p k)))*f (i,k) := by ring
          _ ≤ L*f (i,k) := mul_le_mul_of_nonneg_right (hcode k) (hf (i,k))
      _ = L*(∑ k, f (i,k)) := (Finset.mul_sum ..).symm
      _ ≤ L*a i := mul_le_mul_of_nonneg_left (hrow i) hL
  exact costEntropy_transport_bound ha hb hp hpsum hrows hcodes

/-- Entropy decreases under any deterministic merging of a finite cost vector. -/
theorem costEntropy_pushforward [DecidableEq κ] {b : ι → ℝ}
    (hb : ∀ i, 0 ≤ b i) (dest : ι → κ) :
    costEntropy (fun k => ∑ i, if dest i = k then b i else 0) ≤ costEntropy b := by
  classical
  have ht : costTotal (fun k => ∑ i, if dest i = k then b i else 0) = costTotal b := by
    unfold costTotal
    rw [Finset.sum_comm]
    simp
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset κ)) (fun k _ =>
    negMulLog_sum_le Finset.univ (a := fun i => if dest i = k then b i else 0) (fun i => by
      split_ifs
      · exact hb i
      · exact le_rfl))
  have he : (∑ k, ∑ i, negMulLog (if dest i = k then b i else 0)) =
      ∑ i, negMulLog (b i) := by
    rw [Finset.sum_comm]
    simp only [apply_ite,negMulLog_zero]
    simp
  rw [he] at hs
  unfold costEntropy
  rw [ht]
  linarith

end ThresholdHC.ArbitraryLawAdaptation
