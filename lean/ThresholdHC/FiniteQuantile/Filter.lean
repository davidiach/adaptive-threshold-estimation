import ThresholdHC.EntropyTailLower.ComparableGroups
import ThresholdHC.EntropyTailQuantile.BandGeometry

/-! Filtering by endpoint and relative cost.
The estimate a(1+log(A/a))² ≤ 4A turns the omitted entropy into a
geometric sum of reciprocal dyadic endpoints. -/
noncomputable section
open Real Classical
open scoped BigOperators
namespace ThresholdHC.FiniteQuantile
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailLower

theorem relative_log_square {a A : ℝ} (ha : 0 < a) (hA : a ≤ A) :
    a * (1+log (A/a))^2 ≤ 4*A := by
  have hpos : 0 < A/a := div_pos (ha.trans_le hA) ha
  have hlo := log_nonneg ((one_le_div ha).mpr hA)
  have h := log_le_sub_one_of_pos (sqrt_pos.mpr hpos)
  rw [log_sqrt hpos.le] at h
  have hlog : 1+log (A/a) ≤ 2*sqrt (A/a) := by linarith
  have hsq := (sq_le_sq₀ (by linarith : 0 ≤ 1+log (A/a)) (by positivity)).mpr hlog
  rw [mul_pow, sq_sqrt hpos.le] at hsq
  have he : a*(4*(A/a)) = 4*A := by field_simp
  exact (mul_le_mul_of_nonneg_left hsq ha.le).trans_eq (by norm_num; exact he)

def discardedBand (a b : ℝ) (A lam : ℝ) : Prop :=
  0 < a ∧ 2*b < lam*(1+log (A/a))

theorem discarded_entropy {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    {t lam : ℝ} (ht : 0 < t) (hlam : 0 ≤ lam) (hcut : 32*lam ≤ t)
    (hbefore : ∀ j < n, t ≤ bandEdge j) :
    let A := costTotal a
    let bad := fun i : Fin n => discardedBand (a i) (bandEdge i.val) A lam
    costEntropy (fun i => if bad i then a i else 0) ≤ A/8 := by
  classical
  dsimp only
  let A := costTotal a
  let bad := fun i : Fin n => discardedBand (a i) (bandEdge i.val) A lam
  change costEntropy (fun i => if bad i then a i else 0) ≤ A/8
  rw [costEntropy_indicator_eq_subtype]
  by_cases hz : A = 0
  · have he := eq_zero_of_costTotal_eq_zero ha hz
    simp [he, hz]
  have hA : 0 < A := lt_of_le_of_ne (costTotal_nonneg ha) (Ne.symm hz)
  have hmass : (∑ i : {i // bad i}, a i.val) ≤ A :=
    costTotal_comp_injective_le a ha Subtype.val Subtype.val_injective
  have hsum : (∑ i : {i // bad i}, a i.val/A) ≤ 1 := by
    rw [← Finset.sum_div]
    exact (div_le_one hA).mpr hmass
  have href := costEntropy_le_reference (fun i : {i // bad i} => ha i.val)
    (fun i : {i // bad i} => div_pos i.property.1 hA) hsum
  have hterm (i : {i // bad i}) :
      a i.val*(1-log (a i.val/A)) ≤ (A/16)*(t/bandEdge i.val.val) := by
    let L := 1+log (A/a i.val)
    have hw : 0 < a i.val := i.property.1
    have hx := le_costTotal ha i.val
    have hL : 0 ≤ L := by
      dsimp [L]; linarith only [log_nonneg ((one_le_div hw).mpr hx)]
    have hbound := relative_log_square hw hx
    change a i.val*L^2 ≤ 4*A at hbound
    have hbad : 2*bandEdge i.val.val ≤ lam*L := i.property.2.le
    have hmul := mul_le_mul_of_nonneg_right hbad (mul_nonneg hw.le hL)
    have hprice := mul_le_mul_of_nonneg_left hbound hlam
    have hlimit := mul_le_mul_of_nonneg_left hcut hA.le
    have he : 1-log (a i.val/A) = L := by
      dsimp [L]; rw [log_div hw.ne' hA.ne', log_div hA.ne' hw.ne']; ring
    rw [he, ← mul_div_assoc]
    apply (le_div_iff₀ (bandEdge_pos _)).mpr
    nlinarith only [hmul, hprice, hlimit]
  have hgeom : (∑ i : Fin n, t/bandEdge i.val) ≤ 2 := by
    have h := dyadic_reference_sum_le_one ht.le hbefore
    have he (i : Fin n) : t/bandEdge i.val = 2*(t*2^i.val) := by
      simp [bandEdge, div_eq_mul_inv, ← inv_pow, pow_succ]; ring
    simp_rw [he]
    rw [← Finset.mul_sum]
    linarith only [h]
  have hsub : (∑ i : {i // bad i}, t/bandEdge i.val.val) ≤ 2 :=
    (costTotal_comp_injective_le (fun i : Fin n => t/bandEdge i.val)
      (fun i => div_nonneg ht.le (bandEdge_pos _).le) Subtype.val Subtype.val_injective).trans hgeom
  apply href.trans
  apply (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)).trans
  rw [← Finset.mul_sum]
  nlinarith only [mul_le_mul_of_nonneg_left hsub (div_nonneg hA.le (by norm_num : (0:ℝ) ≤ 16))]

end ThresholdHC.FiniteQuantile
