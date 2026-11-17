import ThresholdHC.SharpRMS.Transcript
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-! The information identity for the exact product likelihood of an adaptive
transcript. Impossible words with zero reference mass are allowed. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open Set Filter
open scoped Topology

def tiltedMass {W I : Type} [Fintype I] (p : W → ℝ) (z : W → I → ℝ) (t : ℝ) (w : W) :=
  p w * ∏ i, (1+t*z w i)

def tiltedScore {W I : Type} [Fintype I] (z : W → I → ℝ) (t : ℝ) (w : W) :=
  ∑ i, z w i/(1+t*z w i)

private theorem factors_pos {I : Type} (z : I → ℝ) (hz : ∀ i, |z i| ≤ 1) (t : ℝ)
    (ht : t ∈ Ioo (-1:ℝ) 1) (i : I) : 0 < 1+t*z i := by
  have hab : |t*z i| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hz i) (abs_nonneg t)).trans_lt (by simpa using abs_lt.mpr ht)
  linarith [(abs_lt.mp hab).1]

private theorem differentiate_product {I : Type} [DecidableEq I] (S : Finset I)
    (z : I → ℝ) (t : ℝ) (hn : ∀ i, 1+t*z i ≠ 0) :
    HasDerivAt (fun y => ∏ i ∈ S, (1+y*z i))
      ((∏ i ∈ S, (1+t*z i))*(∑ i ∈ S, z i/(1+t*z i))) t := by
  induction S using Finset.induction_on with
  | empty => simp [hasDerivAt_const]
  | insert i S hi ih =>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    have hd := (((hasDerivAt_id t).mul_const (z i)).const_add 1).mul ih
    convert hd using 1
    · rfl
    · dsimp
      field_simp [hn i]

theorem derivative_tiltedMass {W I : Type} [Fintype I] (p : W → ℝ) (z : W → I → ℝ)
    (hz : ∀ w i, |z w i| ≤ 1) (t : ℝ) (ht : t ∈ Ioo (-1:ℝ) 1) (w : W) :
    HasDerivAt (fun y => tiltedMass p z y w) (tiltedMass p z t w * tiltedScore z t w) t := by
  classical
  have hd := (differentiate_product Finset.univ (z w) t (fun i => (factors_pos _ (hz w) t ht i).ne')).const_mul (p w)
  convert hd using 1
  · rfl
  · unfold tiltedMass tiltedScore
    ring

private theorem score_derivative {W I : Type} [Fintype I] (z : W → I → ℝ)
    (hz : ∀ w i, |z w i| ≤ 1) (t : ℝ) (ht : t ∈ Ioo (-1:ℝ) 1) (w : W) :
    HasDerivAt (fun y => tiltedScore z y w) (∑ i, -(z w i)^2/(1+t*z w i)^2) t := by
  apply HasDerivAt.fun_sum
  intro i _
  have hd := (hasDerivAt_const t (z w i)).div (((hasDerivAt_id t).mul_const (z w i)).const_add 1)
    (factors_pos _ (hz w) t ht i).ne'
  convert hd using 1
  · rfl
  · dsimp
    ring

theorem centered_tiltedScore {W I : Type} [Fintype W] [Fintype I] (p : W → ℝ) (z : W → I → ℝ)
    (hz : ∀ w i, |z w i| ≤ 1) (mass : ∀ t ∈ Ioo (-1:ℝ) 1, ∑ w, tiltedMass p z t w = 1)
    (y : ℝ) (hy : y ∈ Ioo (-1:ℝ) 1) : ∑ w, tiltedMass p z y w*tiltedScore z y w = 0 := by
  have dt := HasDerivAt.fun_sum (u := Finset.univ) (fun w _ => derivative_tiltedMass p z hz y hy w)
  have fixed : (fun _ : ℝ => (1:ℝ)) =ᶠ[𝓝 y] (fun a => ∑ w, tiltedMass p z a w) := by
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with a ha
    exact (mass a ha).symm
  exact (dt.congr_of_eventuallyEq fixed).unique (hasDerivAt_const y 1)

/-- Differentiating the normalized product law twice cancels every
off-diagonal score term, including for adaptive interleavings. -/
theorem product_fisher {W I : Type} [Fintype W] [Fintype I] (p : W → ℝ) (z : W → I → ℝ)
    (hz : ∀ w i, |z w i| ≤ 1) (mass : ∀ t ∈ Ioo (-1:ℝ) 1, ∑ w, tiltedMass p z t w = 1)
    (t : ℝ) (ht : t ∈ Ioo (-1:ℝ) 1) :
    (∑ w, (tiltedMass p z t w*tiltedScore z t w)^2/tiltedMass p z t w) =
      ∑ w, tiltedMass p z t w * ∑ i, (z w i)^2/(1+t*z w i)^2 := by
  have tilt := derivative_tiltedMass p z hz
  have centered := centered_tiltedScore p z hz mass
  have dd := HasDerivAt.fun_sum (u := Finset.univ) (fun w _ => (tilt t ht w).mul
    (score_derivative z hz t ht w))
  have fixed : (fun _ : ℝ => (0:ℝ)) =ᶠ[𝓝 t]
      (fun a => ∑ w, tiltedMass p z a w*tiltedScore z a w) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with a ha
    exact (centered a ha).symm
  have dd0 := (dd.congr_of_eventuallyEq fixed).unique (hasDerivAt_const t 0)
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib, ← dd0]
  apply Finset.sum_congr rfl
  intro w _
  simp only [neg_div,Finset.sum_neg_distrib]
  by_cases hn : tiltedMass p z t w = 0
  · simp [hn]
  · have cancel (a b : ℝ) (ha : a ≠ 0) : (a*b)^2/a = a*b*b := by field_simp
    rw [cancel _ _ hn]
    ring

open Proofs Tier3 Tier5 in
/-- Exact diagonal Fisher information of a countably labelled, finite
adaptive transcript in its original likelihood coordinates. -/
theorem creation_score_identities {n : ℕ} (pol : List Bool → Option ℕ) (d : ℕ → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) (t : ℝ) (ht : t ∈ Ioo (-1:ℝ) 1) :
    let Q := fun (y : ℝ) (w : Prefix n) => creationLaw pol d (fun _ => (1+y)/2) w
    let z := fun (w : Prefix n) => posterior (capPolicy (coinCap n pol) pol) w (fun i => d i.val)
    (∑ w, Q t w * tiltedScore z t w = 0) ∧
    (∑ w, (deriv (fun y => Q y w) t)^2/Q t w) =
      ∑ w, Q t w * ∑ i, (z w i)^2/(1+t*z w i)^2 := by
  let Q := fun (y : ℝ) (w : Prefix n) => creationLaw pol d (fun _ => (1+y)/2) w
  let p := creationLaw (n := n) pol d (fun _ => 1/2)
  let z := fun (w : Prefix n) => posterior (capPolicy (coinCap n pol) pol) w (fun i => d i.val)
  have hz (w : Prefix n) (i : Fin (coinCap n pol)) : |z w i| ≤ 1 := by
    let a := coinLike (capPolicy (coinCap n pol) pol) w i (1/2+d i.val)
    let b := coinLike (capPolicy (coinCap n pol) pol) w i (1/2-d i.val)
    have ha : 0 ≤ a := coinLike_nonneg _ _ _ (by linarith [(hd i.val).1]) (by linarith [(hd i.val).2])
    have hb : 0 ≤ b := coinLike_nonneg _ _ _ (by linarith [(hd i.val).2]) (by linarith [(hd i.val).1])
    change |(a-b)/(a+b)| ≤ 1
    by_cases he : a+b=0
    · simp [he]
    · have hh : 0 < a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm he)
      rw [abs_div,abs_of_pos hh,div_le_one hh,abs_le]
      constructor <;> linarith
  have eqQ (y : ℝ) (w : Prefix n) : Q y w = tiltedMass p z y w := creation_tilt pol w d (fun _ => y) hd
  have htotal (y : ℝ) (hy : y ∈ Ioo (-1:ℝ) 1) : ∑ w, tiltedMass p z y w=1 := by
    simp_rw [← eqQ]
    exact (creationLaw_total n pol d _ hd (fun _ => ⟨by linarith [hy.1],by linarith [hy.2]⟩)).2
  change (∑ w, Q t w * tiltedScore z t w = 0) ∧ (∑ w, (deriv (fun y => Q y w) t)^2/Q t w) = ∑ w, Q t w * ∑ i, (z w i)^2/(1+t*z w i)^2
  simp_rw [eqQ, (derivative_tiltedMass p z hz t ht _).deriv]
  exact ⟨centered_tiltedScore p z hz htotal t ht, product_fisher p z hz htotal t ht⟩

end ThresholdHC.SharpRMS
