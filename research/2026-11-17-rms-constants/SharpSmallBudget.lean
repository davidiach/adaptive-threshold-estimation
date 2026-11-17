import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! The uniform-prior Bayes risk at a leaf with h positive and l negative
revealed signs. This applies also when the two counts are unequal. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Set

def leafWeight (h l : ℕ) (p : ℝ) := p^h*(1-p)^l

private theorem weight_deriv (h l : ℕ) (p : ℝ) :
    HasDerivAt (fun x : ℝ => x^(h+1)*(1-x)^(l+1))
      (leafWeight h l p * ((h+1:ℝ) - (h+l+2:ℝ)*p)) p := by
  have hd := ((hasDerivAt_id p).pow (h+1)).mul (((hasDerivAt_id p).const_sub 1).pow (l+1))
  convert hd using 1
  · rfl
  · simp only [leafWeight, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, id_eq,
      Pi.pow_apply, pow_succ, mul_one]
    ring

/-- Exact squared error at a stopped binomial leaf, integrated over the
uniform prior on the positive-sign probability. -/
theorem leaf_bayes_identity (h l : ℕ) (x : ℝ) :
    let d := (h:ℝ)+l+2
    let c := ((h:ℝ)+1)/d
    (∫ p in (0:ℝ)..1, leafWeight h l p*(x-p)^2) =
      (∫ p in (0:ℝ)..1, leafWeight h l p*(x-c)^2) +
      (∫ p in (0:ℝ)..1, leafWeight h l p*(p*(1-p)/d)) := by
  let d := (h:ℝ)+l+2
  let c := ((h:ℝ)+1)/d
  have hd : 0 < d := by dsimp [d]; positivity
  have hc : d*c = (h:ℝ)+1 := by dsimp [c]; field_simp
  let F := fun p : ℝ => p^(h+1)*(1-p)^(l+1) * ((2*(x-c)+(c-p))/d)
  let D := fun p : ℝ => leafWeight h l p*(x-p)^2 -
    (leafWeight h l p*(x-c)^2 + leafWeight h l p*(p*(1-p)/d))
  have hF (p : ℝ) : HasDerivAt F (D p) p := by
    have hg := (((hasDerivAt_id p).const_sub c).const_add (2*(x-c))).div_const d
    convert (weight_deriv h l p).mul hg using 1
    · rfl
    · change D p = leafWeight h l p * (((h:ℝ)+1) - d*p) *
          ((2*(x-c)+(c-p))/d) + (p^(h+1)*(1-p)^(l+1))*(-1/d)
      rw [← hc]
      unfold D leafWeight
      field_simp
      simp only [pow_succ]
      ring
  have hD : Continuous D := by dsimp [D,leafWeight]; fun_prop
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
    (fun p _ => hF p) (hD.intervalIntegrable ..)
  have hzero : F 1-F 0 = 0 := by simp [F]
  rw [hzero] at hI
  let f := fun p : ℝ => leafWeight h l p*(x-p)^2
  let g := fun p : ℝ => leafWeight h l p*(x-c)^2
  let j := fun p : ℝ => leafWeight h l p*(p*(1-p)/d)
  have If : IntervalIntegrable f volume 0 1 := Continuous.intervalIntegrable (by dsimp [f,leafWeight]; fun_prop) ..
  have Ig : IntervalIntegrable g volume 0 1 := Continuous.intervalIntegrable (by dsimp [g,leafWeight]; fun_prop) ..
  have Ij : IntervalIntegrable j volume 0 1 := Continuous.intervalIntegrable (by dsimp [j,leafWeight]; fun_prop) ..
  change (∫ p in (0:ℝ)..1, f p - (g p + j p)) = 0 at hI
  have split := intervalIntegral.integral_sub If (Ig.add Ij)
  rw [split,intervalIntegral.integral_add Ig Ij, sub_eq_zero] at hI
  exact hI

theorem leaf_risk_work (h l : ℕ) (x : ℝ) :
    (∫ p in (0:ℝ)..1, leafWeight h l p*((10-(h+l:ℝ))/36*(p*(1-p)))) ≤
    ∫ p in (0:ℝ)..1, leafWeight h l p*(x-p)^2 := by
  rw [leaf_bayes_identity]
  have nonneg (p : ℝ) (hp : p ∈ Icc 0 1) : 0 ≤ leafWeight h l p := by
    unfold leafWeight
    exact mul_nonneg (pow_nonneg hp.1 _) (pow_nonneg (sub_nonneg.mpr hp.2) _)
  have h0 : 0 ≤ ∫ p in (0:ℝ)..1, leafWeight h l p*(x-((h:ℝ)+1)/(h+l+2:ℝ))^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun p hp => mul_nonneg (nonneg p hp) (sq_nonneg _))
  apply le_trans _ (le_add_of_nonneg_left h0)
  apply intervalIntegral.integral_mono_on (by norm_num)
      (Continuous.intervalIntegrable (by unfold leafWeight; fun_prop) ..)
      (Continuous.intervalIntegrable (by unfold leafWeight; fun_prop) ..)
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (nonneg p hp)
  rw [div_eq_mul_inv (p*(1-p))]
  rw [mul_comm (p*(1-p))]
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hp.1 (sub_nonneg.mpr hp.2))
  have hd : 0 < (h:ℝ)+l+2 := by positivity
  rw [← one_div, le_div_iff₀ hd]
  nlinarith [sq_nonneg ((h:ℝ)+l-4)]

end ThresholdHC.SharpRMS
