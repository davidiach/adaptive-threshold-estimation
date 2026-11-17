import ThresholdHC.SharpRMS.PriceBounds
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Interpolate the bounded-work Fisher prices between grid biases directly
from the exit lengths. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open Real Set

private theorem add_tanh (u v : ℝ) :
    (tanh u+tanh v)/(1+tanh v*tanh u) = tanh (u+v) := by
  have den : 0 < 1+tanh v*tanh u := by
    have p : |tanh v*tanh u| < 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (abs_lt.mpr ⟨neg_one_lt_tanh u,tanh_lt_one u⟩).le
        (abs_nonneg _)).trans_lt (by simpa using abs_lt.mpr ⟨neg_one_lt_tanh v,tanh_lt_one v⟩)
    linarith [(abs_lt.mp p).1]
  apply (div_eq_iff den.ne').mpr
  rw [tanh_eq_sinh_div_cosh (u+v),sinh_add,cosh_add,
    tanh_eq_sinh_div_cosh u,tanh_eq_sinh_div_cosh v]
  have c := (cosh_pos (u+v)).ne'
  rw [cosh_add] at c
  field_simp [c,(cosh_pos u).ne',(cosh_pos v).ne']

private theorem posterior_as_tanh (s : ℝ) (hs : 0 < s) (hs' : s < 1) (k : ℕ) :
    barrierPosterior s k = tanh (k*artanh s) := by
  induction k with
  | zero => simp [barrierPosterior]
  | succ k ih =>
    rw [barrierPosterior,ih,Nat.cast_succ,add_mul,one_mul]
    conv_lhs => rw [← tanh_artanh (show s ∈ Ioo (-1:ℝ) 1 from ⟨by linarith,hs'⟩)]
    simp only [artanh_tanh]
    exact add_tanh _ _

private theorem scaled_sinh (u : ℝ) (hu : 0 ≤ u) (k : ℕ) : k*sinh u ≤ sinh (k*u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ,add_mul,one_mul,add_mul,one_mul,sinh_add]
    have hu' := sinh_nonneg_iff.mpr hu
    have hk := sinh_nonneg_iff.mpr (show 0 ≤ (k:ℝ)*u by positivity)
    nlinarith only [ih,mul_nonneg hk (sub_nonneg.mpr (one_le_cosh u)),
      mul_nonneg (sub_nonneg.mpr (one_le_cosh ((k:ℝ)*u))) hu']

private def cothValue (x : ℝ) := cosh x / sinh x

private theorem coth_derivative (x : ℝ) (hx : 0 < x) :
    HasDerivAt cothValue (-(1/sinh x^2)) x := by
  have h := (hasDerivAt_cosh x).div (hasDerivAt_sinh x) (sinh_pos_iff.mpr hx).ne'
  convert h using 1
  · rfl
  · rw [← neg_div]
    congr 1
    nlinarith only [cosh_sq_sub_sinh_sq x]

private theorem slope_mono (k : ℕ) (hk : 0 < k) :
    MonotoneOn (fun u : ℝ => (k:ℝ)*cothValue (k*u)-cothValue u) (Ioi 0) := by
  have kpos : (0:ℝ) < k := by exact_mod_cast hk
  let D := fun u : ℝ => 1/sinh u^2-(k:ℝ)^2/sinh (k*u)^2
  have df (u : ℝ) (hu : 0 < u) :
      HasDerivAt (fun x : ℝ => (k:ℝ)*cothValue (k*x)-cothValue x) (D u) u := by
    have h := ((coth_derivative (k*u) (mul_pos kpos hu)).comp u
      ((hasDerivAt_id u).const_mul (k:ℝ))).const_mul (k:ℝ)
    convert h.sub (coth_derivative u hu) using 1
    · rfl
    · dsimp [D]
      ring
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
    (fun u hu => (df u hu).continuousAt.continuousWithinAt)
    (fun u hu => (df u (interior_subset hu)).hasDerivWithinAt)
  intro u hu
  have pos : 0 < u := interior_subset hu
  have hu' := sinh_pos_iff.mpr pos
  have hk' := sinh_pos_iff.mpr (mul_pos kpos pos)
  have h := scaled_sinh u pos.le k
  change 0 ≤ 1/sinh u^2-(k:ℝ)^2/sinh (k*u)^2
  rw [sub_nonneg,div_le_div_iff₀ (sq_pos_of_pos hk') (sq_pos_of_pos hu')]
  nlinarith only [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ sinh (k*u)+(k:ℝ)*sinh u by positivity)]

/-- Increasing the flip bias decreases every exit-length denominator. -/
theorem exit_length_antitone_bias (s h t : ℝ) (hs : 0 < s) (sh : s ≤ h) (hh : h < 1)
    (ht : 0 ≤ t) (k : ℕ) (hk : 0 < k) : exitLength h t k ≤ exitLength s t k := by
  have a := slope_mono k hk (artanh_pos ⟨hs,sh.trans_lt hh⟩)
    (artanh_pos ⟨hs.trans_le sh,hh⟩) (artanh_le_artanh (by linarith) hh sh)
  have rep (x : ℝ) (hx : 0 < x) (h1 : x < 1) :
      (k:ℝ)/barrierPosterior x k-1/x = (k:ℝ)*cothValue (k*artanh x)-cothValue (artanh x) := by
    have id : ∀ y : ℝ, 1/tanh y = cothValue y := by
      intro y
      rw [tanh_eq_sinh_div_cosh]
      simp [cothValue]
    have hxI : x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,h1⟩
    rw [posterior_as_tanh x hx h1,← id,← id,tanh_artanh hxI]
    ring
  unfold exitLength
  rw [rep s hs (sh.trans_lt hh),rep h (hs.trans_le sh) hh]
  linarith only [mul_le_mul_of_nonneg_left a ht]

/-- A price certified at the upper endpoint h yields a valid price at every
smaller positive bias s after multiplying it by (s/h)^2. -/
theorem interpolate_exit_price (s h t P : ℝ) (hs : 0 < s) (sh : s ≤ h) (hh : h < 1)
    (ht : 0 ≤ t) (ht' : t < 1) (hP : 0 ≤ P) (ha : admissibleExitPrice h t P) :
    admissibleExitPrice s t ((s/h)^2*P) := by
  intro k hk
  let x := barrierPosterior s k
  let y := barrierPosterior h k
  have hpos := hs.trans_le sh
  have sx := barrier_posterior_bounds s hs (sh.trans_lt hh) k
  have hy := barrier_posterior_bounds h hpos hh k
  have xy : x ≤ y := by
    apply (artanh_le_artanh_iff (show x ∈ Ioo (-1:ℝ) 1 from ⟨by linarith [sx.1],sx.2.1⟩)
      (show y ∈ Ioo (-1:ℝ) 1 from ⟨by linarith [hy.1],hy.2.1⟩)).mp
    simp only [x,y,posterior_as_tanh s hs (sh.trans_lt hh),posterior_as_tanh h hpos hh,artanh_tanh]
    exact mul_le_mul_of_nonneg_left (artanh_le_artanh (by linarith) hh sh) (Nat.cast_nonneg _)
  have hd : exitLength h t k ≤ exitLength s t k := exit_length_antitone_bias s h t hs sh hh ht k hk
  have hy1 : y ≤ 1 := hy.2.1.le
  have ty : t*y ≤ 1 := (mul_le_mul_of_nonneg_left hy1 ht).trans (by simpa using ht'.le)
  have convex : 0 ≤ exitLength h t k := by
    have h1 := exit_length_mono h t hpos hh ht ht'.le 1 k (by decide) hk
    have one : exitLength h t 1 = 2 := by simp [exitLength,barrierPosterior]; ring
    linarith
  have R₁ : (1-t*y)*exitLength h t k ≤ (1-t*x)*exitLength s t k :=
    mul_le_mul_of_nonneg (by linarith only [mul_le_mul_of_nonneg_left xy ht]) hd (by linarith) (convex.trans hd)
  have ratio : s/(1+t*s) ≤ h/(1+t*h) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith only [sh]
  have numerator := mul_le_mul_of_nonneg ratio (add_le_add sh xy)
    (div_nonneg hs.le (by positivity)) (add_nonneg hpos.le hy.1)
  have A := ha k hk
  change P*(1+y/h) ≤ (1-t*y)*(1+t*h)*exitLength h t k at A
  have A' : P*(h/(1+t*h)*(h+y)) ≤ h^2*((1-t*y)*exitLength h t k) := by
    field_simp at A ⊢
    exact A
  have B := (mul_le_mul_of_nonneg_left numerator hP).trans (A'.trans (mul_le_mul_of_nonneg_left R₁ (sq_nonneg h)))
  change (s/h)^2*P*(1+x/s) ≤ (1-t*x)*(1+t*s)*exitLength s t k
  field_simp at B ⊢
  exact B

end ThresholdHC.SharpRMS
