import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Tactic

/-! The local randomization used in the critical-gap reduction. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open Real

private theorem tanh_monotone : Monotone Real.tanh := by
  intro x y h
  apply (artanh_le_artanh_iff ⟨neg_one_lt_tanh x,tanh_lt_one x⟩
    ⟨neg_one_lt_tanh y,tanh_lt_one y⟩).mp
  simpa only [artanh_tanh] using h

/-- Any nonzero net count has a fair posterior at least one flip bias away
from zero. This ensures that the fallback mean belongs to [-1,1]. -/
theorem posterior_lattice_gap (a : ℝ) (ha : 0 < a) (ha' : a < 1) (k : ℤ) (hk : k ≠ 0) :
    a ≤ |tanh ((k:ℝ)*artanh a)| := by
  have haI : a ∈ Set.Ioo (-1:ℝ) 1 := ⟨by linarith,ha'⟩
  have hh := artanh_nonneg ha.le
  rcases lt_or_gt_of_ne hk with h | h
  · have h₁ : (1:ℝ) ≤ -(k:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ -k by omega)
    have hl := tanh_monotone (show artanh a ≤ -(k:ℝ)*artanh a by nlinarith [mul_nonneg (sub_nonneg.mpr h₁) hh])
    rw [tanh_artanh haI,neg_mul,Real.tanh_neg] at hl
    exact hl.trans (neg_le_abs _)
  · have h₁ : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
    have hl := tanh_monotone (show artanh a ≤ (k:ℝ)*artanh a by nlinarith [mul_nonneg (sub_nonneg.mpr h₁) hh])
    rw [tanh_artanh haI] at hl
    exact hl.trans (le_abs_self _)

def copyProbability (f z : ℝ) := (1-z^2)/(1-f^2*z^2)

-- At zero the fallback has zero probability, so any mean in [-1,1] works.
def fallbackMean (a z : ℝ) := if z=0 then 0 else a/z

/-- Copy a source flip with probability c, otherwise generate an independent
bit of the indicated mean. The resulting conditional mean equals the Bayesian
prediction given the hidden source sign. This includes z=0 and z=±1. -/
theorem critical_step_kernel (a s z : ℝ) (hs : 0 < s) (hsa : s < a)
    (hz : |z| ≤ 1) (hlattice : z=0 ∨ a ≤ |z|) :
    let f := s/a
    let c := copyProbability f z
    0 ≤ c ∧ c ≤ 1 ∧ |fallbackMean a z| ≤ 1 ∧
      ∀ e : ℝ, (e = -1 ∨ e = 1) →
        c*(s*e)+(1-c)*fallbackMean a z = a*(z+f*e)/(1+f*z*e) := by
  let f := s/a
  have ha : 0 < a := hs.trans hsa
  have hf : 0 < f := div_pos hs ha
  have hf' : f < 1 := (div_lt_one ha).2 hsa
  have hsq : z^2 ≤ 1 := by nlinarith [sq_abs z, mul_nonneg (sub_nonneg.mpr hz) (show 0 ≤ 1+|z| by positivity)]
  have hf2 : f^2 < 1 := by nlinarith [mul_pos (sub_pos.mpr hf') (show 0 < 1+f by positivity)]
  have hden : 0 < 1-f^2*z^2 := by nlinarith [mul_nonneg (sq_nonneg f) (sub_nonneg.mpr hsq)]
  have hsmall : |f*z| < 1 := by
    rw [abs_mul,abs_of_pos hf]
    exact (mul_le_mul_of_nonneg_left hz hf.le).trans_lt (by simpa using hf')
  change 0 ≤ copyProbability f z ∧ copyProbability f z ≤ 1 ∧ _ ∧ _
  refine ⟨div_nonneg (sub_nonneg.mpr hsq) hden.le, (div_le_one hden).2 ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hf2.le) (sq_nonneg z)]
  · rcases hlattice with rfl | hl
    · simp [fallbackMean]
    · have hn : z ≠ 0 := by intro he; simp [he] at hl; linarith
      simp only [fallbackMean, hn, ↓reduceIte, abs_div, abs_of_pos ha]
      exact (div_le_one (abs_pos.mpr hn)).2 hl
  · intro e he
    have hfs : f*a=s := div_mul_cancel₀ _ ha.ne'
    change copyProbability f z*(s*e) + (1-copyProbability f z)*fallbackMean a z =
      a*(z+f*e)/(1+f*z*e)
    by_cases hz0 : z=0
    · subst z
      simp [copyProbability,fallbackMean]
      linarith only [congrArg (fun x : ℝ => x*e) hfs]
    have hd : 1+f*z*e ≠ 0 := by
      rcases he with rfl | rfl <;> linarith [(abs_lt.mp hsmall).1,(abs_lt.mp hsmall).2]
    simp only [fallbackMean,hz0,↓reduceIte,copyProbability]
    rw [← hfs]
    generalize hD : 1-f^2*z^2 = D at hden ⊢
    generalize hE : 1+f*z*e = E at hd ⊢
    field_simp [hz0,hden.ne',hd]
    rw [← hD, ← hE]
    rcases he with rfl | rfl <;> ring

end ThresholdHC.SharpRMS
