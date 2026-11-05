import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace ThresholdHC.LawAdaptation

def spin (b : Bool) : ℝ := if b then 1 else -1

def bitMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

def wordMass (p : ℝ) {n : ℕ} (w : Fin n → Bool) : ℝ :=
  ∏ i, bitMass p (w i)

def parity {n : ℕ} (w : Fin n → Bool) : ℝ := ∏ i, spin (w i)

/-- The expected observable parity under a Bernoulli prefix. -/
theorem parity_mean (p : ℝ) (n : ℕ) :
    ∑ w : Fin n → Bool, wordMass p w * parity w = (2*p-1)^n := by
  simp only [wordMass, parity, ← Finset.prod_mul_distrib]
  have h := Finset.sum_pow' (Finset.univ : Finset Bool)
    (fun b => bitMass p b * spin b) n
  have hs : (∑ b : Bool, bitMass p b * spin b) = 2*p-1 := by
    simp [bitMass, spin]
    ring
  rw [hs] at h
  simpa only [Fintype.piFinset_univ] using h.symm

/-- Even parity removes the unknown sign, for every gap and prefix order. -/
theorem even_parity_mean (d : ℝ) (positive : Bool) (k : ℕ) :
    ∑ w : Fin (2*k) → Bool,
      wordMass (if positive then 1/2+d else 1/2-d) w * parity w = (2*d)^(2*k) := by
  rw [parity_mean]
  cases positive
  · simp only [Bool.false_eq_true, ite_false]
    rw [show 2*(1/2-d)-1 = -(2*d) by ring]
    exact Even.neg_pow (even_two_mul k) (2*d)
  · simp only [ite_true]
    congr 1
    ring

theorem mixed_even_parity (d q : ℝ) (k : ℕ) :
    q * (∑ w : Fin (2*k) → Bool, wordMass (1/2+d) w * parity w) +
      (1-q) * (∑ w : Fin (2*k) → Bool, wordMass (1/2-d) w * parity w) =
      (2*d)^(2*k) := by
  have hp := even_parity_mean d true k
  have hn := even_parity_mean d false k
  simp only [ite_true, Bool.false_eq_true, ite_false] at hp hn
  rw [hp, hn]
  ring

/-- The statistic is bounded on every possible observed word. -/
theorem parity_abs {n : ℕ} (w : Fin n → Bool) : |parity w| = 1 := by
  simp only [parity, Finset.abs_prod]
  have h (i : Fin n) : |spin (w i)| = 1 := by cases w i <;> norm_num [spin]
  simp_rw [h]
  simp

end ThresholdHC.LawAdaptation

