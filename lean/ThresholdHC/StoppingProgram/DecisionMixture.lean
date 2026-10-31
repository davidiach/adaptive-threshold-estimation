import Mathlib

/-! A finite independent Bernoulli decision seed as nonnegative weights
on deterministic policies. Zero-probability policies are retained harmlessly. -/

noncomputable section
open scoped BigOperators

namespace ThresholdHC.StoppingProgram
variable {I : Type*} [Fintype I]

def decisionFactor (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

def decisionWeight (p : I → ℝ) (b : I → Bool) : ℝ := ∏ i, decisionFactor (p i) (b i)

theorem decisionFactor_nonneg {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (b : Bool) : 0 ≤ decisionFactor p b := by
  cases b <;> simp only [decisionFactor,Bool.false_eq_true,ite_false,ite_true] <;> linarith [hp.1,hp.2]

theorem decisionFactor_sum (p : ℝ) : ∑ b : Bool, decisionFactor p b = 1 := by
  simp [decisionFactor]

theorem decisionWeight_nonneg (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (b : I → Bool) :
    0 ≤ decisionWeight p b := Finset.prod_nonneg (fun i _ => decisionFactor_nonneg (hp i) _)

variable [DecidableEq I]

theorem decisionWeight_sum (p : I → ℝ) : ∑ b : I → Bool, decisionWeight p b = 1 := by
  simp only [decisionWeight]
  rw [← Fintype.prod_sum]
  simp only [decisionFactor_sum,Finset.prod_const_one]

theorem decisionWeight_product (p : I → ℝ) (g : I → Bool → ℝ) :
    (∑ b : I → Bool, decisionWeight p b*(∏ i, g i (b i))) =
      ∏ i, ((1-p i)*g i false+p i*g i true) := by
  simp only [decisionWeight,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => decisionFactor (p i) b*g i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp [decisionFactor,add_comm]

theorem decisionWeight_single (p : I → ℝ) (i : I) (g : Bool → ℝ) :
    (∑ b : I → Bool, decisionWeight p b*g (b i)) = (1-p i)*g false+p i*g true := by
  classical
  have h := decisionWeight_product p (fun j b => if j = i then g b else 1)
  simpa only [Finset.prod_ite_eq',Finset.mem_univ,ite_true,mul_one,sub_add_cancel,
    ite_mul,mul_ite,ite_add_ite] using h

theorem decisionWeight_match (p : I → ℝ) (S : Finset I) (want : I → Bool) :
    (∑ b : I → Bool, if ∀ i ∈ S, b i = want i then decisionWeight p b else 0) =
      ∏ i ∈ S, decisionFactor (p i) (want i) := by
  let g : I → Bool → ℝ := fun i b => if i ∈ S then if b = want i then 1 else 0 else 1
  have hg (b : I → Bool) : (∏ i, g i (b i)) = if ∀ i ∈ S, b i = want i then 1 else 0 := by
    have he (i : I) : g i (b i) = if i ∈ S → b i = want i then 1 else 0 := by
      by_cases hi : i ∈ S <;> simp [g,hi]
    simp_rw [he]
    rw [Fintype.prod_boole]
  have hlocal (i : I) : (1-p i)*g i false+p i*g i true =
      if i ∈ S then decisionFactor (p i) (want i) else 1 := by
    by_cases hi : i ∈ S
    · cases h : want i <;> simp [g,hi,h,decisionFactor]
    · simp [g,hi]
  have h := decisionWeight_product p g
  simp only [hg,mul_ite,mul_one,mul_zero,hlocal,Fintype.prod_ite_mem] at h
  exact h

end ThresholdHC.StoppingProgram
