import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! First and second moments of actual Poisson replication counts. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace ThresholdHC.EntropyTailUpper

def poissonWeight (r : ℝ≥0) (n : ℕ) : ℝ := exp (-r) * (r:ℝ)^n / n.factorial

theorem poissonWeight_succ (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1:ℕ) = (r:ℝ) * poissonWeight r n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

theorem poissonWeight_first_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonWeight r n * (n:ℝ)) (r:ℝ) := by
  have h := (hasSum_one_poissonMeasure r).mul_left (r:ℝ)
  have hs : HasSum (fun n : ℕ => poissonWeight r (n+1) * (n+1:ℕ)) (r:ℝ) := by
    simp_rw [poissonWeight_succ]
    simpa only [poissonWeight, mul_one] using h
  apply (hasSum_nat_add_iff' 1).mp
  simpa using hs

theorem poissonWeight_factorial_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonWeight r n * (n:ℝ) * ((n:ℝ)-1)) ((r:ℝ)^2) := by
  have he (n : ℕ) : poissonWeight r (n+1) * (n+1:ℕ) * ((n+1:ℕ)-1:ℝ) =
      (r:ℝ) * (poissonWeight r n * (n:ℝ)) := by
    rw [poissonWeight_succ]
    push_cast
    ring
  have hs : HasSum (fun n : ℕ => poissonWeight r (n+1) * (n+1:ℕ) * ((n+1:ℕ)-1:ℝ)) ((r:ℝ)^2) := by
    simpa only [he, pow_two] using (poissonWeight_first_hasSum r).mul_left (r:ℝ)
  apply (hasSum_nat_add_iff' 1).mp
  simpa using hs

theorem poissonWeight_second_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonWeight r n * (n:ℝ)^2) ((r:ℝ)^2+r) := by
  convert (poissonWeight_factorial_hasSum r).add (poissonWeight_first_hasSum r) using 1
  funext n
  ring

theorem poisson_count_integrable (r : ℝ≥0) : Integrable (fun n : ℕ => (n:ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa [poissonWeight] using
    (poissonWeight_first_hasSum r).summable

theorem poisson_count_sq_integrable (r : ℝ≥0) : Integrable (fun n : ℕ => (n:ℝ)^2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa [poissonWeight] using
    (poissonWeight_second_hasSum r).summable

theorem poisson_count_mean (r : ℝ≥0) : (∫ n : ℕ, (n:ℝ) ∂poissonMeasure r) = (r:ℝ) := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul, poissonWeight] using (poissonWeight_first_hasSum r).tsum_eq

theorem poisson_count_second_moment (r : ℝ≥0) :
    (∫ n : ℕ, (n:ℝ)^2 ∂poissonMeasure r) = (r:ℝ)^2+r := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul, poissonWeight] using (poissonWeight_second_hasSum r).tsum_eq

end ThresholdHC.EntropyTailUpper
