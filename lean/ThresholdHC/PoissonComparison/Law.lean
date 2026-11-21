import ThresholdHC.PoissonComparison.Specification

/-! The Poisson vector law: it is a probability measure, its singleton masses
are products of Poisson masses, and the exponential of an affine score
`b + ∑ j, β j * z j` is integrable, with integral
`exp (b + ∑ j, w j * (exp (β j) - 1))` when every `w j ≥ 0`. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Nat
namespace ThresholdHC.PoissonComparison

/-- The Poisson vector law is a probability measure for every intensity vector. -/
instance poissonVectorLaw_isProbabilityMeasure {J : Type} [Fintype J] (w : J → ℝ) :
    IsProbabilityMeasure (poissonVectorLaw w) := by
  unfold poissonVectorLaw
  infer_instance

theorem poissonVectorLaw_singleton {J : Type} [Fintype J] (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (z : J → ℕ) :
    poissonVectorLaw w {z} =
      ∏ j, ENNReal.ofReal (Real.exp (-w j) * w j ^ (z j) / (z j)!) := by
  rw [poissonVectorLaw, Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro j _
  rw [poissonMeasure_singleton, Real.coe_toNNReal _ (hw j)]

/-- One coordinate: `n ↦ exp (β n)` is integrable under `Po(r)`. -/
theorem poisson_exp_integrable (r : NNReal) (β : ℝ) :
    Integrable (fun n : ℕ => Real.exp (β * n)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have h := (Real.summable_pow_div_factorial ((r : ℝ) * Real.exp β)).mul_left
    (Real.exp (-(r : ℝ)))
  refine h.congr (fun n => ?_)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_comm β,Real.exp_nat_mul,mul_pow]
  ring

/-- One coordinate: the moment generating function of `Po(r)`. -/
theorem poisson_exp_integral (r : NNReal) (β : ℝ) :
    (∫ n : ℕ, Real.exp (β * n) ∂(poissonMeasure r)) = Real.exp (r * (Real.exp β - 1)) := by
  rw [integral_poissonMeasure]
  have h := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp β)).mul_left
    (Real.exp (-(r : ℝ)))
  have he : (fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n)!) • Real.exp (β * n)) =
      (fun n => Real.exp (-(r : ℝ)) * (((r : ℝ) * Real.exp β) ^ n / (n)!)) := by
    funext n
    rw [smul_eq_mul,mul_comm β,Real.exp_nat_mul,mul_pow]
    ring
  rw [he,h.tsum_eq,← Real.exp_eq_exp_ℝ,← Real.exp_add]
  congr 1
  ring

theorem exp_affine_score_eq {J : Type} [Fintype J] (b : ℝ) (β : J → ℝ) :
    (fun z : J → ℕ => Real.exp (b + ∑ j, β j * (z j : ℝ))) =
      (fun z => Real.exp b * ∏ j, Real.exp (β j * (z j : ℝ))) := by
  funext z
  rw [Real.exp_add,Real.exp_sum]

/-- The exponential of an affine score is integrable under the Poisson vector law. -/
theorem poissonVectorLaw_exp_integrable {J : Type} [Fintype J] (w : J → ℝ) (b : ℝ)
    (β : J → ℝ) :
    Integrable (fun z : J → ℕ => Real.exp (b + ∑ j, β j * (z j : ℝ))) (poissonVectorLaw w) := by
  rw [exp_affine_score_eq]
  exact (Integrable.fintype_prod (f := fun j (n : ℕ) => Real.exp (β j * n))
    (fun j => poisson_exp_integrable _ _)).const_mul _

/-- Exponential moments of affine scores under the Poisson vector law. -/
theorem poissonVectorLaw_exp_integral {J : Type} [Fintype J] (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (b : ℝ) (β : J → ℝ) :
    (∫ z, Real.exp (b + ∑ j, β j * (z j : ℝ)) ∂(poissonVectorLaw w)) =
      Real.exp (b + ∑ j, w j * (Real.exp (β j) - 1)) := by
  rw [exp_affine_score_eq,integral_const_mul,poissonVectorLaw,
    integral_fintype_prod_eq_prod (fun j (n : ℕ) => Real.exp (β j * n)),Real.exp_add,
    Real.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [poisson_exp_integral,Real.coe_toNNReal _ (hw j)]

end ThresholdHC.PoissonComparison
