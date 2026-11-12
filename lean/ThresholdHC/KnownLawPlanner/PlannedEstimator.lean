import ThresholdHC.EntropyTailExecution.AllocatedEstimator

/-! The multilevel Poisson estimator run with the rates of a plan.

The allocated estimator of the upper theorem uses the optimal rates. A plan
may use any positive rates, for example rates computed from rounded weights.
Its expected work is at most `Σ r_i c_i` and its squared risk at most
`Σ v_i / r_i + b²`, where `c_i` bounds the expected cost of call `i`, `v_i`
its second moment and `b` the bias of the sum. The bounds concern the
unchanged original expected-budget and squared-risk model. -/

noncomputable section
open MeasureTheory Real
open scoped NNReal ENNReal BigOperators

namespace ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailUpper
open ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailExecution

/-- The observable Poisson estimator with rates `r` over the calls `D`. Call
`i` is repeated a Poisson number of times with mean `r i`, and the sum of its
values is divided by `r i`. -/
def plannedEstimator {J : ℕ} (r : Fin (J+1) → ℝ≥0) (D : Fin (J+1) → FiniteCall) :
    AdaptiveEstimator (Fin (J+1) → ℕ) :=
  poissonPlanEstimator r (fun i => scaleCall ((r i:ℝ)⁻¹) (D i))

/-- Expected work of the planned estimator: at most `Σ r_i c_i`. -/
theorem planned_work_bound {J : ℕ} (r : Fin (J+1) → ℝ≥0) (D : Fin (J+1) → FiniteCall)
    {K : Fin (J+1) → ℝ} (hK : ∀ i ω, ((D i).cost ω:ℝ) ≤ K i)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {c : Fin (J+1) → ℝ}
    (hC : ∀ i, (∫ ω, ((D i).cost ω:ℝ) ∂originalPopulationTapeLaw μ q) ≤ c i) :
    expectedWork μ (plannedEstimator r D) q ≤ ENNReal.ofReal (∑ i, (r i:ℝ) * c i) := by
  unfold plannedEstimator
  rw [poissonPlan_expectedWork _ (fun i => scaleCall ((r i:ℝ)⁻¹) (D i)) μ q (fun i ω => hK i ω)]
  exact ENNReal.ofReal_le_ofReal
    (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hC i) (r i).coe_nonneg)

/-- Squared risk of the planned estimator: at most `Σ v_i / r_i + b²`. -/
theorem planned_mse_bound {J : ℕ} (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ))
    (D : Fin (J+1) → FiniteCall) {U : Fin (J+1) → ℝ}
    (hU0 : ∀ i, 0 ≤ U i) (hU : ∀ i ω, ‖(D i).value ω‖ ≤ U i)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a : ℝ) {v : Fin (J+1) → ℝ}
    (hV : ∀ i, (∫ ω, ((D i).value ω)^2 ∂originalPopulationTapeLaw μ q) ≤ v i)
    {b : ℝ} (hb : 0 ≤ b)
    (hbias : |(∑ i, ∫ ω, (D i).value ω ∂originalPopulationTapeLaw μ q)-a| ≤ b) :
    squaredRisk (experimentLaw μ (plannedEstimator r D) q)
      (populationOutput (plannedEstimator r D)) a ≤
      ENNReal.ofReal ((∑ i, v i / (r i:ℝ)) + b^2) := by
  unfold plannedEstimator
  rw [poissonPlan_squaredRisk _ hr _ (fun i => (D i).value)
    (fun i => (D i).measurable_value) (fun _ _ => rfl) hU0 hU]
  apply ENNReal.ofReal_le_ofReal
  refine add_le_add (Finset.sum_le_sum fun i _ =>
    div_le_div_of_nonneg_right (hV i) (hr i).le) ?_
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr hbias

end ThresholdHC.KnownLawPlanner
