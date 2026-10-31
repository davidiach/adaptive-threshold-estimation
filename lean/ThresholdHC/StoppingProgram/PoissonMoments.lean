import ThresholdHC.EntropyTailExecution.RealizedPoisson
import ThresholdHC.StoppingProgram.ShiftEstimator

/-! Exact compound-Poisson mean-square error stated directly in terms of
the actual per-call outputs, with positive rates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6
open ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailExecution

theorem poissonPlan_unscaled_squaredRisk {J : ℕ} (r : Fin (J+1) → ℝ≥0)
    (hr : ∀ i, 0 < (r i:ℝ)) (A : Fin (J+1) → FiniteCall)
    (K : Fin (J+1) → ℝ) (hK0 : ∀ i, 0 ≤ K i) (hK : ∀ i ω, ‖(A i).value ω‖ ≤ K i)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a : ℝ) :
    squaredRisk (experimentLaw μ (poissonPlanEstimator r A) q) (populationOutput (poissonPlanEstimator r A)) a =
      ENNReal.ofReal ((∑ i, (r i:ℝ)*(∫ ω, ((A i).value ω)^2 ∂originalPopulationTapeLaw μ q))+
        ((∑ i, (r i:ℝ)*(∫ ω, (A i).value ω ∂originalPopulationTapeLaw μ q))-a)^2) := by
  let Y := fun i ω => (r i:ℝ)*(A i).value ω
  have hYm : ∀ i, Measurable (Y i) := fun i => measurable_const.mul (A i).measurable_value
  have hY : ∀ i ω, (A i).value ω = (r i:ℝ)⁻¹*Y i ω := by
    intro i ω
    dsimp only [Y]
    rw [← mul_assoc,inv_mul_cancel₀ (hr i).ne',one_mul]
  have hKb : ∀ i ω, ‖Y i ω‖ ≤ (r i:ℝ)*K i := by
    intro i ω
    dsimp only [Y]
    rw [norm_mul]
    have he : ‖(r i:ℝ)‖ = (r i:ℝ) := Real.norm_of_nonneg (show (0:ℝ) ≤ r i from (r i).property)
    rw [he]
    exact mul_le_mul_of_nonneg_left (hK i ω) (r i).property
  have h := poissonPlan_squaredRisk r hr A Y hYm hY (fun i => mul_nonneg (r i).property (hK0 i)) hKb μ q a
  have hmean (i) : (∫ ω, Y i ω ∂originalPopulationTapeLaw μ q) =
      (r i:ℝ)*(∫ ω, (A i).value ω ∂originalPopulationTapeLaw μ q) := integral_const_mul _ _
  have hsecond (i) : (∫ ω, (Y i ω)^2 ∂originalPopulationTapeLaw μ q)/(r i:ℝ) =
      (r i:ℝ)*(∫ ω, ((A i).value ω)^2 ∂originalPopulationTapeLaw μ q) := by
    simp only [Y,mul_pow,integral_const_mul]
    field_simp
  simpa only [hmean,hsecond] using h

end ThresholdHC.StoppingProgram
