import ThresholdHC.StoppingProgram.RealizedOutputs
import ThresholdHC.StoppingProgram.PoissonMoments

/-! The actual observable Poisson estimator for a positive-intensity cone
flow, with its exact work and certified mean-square error. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6
open ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailExecution

def flowPoissonRates {N J : ℕ} (f : Flow N) (hf : FlowCone f) (e : Fin (J+1) ≃ PositiveTable f)
    (i : Fin (J+1)) : ℝ≥0 := ⟨flowTableRate f (e i).val,flowTableRate_nonneg f hf _⟩

def flowPoissonCalls {N J : ℕ} (hN : 0 < N) (f : Flow N) (e : Fin (J+1) ≃ PositiveTable f)
    (i : Fin (J+1)) : FiniteCall := tableCall hN (e i).val (flowTableOutput f)

def flowPoissonEstimator {N J : ℕ} (hN : 0 < N) (f : Flow N) (hf : FlowCone f)
    (e : Fin (J+1) ≃ PositiveTable f) : AdaptiveEstimator (Fin (J+1) → ℕ) :=
  poissonPlanEstimator (flowPoissonRates f hf e) (flowPoissonCalls hN f e)

theorem flowPoisson_work {N J : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hN : 0 < N) (f : Flow N) (hf : FlowCone f) (e : Fin (J+1) ≃ PositiveTable f) :
    expectedWork μ (flowPoissonEstimator hN f hf e) q = ENNReal.ofReal (countMean μ q f.continueWeight) := by
  have hk (i : Fin (J+1)) (ω : ℕ → Bool) : ((flowPoissonCalls hN f e i).cost ω:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast tableCall_cost_le hN (e i).val (flowTableOutput f) ω
  rw [flowPoissonEstimator,poissonPlan_expectedWork _ _ μ q hk]
  congr 1
  change (∑ i : Fin (J+1), flowTableRate f (e i).val*
    (∫ ω, (tableCost (e i).val ω:ℝ) ∂originalPopulationTapeLaw μ q)) = _
  rw [enumeratedTable_sum f hf e (fun b => ∫ ω, (tableCost b ω:ℝ) ∂originalPopulationTapeLaw μ q)]
  exact flow_mixture_work μ q f hf hN

theorem flowPoisson_squaredRisk {N J : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hN : 0 < N) (f : Flow N) (hf : FlowCone f) (e : Fin (J+1) ≃ PositiveTable f) (a : ℝ) :
    squaredRisk (experimentLaw μ (flowPoissonEstimator hN f hf e) q)
      (populationOutput (flowPoissonEstimator hN f hf e)) a ≤
      ENNReal.ofReal (countMean μ q f.momentWeight+(countMean μ q f.outputWeight-a)^2) := by
  let K : ℝ := ∑ s, ‖flowTableOutput f s‖
  have hk : 0 ≤ K := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hr (i : Fin (J+1)) : 0 < (flowPoissonRates f hf e i:ℝ) := (e i).property
  have hv (i : Fin (J+1)) (ω : ℕ → Bool) : ‖(flowPoissonCalls hN f e i).value ω‖ ≤ K :=
    tableValue_bounded (e i).val (flowTableOutput f) ω
  rw [flowPoissonEstimator,poissonPlan_unscaled_squaredRisk _ hr _ (fun _ => K) (fun _ => hk) hv]
  apply ENNReal.ofReal_le_ofReal
  change (∑ i : Fin (J+1), flowTableRate f (e i).val*
      (∫ ω, (tableValue (e i).val (flowTableOutput f) ω)^2 ∂originalPopulationTapeLaw μ q))+
    ((∑ i : Fin (J+1), flowTableRate f (e i).val*
      (∫ ω, tableValue (e i).val (flowTableOutput f) ω ∂originalPopulationTapeLaw μ q))-a)^2 ≤ _
  rw [enumeratedTable_sum f hf e (fun b => ∫ ω, (tableValue b (flowTableOutput f) ω)^2 ∂originalPopulationTapeLaw μ q),
    enumeratedTable_sum f hf e (fun b => ∫ ω, tableValue b (flowTableOutput f) ω ∂originalPopulationTapeLaw μ q),
    flow_output_mean μ q f hf hN]
  exact add_le_add (flow_output_second_moment μ q f hf hN) le_rfl

end ThresholdHC.StoppingProgram
