import ThresholdHC.EntropyTailExecution.PoissonPlan

/-! Exact expected work and mean-square error for the observable Poisson plan,
under the original population experiment. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailSampling

theorem poissonPlan_expectedWork {J : ℕ} (r : Fin (J+1) → ℝ≥0)
    (A : Fin (J+1) → FiniteCall) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {K : Fin (J+1) → ℝ} (hK : ∀ i ω, ((A i).cost ω:ℝ) ≤ K i) :
    expectedWork μ (poissonPlanEstimator r A) q =
      ENNReal.ofReal (∑ i, (r i:ℝ)*(∫ ω, ((A i).cost ω:ℝ) ∂originalPopulationTapeLaw μ q)) := by
  let ν := originalPopulationTapeLaw μ q
  let C := fun i ω => ((A i).cost ω:ℝ)
  have hm : ∀ i, Measurable (C i) := fun i =>
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (A i).measurable_cost
  have hb : ∀ i ω, ‖C i ω‖ ≤ K i := by
    intro i ω
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hK i ω
  have hn : ∀ z, 0 ≤ multilevelCost C z := by
    intro z
    unfold multilevelCost countedSum prefixSum C
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  change expectedWork μ (finitePlanEstimator (countLaw r) (indexedCall A) countLabels) q = _
  rw [finitePlan_expectedWork _ _ _ countLabels_nodup]
  have he : (fun z : (Fin (J+1) → ℕ) × (ℕ → ℕ → Bool) =>
      (plannedCost (indexedCall A) (countLabels z.1) z.2:ℝ≥0∞)) =
      fun z => ENNReal.ofReal (multilevelCost C (poissonPlanInput z)) := by
    funext z
    rw [← plannedCost_counts]
    simp
  rw [he, (poissonPlanInput_preserving ν r).lintegral_comp
    (measurable_multilevelCost C hm).ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal (multilevelCost_integrable ν r C hm hb) (ae_of_all _ hn),
    multilevelCost_mean ν r C hm hb]

theorem poissonPlan_squaredRisk {J : ℕ} (r : Fin (J+1) → ℝ≥0)
    (hr : ∀ i, 0 < (r i:ℝ)) (A : Fin (J+1) → FiniteCall)
    (Y : Fin (J+1) → (ℕ → Bool) → ℝ) (hYm : ∀ i, Measurable (Y i))
    (hY : ∀ i ω, (A i).value ω = (r i:ℝ)⁻¹*Y i ω)
    {K : Fin (J+1) → ℝ} (hK0 : ∀ i, 0 ≤ K i) (hK : ∀ i ω, ‖Y i ω‖ ≤ K i)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a : ℝ) :
    squaredRisk (experimentLaw μ (poissonPlanEstimator r A) q)
      (populationOutput (poissonPlanEstimator r A)) a =
      ENNReal.ofReal ((∑ i, (∫ ω, (Y i ω)^2 ∂originalPopulationTapeLaw μ q)/(r i:ℝ))+
        ((∑ i, ∫ ω, Y i ω ∂originalPopulationTapeLaw μ q)-a)^2) := by
  let ν := originalPopulationTapeLaw μ q
  unfold poissonPlanEstimator
  rw [finitePlan_squaredRisk _ _ _ countLabels_nodup]
  simp_rw [plannedValue_counts A r _ _ Y hY]
  have hm : Measurable (fun z => ENNReal.ofReal ((multilevelValue r Y z-a)^2)) :=
    (((measurable_multilevelValue r Y hYm).sub measurable_const).pow_const 2).ennreal_ofReal
  rw [(poissonPlanInput_preserving ν r).lintegral_comp hm]
  have hi := ((multilevelValue_memLp ν r Y hYm hK0 hK).sub (memLp_const a)).integrable_sq
  dsimp only [Pi.sub_apply] at hi
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => sq_nonneg _)),
    multilevelValue_mse ν r hr Y hYm hK0 hK]

end ThresholdHC.EntropyTailExecution
