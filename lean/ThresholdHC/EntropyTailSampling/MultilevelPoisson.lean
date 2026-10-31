import ThresholdHC.EntropyTailSampling.PoissonEstimator
import ThresholdHC.EntropyTailUpper.Allocation

/-! Independent finite collections of genuine marked Poisson averages. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped NNReal BigOperators

namespace ThresholdHC.EntropyTailSampling
open ThresholdHC.EntropyTailUpper
variable {X I : Type} [MeasurableSpace X] [Fintype I]

def multilevelLaw (ν : Measure X) (r : I → ℝ≥0) : Measure (I → ℕ × (ℕ → X)) :=
  Measure.pi (fun i => markedPoissonLaw ν (r i))

instance multilevelLaw_probability (ν : Measure X) [IsProbabilityMeasure ν] (r : I → ℝ≥0) :
    IsProbabilityMeasure (multilevelLaw ν r) := by unfold multilevelLaw; infer_instance

def multilevelValue (r : I → ℝ≥0) (Y : I → X → ℝ) (z : I → ℕ × (ℕ → X)) : ℝ :=
  ∑ i, poissonAverage (r i) (Y i) (z i)

def multilevelCost (C : I → X → ℝ) (z : I → ℕ × (ℕ → X)) : ℝ :=
  ∑ i, countedSum (C i) (z i)

theorem measurable_multilevelValue (r : I → ℝ≥0) (Y : I → X → ℝ) (hY : ∀ i, Measurable (Y i)) :
    Measurable (multilevelValue r Y) :=
  Finset.measurable_sum _ (fun i _ => (measurable_poissonAverage (r i) (Y i) (hY i)).comp (measurable_pi_apply i))

theorem measurable_multilevelCost (C : I → X → ℝ) (hC : ∀ i, Measurable (C i)) :
    Measurable (multilevelCost C) :=
  Finset.measurable_sum _ (fun i _ => (measurable_countedSum (C i) (hC i)).comp (measurable_pi_apply i))

theorem multilevelValue_memLp (ν : Measure X) [IsProbabilityMeasure ν]
    (r : I → ℝ≥0) (Y : I → X → ℝ) (hYm : ∀ i, Measurable (Y i))
    {K : I → ℝ} (hK0 : ∀ i, 0 ≤ K i) (hK : ∀ i x, ‖Y i x‖ ≤ K i) :
    MemLp (multilevelValue r Y) 2 (multilevelLaw ν r) := by
  apply memLp_finsetSum
  intro i _
  exact (poissonAverage_memLp ν (r i) (Y i) (hYm i) (hK0 i) (hK i)).comp_measurePreserving
    (measurePreserving_eval (fun i => markedPoissonLaw ν (r i)) i)

theorem multilevelValue_mean (ν : Measure X) [IsProbabilityMeasure ν]
    (r : I → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) (Y : I → X → ℝ) (hYm : ∀ i, Measurable (Y i))
    {K : I → ℝ} (hK0 : ∀ i, 0 ≤ K i) (hK : ∀ i x, ‖Y i x‖ ≤ K i) :
    (∫ z, multilevelValue r Y z ∂multilevelLaw ν r) = ∑ i, ∫ x, Y i x ∂ν := by
  have hi (i : I) : Integrable (fun z : I → ℕ × (ℕ → X) => poissonAverage (r i) (Y i) (z i))
      (multilevelLaw ν r) :=
    ((poissonAverage_memLp ν (r i) (Y i) (hYm i) (hK0 i) (hK i)).comp_measurePreserving
      (measurePreserving_eval (fun i => markedPoissonLaw ν (r i)) i)).integrable (by norm_num)
  unfold multilevelValue
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_map (measurable_pi_apply i).aemeasurable (measurable_poissonAverage (r i) (Y i) (hYm i)).aestronglyMeasurable,
    multilevelLaw, (measurePreserving_eval (fun i => markedPoissonLaw ν (r i)) i).map_eq]
  exact poissonAverage_mean ν (hr i) (Y i) (hYm i) (hK i)

theorem multilevelValue_variance (ν : Measure X) [IsProbabilityMeasure ν]
    (r : I → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) (Y : I → X → ℝ) (hYm : ∀ i, Measurable (Y i))
    {K : I → ℝ} (hK0 : ∀ i, 0 ≤ K i) (hK : ∀ i x, ‖Y i x‖ ≤ K i) :
    variance (multilevelValue r Y) (multilevelLaw ν r) =
      ∑ i, (∫ x, (Y i x)^2 ∂ν)/(r i:ℝ) := by
  have h := variance_sum_pi (μ := fun i => markedPoissonLaw ν (r i))
    (X := fun i => poissonAverage (r i) (Y i)) (fun i => poissonAverage_memLp ν (r i) (Y i) (hYm i) (hK0 i) (hK i))
  have he : multilevelValue r Y = ∑ i, fun z : I → ℕ × (ℕ → X) => poissonAverage (r i) (Y i) (z i) := by
    funext z
    simp [multilevelValue]
  rw [he]
  change variance _ (Measure.pi (fun i => markedPoissonLaw ν (r i))) = _
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  exact poissonAverage_variance ν (hr i) (Y i) (hYm i) (hK0 i) (hK i)

theorem multilevelValue_mse (ν : Measure X) [IsProbabilityMeasure ν]
    (r : I → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) (Y : I → X → ℝ) (hYm : ∀ i, Measurable (Y i))
    {K : I → ℝ} (hK0 : ∀ i, 0 ≤ K i) (hK : ∀ i x, ‖Y i x‖ ≤ K i) (a : ℝ) :
    (∫ z, (multilevelValue r Y z-a)^2 ∂multilevelLaw ν r) =
      (∑ i, (∫ x, (Y i x)^2 ∂ν)/(r i:ℝ))+((∑ i, ∫ x, Y i x ∂ν)-a)^2 := by
  rw [ThresholdHC.BlindUpper.mse_eq_variance_add_bias _ _ (multilevelValue_memLp ν r Y hYm hK0 hK),
    multilevelValue_variance ν r hr Y hYm hK0 hK, multilevelValue_mean ν r hr Y hYm hK0 hK]

theorem multilevelCost_integrable (ν : Measure X) [IsProbabilityMeasure ν]
    (r : I → ℝ≥0) (C : I → X → ℝ) (hCm : ∀ i, Measurable (C i))
    {K : I → ℝ} (hK : ∀ i x, ‖C i x‖ ≤ K i) :
    Integrable (multilevelCost C) (multilevelLaw ν r) := by
  apply integrable_finsetSum
  intro i _
  exact (measurePreserving_eval (fun i => markedPoissonLaw ν (r i)) i).integrable_comp_of_integrable
    (countedSum_integrable ν (r i) (C i) (hCm i) (hK i))

theorem multilevelCost_mean (ν : Measure X) [IsProbabilityMeasure ν]
    (r : I → ℝ≥0) (C : I → X → ℝ) (hCm : ∀ i, Measurable (C i))
    {K : I → ℝ} (hK : ∀ i x, ‖C i x‖ ≤ K i) :
    (∫ z, multilevelCost C z ∂multilevelLaw ν r) = ∑ i, (r i:ℝ)*(∫ x, C i x ∂ν) := by
  have hi (i : I) : Integrable (fun z : I → ℕ × (ℕ → X) => countedSum (C i) (z i))
      (multilevelLaw ν r) :=
    (measurePreserving_eval (fun i => markedPoissonLaw ν (r i)) i).integrable_comp_of_integrable
      (countedSum_integrable ν (r i) (C i) (hCm i) (hK i))
  unfold multilevelCost
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_map (measurable_pi_apply i).aemeasurable (measurable_countedSum (C i) (hCm i)).aestronglyMeasurable,
    multilevelLaw, (measurePreserving_eval (fun i => markedPoissonLaw ν (r i)) i).map_eq]
  exact countedSum_mean ν (r i) (C i) (hCm i)
    (MemLp.of_bound (hCm i).aestronglyMeasurable (K i) (ae_of_all _ (hK i))) (hK i)

end ThresholdHC.EntropyTailSampling
