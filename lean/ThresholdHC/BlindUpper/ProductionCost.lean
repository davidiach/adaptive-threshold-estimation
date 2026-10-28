import ThresholdHC.BlindUpper.ProductionAverage

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy
open scoped ENNReal


def productionCost {X : Type} (C : X → ℝ) (n : ℕ) (x : ℕ → X) : ℝ :=
  ∑ i : Fin (n+1), C (x i.val)

theorem measurable_productionCost {X : Type} [MeasurableSpace X]
    (C : X → ℝ) (hC : Measurable C) (n : ℕ) : Measurable (productionCost C n) := by
  apply Finset.measurable_sum
  intro i hi
  exact hC.comp (measurable_pi_apply i.val)

theorem measurable_productionCost_joint {X : Type} [MeasurableSpace X]
    (C : X → ℝ) (hC : Measurable C) : Measurable (fun z : ℕ × (ℕ → X) => productionCost C z.1 z.2) :=
  measurable_from_prod_countable_right (fun n => measurable_productionCost C hC n)

theorem productionCost_nonneg {X : Type} (C : X → ℝ) (hC : ∀ x, 0 ≤ C x) (n : ℕ) (x : ℕ → X) :
    0 ≤ productionCost C n x := Finset.sum_nonneg (fun i hi => hC (x i.val))

theorem productionCost_integrable {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (C : X → ℝ) (hC : Integrable C ν) (n : ℕ) :
    Integrable (productionCost C n) (Measure.infinitePi (fun _ : ℕ => ν)) := by
  apply integrable_finsetSum
  intro i hi
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) i.val).integrable_comp_of_integrable hC

theorem productionCost_mean {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (C : X → ℝ)
    (hCm : Measurable C) (hC : Integrable C ν) (n : ℕ) :
    (∫ x, productionCost C n x ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      ((n : ℝ)+1)*(∫ x, C x ∂ν) := by
  have hi (i : Fin (n+1)) : Integrable (fun x : ℕ → X => C (x i.val))
      (Measure.infinitePi (fun _ : ℕ => ν)) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) i.val).integrable_comp_of_integrable hC
  unfold productionCost
  rw [integral_finsetSum _ (fun i hi' => hi i)]
  have he (i : Fin (n+1)) :
      (∫ x : ℕ → X, C (x i.val) ∂Measure.infinitePi (fun _ : ℕ => ν)) = ∫ x, C x ∂ν := by
    rw [← integral_map (measurable_pi_apply i.val).aemeasurable hCm.aestronglyMeasurable,
      Measure.infinitePi_map_eval]
  simp_rw [he]
  simp

theorem productionCost_lintegral {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (C : X → ℝ)
    (hCm : Measurable C) (hC : Integrable C ν) (hC₀ : ∀ x, 0 ≤ C x) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (productionCost C n x) ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      ENNReal.ofReal (((n : ℝ)+1)*(∫ x, C x ∂ν)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (productionCost_integrable ν C hC n)
    (ae_of_all _ (productionCost_nonneg C hC₀ n)),productionCost_mean ν C hCm hC n]


end ThresholdHC.BlindUpper
