import ThresholdHC.BlindUpper.ProductionCost
import ThresholdHC.BlindUpper.DoubleGeometric

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy
open scoped ENNReal


theorem doubleFailures_production_count_integrable (p : unitInterval) (hp : 0 < (p : ℝ)) :
    Integrable (fun n : ℕ => (n : ℝ)+1) (doubleFailuresLaw p) := by
  have he : (fun n : ℕ => (n : ℝ)+1) = (fun n : ℕ => ((n : ℝ)+2)-1) := by funext n; ring
  rw [he]
  exact (doubleFailures_count_integrable p hp).sub (integrable_const 1)

theorem doubleFailures_production_count_mean (p : unitInterval) (hp : 0 < (p : ℝ)) :
    (∫ n, (n : ℝ)+1 ∂doubleFailuresLaw p) = 2/(p : ℝ)-1 := by
  have he : (fun n : ℕ => (n : ℝ)+1) = (fun n : ℕ => ((n : ℝ)+2)-1) := by funext n; ring
  rw [he,integral_sub (doubleFailures_count_integrable p hp) (integrable_const 1),
    doubleFailures_count_mean p hp]
  simp

theorem mixedProduction_mse {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (Z : X → ℝ) (hZm : Measurable Z)
    (hZ : MemLp Z 2 ν) (p : unitInterval) (hp : 0 < (p : ℝ)) (a : ℝ) :
    (∫⁻ z : ℕ × (ℕ → X), ENNReal.ofReal ((productionAverage Z z.1 z.2-a)^2)
      ∂(doubleFailuresLaw p).prod (Measure.infinitePi (fun _ : ℕ => ν))) =
      ENNReal.ofReal (variance Z ν*(p : ℝ)+((∫ x, Z x ∂ν)-a)^2) := by
  have hm : Measurable (fun z : ℕ × (ℕ → X) => ENNReal.ofReal ((productionAverage Z z.1 z.2-a)^2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_productionAverage_joint Z hZm).sub measurable_const).pow_const 2)
  rw [lintegral_prod _ hm.aemeasurable]
  simp_rw [productionAverage_mse ν Z hZm hZ]
  simp_rw [div_eq_mul_inv]
  have hi : Integrable (fun n : ℕ => variance Z ν*((n : ℝ)+1)⁻¹+((∫ x, Z x ∂ν)-a)^2)
      (doubleFailuresLaw p) :=
    ((doubleFailures_inverse_integrable p).const_mul (variance Z ν)).add (integrable_const _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun n =>
    add_nonneg (mul_nonneg (variance_nonneg _ _) (by positivity)) (sq_nonneg _))),
    integral_add ((doubleFailures_inverse_integrable p).const_mul (variance Z ν)) (integrable_const _),
    integral_const_mul,doubleFailures_inverse_mean p hp]
  simp

theorem mixedProduction_work {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (C : X → ℝ)
    (hCm : Measurable C) (hC : Integrable C ν) (hC₀ : ∀ x, 0 ≤ C x)
    (p : unitInterval) (hp : 0 < (p : ℝ)) :
    (∫⁻ z : ℕ × (ℕ → X), ENNReal.ofReal (productionCost C z.1 z.2)
      ∂(doubleFailuresLaw p).prod (Measure.infinitePi (fun _ : ℕ => ν))) =
      ENNReal.ofReal ((2/(p : ℝ)-1)*(∫ x, C x ∂ν)) := by
  have hm : Measurable (fun z : ℕ × (ℕ → X) => ENNReal.ofReal (productionCost C z.1 z.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_productionCost_joint C hCm)
  rw [lintegral_prod _ hm.aemeasurable]
  simp_rw [productionCost_lintegral ν C hCm hC hC₀]
  have hi : Integrable (fun n : ℕ => ((n : ℝ)+1)*(∫ x, C x ∂ν)) (doubleFailuresLaw p) :=
    (doubleFailures_production_count_integrable p hp).mul_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun n =>
    mul_nonneg (by positivity) (integral_nonneg hC₀))),
    integral_mul_const,doubleFailures_production_count_mean p hp]


end ThresholdHC.BlindUpper
