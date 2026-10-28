import ThresholdHC.BlindUpper.PilotWork

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy
open scoped ENNReal


theorem boundedCost_integrable {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℝ) (C : X → ℝ)
    (hC : ∀ x, 0 ≤ C x ∧ C x ≤ N) (hCm : Measurable C) : Integrable C ν := by
  apply Integrable.of_bound hCm.aestronglyMeasurable N
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hC x).1]; exact (hC x).2)

theorem firstPilotWork_cost_expectation {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℝ) (hN : 0 < N)
    (C : X → ℝ) (hC : ∀ x, 0 ≤ C x ∧ C x ≤ N) (hCm : Measurable C)
    (hc : 0 < ∫ x, C x ∂ν) :
    (∫⁻ z, firstPilotWork (costParameter N hN C hC) (fun x => ENNReal.ofReal (C x)) z
      ∂Measure.infinitePi (fun _ : ℕ => ν.prod uniformUnitMeasure)) = ENNReal.ofReal N := by
  have hmC : Measurable (fun x => ENNReal.ofReal (C x)) := ENNReal.measurable_ofReal.comp hCm
  rw [firstPilotWork_expectation ν _ (measurable_costParameter N hN C hC hCm)
    (fun x => ENNReal.ofReal (C x)) hmC,mean_costParameter ν N hN C hC hCm]
  rw [← ofReal_integral_eq_lintegral_ofReal (boundedCost_integrable ν N C hC hCm)
    (ae_of_all _ (fun x => (hC x).1)),
    ← ENNReal.ofReal_inv_of_pos (div_pos hc hN),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (div_nonneg hc.le hN.le))]
  congr 1
  field_simp

def twoPilotWork {X : Type} (P : X → unitInterval) (C : X → ℝ≥0∞)
    (z : (ℕ → X × ℝ) × (ℕ → X × ℝ)) : ℝ≥0∞ := firstPilotWork P C z.1+firstPilotWork P C z.2

theorem twoPilotWork_cost_expectation {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℝ) (hN : 0 < N)
    (C : X → ℝ) (hC : ∀ x, 0 ≤ C x ∧ C x ≤ N) (hCm : Measurable C)
    (hc : 0 < ∫ x, C x ∂ν) :
    (∫⁻ z, twoPilotWork (costParameter N hN C hC) (fun x => ENNReal.ofReal (C x)) z
      ∂(Measure.infinitePi (fun _ : ℕ => ν.prod uniformUnitMeasure)).prod
        (Measure.infinitePi (fun _ : ℕ => ν.prod uniformUnitMeasure))) = ENNReal.ofReal (2*N) := by
  let P := costParameter N hN C hC
  let D : X → ℝ≥0∞ := fun x => ENNReal.ofReal (C x)
  have hm := measurable_firstPilotWork P (measurable_costParameter N hN C hC hCm) D
    (ENNReal.measurable_ofReal.comp hCm)
  have hf : Measurable (fun z : (ℕ → X × ℝ) × (ℕ → X × ℝ) => firstPilotWork P D z.1) :=
    hm.comp measurable_fst
  have hs : Measurable (fun z : (ℕ → X × ℝ) × (ℕ → X × ℝ) => firstPilotWork P D z.2) :=
    hm.comp measurable_snd
  change (∫⁻ z : (ℕ → X × ℝ) × (ℕ → X × ℝ), firstPilotWork P D z.1+firstPilotWork P D z.2 ∂_) = _
  rw [lintegral_add_left hf,lintegral_prod _ hf.aemeasurable,lintegral_prod _ hs.aemeasurable]
  simp only [lintegral_const,measure_univ,mul_one]
  rw [firstPilotWork_cost_expectation ν N hN C hC hCm hc,
    ← ENNReal.ofReal_add hN.le hN.le]
  congr 1
  ring


end ThresholdHC.BlindUpper
