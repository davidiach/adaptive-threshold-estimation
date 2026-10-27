import ThresholdHC.Tier3.RandomizedBase
import Mathlib.InformationTheory.KullbackLeibler.Basic

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.Tier4

theorem measure_eq_withDensity_of_setIntegral {X : Type} [MeasurableSpace X]
    (P Q : Measure X) [IsFiniteMeasure P] (r : X → ℝ)
    (hr : Integrable r Q) (hr0 : ∀ x, 0 ≤ r x)
    (heq : ∀ s, MeasurableSet s → P.real s = ∫ x in s, r x ∂Q) :
    P = Q.withDensity (fun x => ENNReal.ofReal (r x)) := by
  ext s hs
  rw [withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal hr.integrableOn
    (Filter.Eventually.of_forall hr0), ← heq s hs]
  exact (ENNReal.ofReal_toReal (measure_ne_top P s)).symm

theorem klDiv_of_finite_likelihood {X B : Type} [MeasurableSpace X] [MeasurableSpace B]
    [Finite B] [MeasurableSingletonClass B]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (g : X → B) (hg : Measurable g) (r : B → ℝ)
    (hr0 : ∀ x, 0 ≤ r (g x))
    (hQP : Q.withDensity (fun x => ENNReal.ofReal (r (g x))) = P) :
    klDiv P Q = ENNReal.ofReal (∫ x, Real.log (r (g x)) ∂P) := by
  have hrm : Measurable (fun x => r (g x)) := (measurable_of_countable r).comp hg
  have hac : P ≪ Q := hQP ▸ withDensity_absolutelyContinuous Q _
  have hrn : P.rnDeriv Q =ᵐ[Q] (fun x => ENNReal.ofReal (r (g x))) := by
    rw [← hQP]
    exact Measure.rnDeriv_withDensity Q hrm.ennreal_ofReal
  have hllr : llr P Q =ᵐ[P] (fun x => Real.log (r (g x))) := by
    filter_upwards [hac.ae_le hrn] with x hx
    simp [llr, hx, ENNReal.toReal_ofReal (hr0 x)]
  have hint : Integrable (llr P Q) P := by
    rw [integrable_congr hllr]
    exact Tier3.integrable_finite_comp P g hg (fun b => Real.log (r b))
  rw [klDiv_of_ac_of_integrable hac hint, probReal_univ, probReal_univ,
    add_sub_cancel_right, integral_congr_ae hllr]

/-- A finite measurable statistic supplies an integrable log-density ratio,
including at common zero-density points. -/
theorem klDiv_finite_density {X B : Type} [MeasurableSpace X] [MeasurableSpace B]
    [Finite B] [MeasurableSingletonClass B]
    (μ : Measure X) [IsFiniteMeasure μ] (g : X → B) (hg : Measurable g)
    (p q : B → ℝ) (hp : ∀ x, 0 ≤ p (g x)) (hq : ∀ x, 0 ≤ q (g x))
    (hs : ∀ x, q (g x) = 0 → p (g x) = 0)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (p (g x))))]
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (q (g x))))] :
    klDiv (μ.withDensity (fun x => ENNReal.ofReal (p (g x))))
      (μ.withDensity (fun x => ENNReal.ofReal (q (g x)))) =
      ENNReal.ofReal (∫ x, p (g x) * Real.log (p (g x) / q (g x)) ∂μ) := by
  let P := μ.withDensity (fun x => ENNReal.ofReal (p (g x)))
  let Q := μ.withDensity (fun x => ENNReal.ofReal (q (g x)))
  let r : X → ℝ := fun x => p (g x) / q (g x)
  have hpm : Measurable (fun x => ENNReal.ofReal (p (g x))) :=
    ((measurable_of_countable p).comp hg).ennreal_ofReal
  have hqm : Measurable (fun x => ENNReal.ofReal (q (g x))) :=
    ((measurable_of_countable q).comp hg).ennreal_ofReal
  have hrm : Measurable r := (measurable_of_countable (fun b => p b / q b)).comp hg
  have hr0 (x : X) : 0 ≤ r x := div_nonneg (hp _) (hq _)
  have hQP : Q.withDensity (fun x => ENNReal.ofReal (r x)) = P := by
    rw [show Q = μ.withDensity (fun x => ENNReal.ofReal (q (g x))) from rfl,
      ← withDensity_mul μ hqm hrm.ennreal_ofReal]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hq _)]
    by_cases h : q (g x) = 0
    · simp [h, hs _ h, r]
    · simp [r, h, mul_div_cancel₀]
  have hac : P ≪ Q := hQP ▸ withDensity_absolutelyContinuous Q _
  have hrn : P.rnDeriv Q =ᵐ[Q] (fun x => ENNReal.ofReal (r x)) := by
    rw [← hQP]
    exact Measure.rnDeriv_withDensity Q hrm.ennreal_ofReal
  have hllr : llr P Q =ᵐ[P] (fun x => Real.log (r x)) := by
    filter_upwards [hac.ae_le hrn] with x hx
    simp [llr, hx, ENNReal.toReal_ofReal (hr0 x)]
  have hint : Integrable (llr P Q) P := by
    rw [integrable_congr hllr]
    exact Tier3.integrable_finite_comp P g hg (fun b => Real.log (p b / q b))
  change klDiv P Q = _
  rw [klDiv_of_ac_of_integrable hac hint, probReal_univ, probReal_univ, add_sub_cancel_right,
    integral_congr_ae hllr]
  congr 1
  rw [show P = μ.withDensity (fun x => ENNReal.ofReal (p (g x))) from rfl,
    integral_withDensity_eq_integral_toReal_smul hpm (by simp)]
  simp only [ENNReal.toReal_ofReal (hp _), smul_eq_mul]
  rfl

end ThresholdHC.Tier4
