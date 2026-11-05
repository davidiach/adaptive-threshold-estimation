import ThresholdHC.Tier5.FiniteJoint

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved

/-- Nonnegative finite-kernel tests determine the bounded real tests used
by the original population experiment, including arbitrary seed spaces. -/
theorem finite_kernel_of_lintegral {R W : Type} [MeasurableSpace R] [MeasurableSpace W]
    [Fintype W] [MeasurableSingletonClass W]
    (μ : Measure R) (P : Measure (R × W)) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (p : R → W → ℝ) (hp : ∀ w, Measurable (fun r => p r w))
    (hp0 : ∀ r w, 0 ≤ p r w) (hs : ∀ r, (∑ w, p r w) = 1)
    (hl : ∀ F : R × W → ℝ≥0∞, Measurable F →
      (∫⁻ z, F z ∂P) = ∫⁻ r, ∑ w, ENNReal.ofReal (p r w) * F (r,w) ∂μ) :
    ThresholdHC.Tier5.FiniteKernelRealization μ P p := by
  intro f hf hbound
  obtain ⟨C,hC⟩ := hbound
  let H (r : R) := ∑ w, p r w * f (r,w)
  have hm : Measurable H :=
    Finset.measurable_sum _ (fun w _ => (hp w).mul (hf.comp (measurable_id.prodMk measurable_const)))
  have hb (r : R) : |H r| ≤ C := by
    calc
      _ ≤ ∑ w, |p r w * f (r,w)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ w, p r w * |f (r,w)| := by
        apply Finset.sum_congr rfl
        intro w _
        rw [abs_mul,abs_of_nonneg (hp0 r w)]
      _ ≤ ∑ w, p r w * C := Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hC _) (hp0 r w))
      _ = C := by rw [← Finset.sum_mul,hs,one_mul]
  have hfi : Integrable f P := ThresholdHC.Tier5.integrable_of_abs_bound _ _ hf C hC
  have hHi : Integrable H μ := ThresholdHC.Tier5.integrable_of_abs_bound _ _ hm C hb
  have hg0 (z : R × W) : 0 ≤ f z + C := by have h := (abs_le.mp (hC z)).1; linarith
  have hH0 (r : R) : 0 ≤ H r + C := by have h := (abs_le.mp (hb r)).1; linarith
  have he (r : R) :
      (∑ w, ENNReal.ofReal (p r w) * ENNReal.ofReal (f (r,w) + C)) =
        ENNReal.ofReal (H r + C) := by
    simp_rw [← ENNReal.ofReal_mul (hp0 r _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => mul_nonneg (hp0 r w) (hg0 (r,w)))]
    congr 1
    simp only [H,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul]
  have h := hl (fun z => ENNReal.ofReal (f z + C)) (ENNReal.measurable_ofReal.comp (hf.add_const C))
  simp_rw [he] at h
  have ht := congrArg ENNReal.toReal h
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) (hf.add_const C).aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hH0) (hm.add_const C).aestronglyMeasurable] at ht
  rw [integral_add hfi (integrable_const C),integral_add hHi (integrable_const C)] at ht
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at ht
  exact add_right_cancel ht

end ThresholdHC.ContinuousObserved
