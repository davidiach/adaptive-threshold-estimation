import ThresholdHC.EntropyTail.Model

/-! Boundedness and measure linearity of the tail part of the functional. -/

noncomputable section
open MeasureTheory Set Real

namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6

theorem tailKernel_nonneg {h : ℝ} (hh : 0 ≤ h) (d : Gap) :
    0 ≤ min 1 (h/(d:ℝ)) := le_min (by norm_num) (div_nonneg hh d.property.1.le)

theorem tailKernel_integrable (ν : Measure Gap) [IsFiniteMeasure ν] {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun d : Gap => min 1 (h/(d:ℝ))) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_const.min (measurable_const.div measurable_subtype_coe)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun d => by
    change |min 1 (h / (d:ℝ))| ≤ 1
    rw [abs_of_nonneg (tailKernel_nonneg hh d)]
    exact min_le_left _ _)

theorem tailModulus_nonneg (ν : Measure Gap) {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ tailModulus ν h := integral_nonneg (tailKernel_nonneg hh)

theorem tailModulus_le_mass (ν : Measure Gap) [IsFiniteMeasure ν] {h : ℝ} (hh : 0 ≤ h) :
    tailModulus ν h ≤ ν.real univ := by
  calc
    tailModulus ν h ≤ ∫ _ : Gap, (1 : ℝ) ∂ν :=
      integral_mono (tailKernel_integrable ν hh) (integrable_const _)
        (fun _ => min_le_left _ _)
    _ = ν.real univ := by simp

theorem tailModulus_mono {ν ξ : Measure Gap} [IsFiniteMeasure ξ] (hν : ν ≤ ξ)
    {h : ℝ} (hh : 0 ≤ h) : tailModulus ν h ≤ tailModulus ξ h :=
  integral_mono_measure hν (Filter.Eventually.of_forall (tailKernel_nonneg hh))
    (tailKernel_integrable ξ hh)

theorem tailModulus_add (ν ξ : Measure Gap) [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    {h : ℝ} (hh : 0 ≤ h) : tailModulus (ν+ξ) h = tailModulus ν h + tailModulus ξ h :=
  integral_add_measure (tailKernel_integrable ν hh) (tailKernel_integrable ξ hh)

theorem tailModulus_eq_mass (ν : Measure Gap) {h : ℝ}
    (hs : ∀ᵐ d : Gap ∂ν, (d:ℝ) ≤ h) : tailModulus ν h = ν.real univ := by
  calc
    tailModulus ν h = ∫ _ : Gap, (1 : ℝ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hs] with d hd
      exact min_eq_left ((one_le_div d.property.1).2 hd)
    _ = ν.real univ := by simp

theorem inverse_integrable_of_support (ν : Measure Gap) [IsFiniteMeasure ν] {t : ℝ}
    (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂ν, t ≤ (d:ℝ)) :
    Integrable (fun d : Gap => (d:ℝ)⁻¹) ν := by
  apply (integrable_const t⁻¹).mono' (by fun_prop)
  filter_upwards [hs] with d hd
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr d.property.1)]
  exact inv_anti₀ ht hd

theorem tailModulus_eq_inverseCost (ν : Measure Gap) {h : ℝ}
    (hs : ∀ᵐ d : Gap ∂ν, h ≤ (d:ℝ)) :
    tailModulus ν h = h * ∫ d : Gap, (d:ℝ)⁻¹ ∂ν := by
  calc
    tailModulus ν h = ∫ d : Gap, h * (d:ℝ)⁻¹ ∂ν := by
      apply integral_congr_ae
      filter_upwards [hs] with d hd
      rw [min_eq_right ((div_le_one d.property.1).2 hd), div_eq_mul_inv]
    _ = _ := integral_const_mul _ _

end ThresholdHC.EntropyTail
