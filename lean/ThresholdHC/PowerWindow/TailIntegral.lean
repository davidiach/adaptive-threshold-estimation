import ThresholdHC.PowerWindow.Law
import ThresholdHC.PowerWindow.Phi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.CriticalEntropy
open ThresholdHC.EntropyTailQuantile

/-- The change of variables underlying the power-law tail, with no exceptional
case at exponent one. The clipped kernel is integrable even at zero. -/
theorem power_kernel_integral {α x t : ℝ} (hα : 0 < α) (hx : 0 < x) (hxt : x < t) :
    (∫ u in (0 : ℝ)..t ^ α, min 1 (x / u ^ α⁻¹)) =
      x ^ α + α * x * ∫ s in x..t, s ^ (α - 2) := by
  have ht : 0 < t := hx.trans hxt
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun s : ℝ => s ^ α) (f' := fun s => α * s ^ (α - 1))
    (g := fun u => min 1 (x / u ^ α⁻¹))
    (a := 0) (b := t)
    (continuousOn_id.rpow_const (fun _ _ => Or.inr hα.le))
    (fun s hs => by
      have hs0 : 0 < s := by simpa [min_eq_left ht.le, max_eq_right ht.le] using hs.1
      simpa using (hasDerivAt_id s).rpow_const (Or.inl hs0.ne'))
    (fun s hs => by
      have hs0 : 0 < s := by simpa [min_eq_left ht.le, max_eq_right ht.le] using hs.1
      exact mul_nonneg hα.le (Real.rpow_nonneg hs0.le _))
  rw [Real.zero_rpow hα.ne'] at hsub
  have hsub' : (∫ s in (0 : ℝ)..t, min 1 (x / s) * (α * s ^ (α - 1))) =
      ∫ u in (0 : ℝ)..t ^ α, min 1 (x / u ^ α⁻¹) := by
    rw [← hsub]
    apply intervalIntegral.integral_congr_Ioo_of_le ht.le
    intro s hs
    simp only [Function.comp_apply, Real.rpow_rpow_inv hs.1.le hα.ne']
  rw [← hsub']
  have hleft : (Ioo (0 : ℝ) x).EqOn
      (fun s => min 1 (x / s) * (α * s ^ (α - 1)))
      (fun s => α * s ^ (α - 1)) := by
    intro s hs
    dsimp only
    rw [min_eq_left ((one_le_div hs.1).2 hs.2.le), one_mul]
  have hright : (Ioo x t).EqOn
      (fun s => min 1 (x / s) * (α * s ^ (α - 1)))
      (fun s => α * x * s ^ (α - 2)) := by
    intro s hs
    dsimp only
    have hs0 := hx.trans hs.1
    rw [min_eq_right ((div_le_one hs0).2 hs.1.le)]
    have hp : s ^ (α - 2) = s ^ (α - 1) / s := by
      rw [show α - 2 = (α - 1) - 1 by ring, Real.rpow_sub hs0, Real.rpow_one]
    rw [hp]
    ring
  have il : IntervalIntegrable (fun s : ℝ => α * s ^ (α - 1)) volume 0 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1)).const_mul α
  have ir : IntervalIntegrable (fun s : ℝ => α * x * s ^ (α - 2)) volume x t :=
    ((continuousOn_id.rpow_const (fun s hs => by
      rw [uIcc_of_le hxt.le] at hs
      exact Or.inl (hx.trans_le hs.1).ne')).intervalIntegrable).const_mul (α * x)
  have il' := il.congr_uIoo (by simpa [uIoo_of_le hx.le] using hleft.symm)
  have ir' := ir.congr_uIoo (by simpa [uIoo_of_le hxt.le] using hright.symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals il' ir',
    intervalIntegral.integral_congr_Ioo_of_le hx.le hleft,
    intervalIntegral.integral_congr_Ioo_of_le hxt.le hright,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  congr 1
  rw [integral_rpow (Or.inl (by linarith : -1 < α - 1))]
  rw [show α - 1 + 1 = α by ring, Real.zero_rpow hα.ne']
  field_simp
  ring

/-- The actual clipped lower-quantile cost expressed on its uniform variable. -/
theorem power_tail_uniform_integral (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : ExactPowerLaw μ α a) (x : ℝ) :
    tailModulus (quantileTail μ ρ) (a * x) =
      ∫ u in (0 : ℝ)..ρ, min 1 (x / u ^ α⁻¹) := by
  have hi : Iic ρ ∩ Icc (0 : ℝ) 1 = Icc 0 ρ := by
    ext u
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hu, hu0, _⟩
      exact ⟨hu0, hu⟩
    · rintro ⟨hu0, hu⟩
      exact ⟨hu, hu0, hu.trans hρ1⟩
  unfold tailModulus
  rw [power_quantile_tail μ hα ha ha2 hρ hρ1 hm, partialPowerLaw,
    integral_map (measurable_powerQuantile α a hα ha ha2).aemeasurable
      (show Measurable (fun d : Gap => min 1 (a * x / (d : ℝ))) from
        measurable_const.min (measurable_const.div measurable_subtype_coe)).aestronglyMeasurable,
    uniformUnitMeasure, Measure.restrict_restrict measurableSet_Iic, hi,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hρ.le]
  apply intervalIntegral.integral_congr_Ioo_of_le hρ.le
  intro u hu
  have hu' : 0 < u ∧ u ≤ 1 := ⟨hu.1, hu.2.le.trans hρ1⟩
  simp only [powerQuantile, dite_eq_left hu']
  congr 1
  field_simp

theorem power_tail_formula (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ x : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a)
    (hx : 0 < x) (hxt : x < powerQuantileScale α ρ) :
    tailModulus (quantileTail μ ρ) (a * x) = powerTail α x ρ := by
  rw [power_tail_uniform_integral μ hα ha ha2 hρ hρ1.le hm x]
  have hp : powerQuantileScale α ρ ^ α = ρ := by
    simpa [powerQuantileScale, one_div] using Real.rpow_inv_rpow hρ.le hα.ne'
  simpa only [hp, powerTail] using power_kernel_integral hα hx hxt

theorem power_tail_saturated (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ x : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a)
    (hxt : powerQuantileScale α ρ ≤ x) :
    tailModulus (quantileTail μ ρ) (a * x) = ρ := by
  rw [power_tail_uniform_integral μ hα ha ha2 hρ hρ1.le hm x]
  calc
    _ = ∫ _u in (0 : ℝ)..ρ, (1 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hρ.le
      intro u hu
      apply min_eq_left
      apply (one_le_div (Real.rpow_pos_of_pos hu.1 _)).2
      exact (Real.rpow_le_rpow hu.1.le hu.2.le (inv_pos.2 hα).le).trans
        (by simpa [powerQuantileScale, one_div] using hxt)
    _ = ρ := by simp

end ThresholdHC.PowerWindow
