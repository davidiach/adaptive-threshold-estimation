import ThresholdHC.PowerWindow.Law
import ThresholdHC.PowerWindow.Phi
import ThresholdHC.PsiGap.Entropy

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiClosedForm
open ThresholdHC.EntropyTailQuantile ThresholdHC.PsiGap

theorem uniform_power_integral {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (∫ u in ρ..1, u ^ (-2 / α)) = powerPhi α ρ := by
  rw [power_phi_closed α ρ hα hρ hρ1]
  by_cases ht : α = 2
  · subst α
    rw [ite_eq_left (show (2 : ℝ) = 2 from rfl)]
    norm_num only [neg_div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_neg_one]
    exact integral_inv_of_pos hρ (by norm_num)
  · rw [ite_eq_right ht, integral_rpow (Or.inr ⟨?_, notMem_uIcc_of_lt hρ (by norm_num)⟩)]
    · rw [Real.one_rpow, show -2 / α + 1 = 1 - 2 / α by ring]
      field_simp
    · intro he
      apply ht
      have := (div_eq_iff hα.ne').1 he
      linarith

theorem power_core_integral (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a) :
    (∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂quantileCore μ ρ) = a⁻¹ ^ 2 * powerPhi α ρ := by
  rw [power_quantile_core μ hα ha ha2 hρ hρ1.le hm,
    integral_map (measurable_powerQuantile α a hα ha ha2).aemeasurable
      (show Measurable (fun d : Gap => (d : ℝ)⁻¹ ^ 2) from
        measurable_subtype_coe.inv.pow_const 2).aestronglyMeasurable,
    ← intervalIntegral.integral_of_le hρ1.le,
    ← uniform_power_integral hα hρ hρ1, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u hu
  rw [uIoc_of_le hρ1.le] at hu
  have hu0 := hρ.trans hu.1
  have hu' : 0 < u ∧ u ≤ 1 := ⟨hu0, hu.2⟩
  simp only [powerQuantile, dite_eq_left hu', mul_inv, mul_pow]
  congr 1
  rw [← Real.rpow_neg hu0.le, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
  congr 1
  ring

/-- The inverse-square cost identity of Lemma 14.12 for the actual quantile
core, including exponent two and arbitrary scale `a`. -/
theorem power_core_cost (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a) :
    a^2 * coreCost μ ρ = powerPhi α ρ := by
  have : IsFiniteMeasure (quantileCore μ ρ) :=
    isFiniteMeasure_of_le μ (quantileCore_le μ ρ)
  have ht := quantileThreshold_properties μ hρ hρ1.le
  obtain ⟨_, _, _, _, hint, _⟩ :=
    core_bands (quantileCore μ ρ) ht.1 ht.2.1 (quantileCore_support μ ρ)
  unfold coreCost inverseSquareCost
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun d => sq_nonneg ((d : ℝ)⁻¹)),
    ENNReal.toReal_ofReal (integral_nonneg fun d : Gap => sq_nonneg ((d : ℝ)⁻¹)),
    power_core_integral μ hα ha ha2 hρ hρ1 hm]
  field_simp

end ThresholdHC.PowerWindow
