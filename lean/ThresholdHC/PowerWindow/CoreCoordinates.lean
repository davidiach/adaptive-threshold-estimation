import ThresholdHC.PowerWindow.LogMoments
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile

theorem power_core_window (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a) :
    ∀ᵐ d : Gap ∂quantileCore μ ρ,
      a * powerQuantileScale α ρ ≤ (d : ℝ) ∧ (d : ℝ) ≤ a := by
  rw [power_quantile_core μ hα ha ha2 hρ hρ1.le hm]
  apply (ae_map_iff (measurable_powerQuantile α a hα ha ha2).aemeasurable
    ((measurableSet_le measurable_const measurable_subtype_coe).inter
      (measurableSet_le measurable_subtype_coe measurable_const))).2
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 := hρ.trans hu.1
  simp only [powerQuantile, dite_eq_left (show 0 < u ∧ u ≤ 1 from ⟨hu0, hu.2⟩),
    powerQuantileScale, one_div]
  exact ⟨mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hρ.le hu.1.le (inv_pos.2 hα).le) ha.le,
    mul_le_of_le_one_right ha.le (Real.rpow_le_one hu0.le hu.2 (inv_pos.2 hα).le)⟩

theorem power_core_affine_log (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a) (b c : ℝ) :
    Integrable (fun d : Gap => (d : ℝ)⁻¹ ^ 2 * (b + c * Real.log (d : ℝ)))
      (quantileCore μ ρ) ∧
    (∫ d : Gap, (d : ℝ)⁻¹ ^ 2 * (b + c * Real.log (d : ℝ)) ∂quantileCore μ ρ) =
      a⁻¹ ^ 2 * ∫ u in ρ..1, u ^ (-2/α) * (b + c * (Real.log a + α⁻¹ * Real.log u)) := by
  have hmeas : Measurable (fun d : Gap => (d : ℝ)⁻¹ ^ 2 * (b + c * Real.log (d : ℝ))) := by
    fun_prop
  have he (u : ℝ) (hu : u ∈ Ioc ρ 1) :
      (powerQuantile α a hα ha ha2 u : ℝ)⁻¹ ^ 2 *
        (b + c * Real.log (powerQuantile α a hα ha ha2 u : ℝ)) =
      a⁻¹ ^ 2 * (u ^ (-2/α) * (b + c * (Real.log a + α⁻¹ * Real.log u))) := by
    have hu0 := hρ.trans hu.1
    simp only [powerQuantile, dite_eq_left (show 0 < u ∧ u ≤ 1 from ⟨hu0, hu.2⟩),
      Real.log_mul ha.ne' (Real.rpow_pos_of_pos hu0 _).ne', Real.log_rpow hu0,
      mul_inv, mul_pow]
    have hp : (u ^ α⁻¹)⁻¹ ^ 2 = u ^ (-2/α) := by
      rw [← Real.rpow_neg hu0.le, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
      congr 1
      ring
    rw [hp]
    ring
  have hc : ContinuousOn (fun u : ℝ => a⁻¹ ^ 2 *
      (u ^ (-2/α) * (b + c * (Real.log a + α⁻¹ * Real.log u)))) (uIcc ρ 1) := by
    have hn (u : ℝ) (hu : u ∈ uIcc ρ 1) : u ≠ 0 := by
      rw [uIcc_of_le hρ1.le] at hu
      exact (hρ.trans_le hu.1).ne'
    exact continuousOn_const.mul ((continuousOn_id.rpow_const fun u hu => Or.inl (hn u hu)).mul
      (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.add
        (continuousOn_const.mul (continuousOn_id.log hn))))))
  rw [power_quantile_core μ hα ha ha2 hρ hρ1.le hm]
  constructor
  · apply (integrable_map_measure hmeas.aestronglyMeasurable
      (measurable_powerQuantile α a hα ha ha2).aemeasurable).2
    apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hρ1.le).1 hc.intervalIntegrable).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (he u hu).symm
  · rw [integral_map (measurable_powerQuantile α a hα ha ha2).aemeasurable
        hmeas.aestronglyMeasurable, ← intervalIntegral.integral_of_le hρ1.le,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro u hu
    rw [uIoc_of_le hρ1.le] at hu
    exact he u hu

theorem power_core_oriented_log (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a) (e c : ℝ) :
    Integrable (fun d : Gap => (d : ℝ)⁻¹ ^ 2 *
      (1 + e * (Real.log (d : ℝ) - Real.log a - α⁻¹ * c) / Real.log 2)) (quantileCore μ ρ) ∧
    (∫ d : Gap, (d : ℝ)⁻¹ ^ 2 *
      (1 + e * (Real.log (d : ℝ) - Real.log a - α⁻¹ * c) / Real.log 2) ∂quantileCore μ ρ) =
      a⁻¹ ^ 2 * (powerPhi α ρ + e / (α * Real.log 2) *
        ∫ u in ρ..1, u ^ (-2/α) * (Real.log u - c)) := by
  let b := 1 - e * (Real.log a + α⁻¹ * c) / Real.log 2
  let q := e / Real.log 2
  have he (d : Gap) : 1 + e * (Real.log (d : ℝ) - Real.log a - α⁻¹ * c) / Real.log 2 =
      b + q * Real.log (d : ℝ) := by dsimp [b, q]; ring
  simp_rw [he]
  obtain ⟨hi, hv⟩ := power_core_affine_log μ hα ha ha2 hρ hρ1 hm b q
  refine ⟨hi, hv.trans ?_⟩
  congr 1
  have hfun : (fun u : ℝ => u ^ (-2/α) * (b + q * (Real.log a + α⁻¹ * Real.log u))) =
      (fun u : ℝ => u ^ (-2/α) + e / (α * Real.log 2) * (u ^ (-2/α) * (Real.log u - c))) := by
    funext u
    dsimp [b, q]
    ring
  rw [hfun]
  have hn (u : ℝ) (hu : u ∈ uIcc ρ 1) : u ≠ 0 := by
    rw [uIcc_of_le hρ1.le] at hu
    exact (hρ.trans_le hu.1).ne'
  have hp : ContinuousOn (fun u : ℝ => u ^ (-2/α)) (uIcc ρ 1) :=
    continuousOn_id.rpow_const fun u hu => Or.inl (hn u hu)
  have hl : ContinuousOn (fun u : ℝ => Real.log u - c) (uIcc ρ 1) :=
    (continuousOn_id.log hn).sub continuousOn_const
  have hci : IntervalIntegrable (fun u : ℝ => e / (α * Real.log 2) *
      (u ^ (-2/α) * (Real.log u - c))) volume ρ 1 :=
    (hp.mul hl).intervalIntegrable.const_mul _
  rw [intervalIntegral.integral_add hp.intervalIntegrable hci, intervalIntegral.integral_const_mul,
    uniform_power_integral hα hρ hρ1]

theorem log_moment_to_band_mean {α s J I : ℝ} (hα : 0 < α) (hs : 0 < s)
    (hJ : 0 ≤ J) (hI : s * I ≤ α * J) :
    I / (α * Real.log 2) ≤ 2 * J / s := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_div_iff₀ (mul_pos hα hlog) hs).2
  have hh : 0 ≤ (2 * Real.log 2 - 1) * (α * J) :=
    mul_nonneg (by linarith [Real.log_two_gt_d9]) (mul_nonneg hα.le hJ)
  nlinarith

theorem power_core_upper_moment (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a) (hα2 : 2 < α) :
    Integrable (fun d : Gap => (d : ℝ)⁻¹ ^ 2 *
      (1 + Real.log (a / (d : ℝ)) / Real.log 2)) (quantileCore μ ρ) ∧
    (∫ d : Gap, (d : ℝ)⁻¹ ^ 2 * (1 + Real.log (a / (d : ℝ)) / Real.log 2)
      ∂quantileCore μ ρ) ≤ (a⁻¹ ^ 2 * powerPhi α ρ) * (1 + 2 / |α - 2|) := by
  obtain ⟨hi, he⟩ := power_core_oriented_log μ hα ha ha2 hρ hρ1 hm (-1) 0
  have hf (d : Gap) : 1 + (-1) * (Real.log (d : ℝ) - Real.log a - α⁻¹ * 0) / Real.log 2 =
      1 + Real.log (a / (d : ℝ)) / Real.log 2 := by
    rw [Real.log_div ha.ne' d.2.1.ne']
    ring
  simp_rw [hf] at hi he
  refine ⟨hi, ?_⟩
  rw [he, abs_of_pos (sub_pos.2 hα2)]
  let I := ∫ u in ρ..1, u ^ (-2/α) * (Real.log u - 0)
  have hb := upper_log_moment_bound hρ hρ1 (1 - 2/α)
  rw [show (1 - 2/α : ℝ) - 1 = -2/α by ring, uniform_power_integral hα hρ hρ1] at hb
  have hneg : (∫ u in ρ..1, u ^ (-2/α) * (-Real.log u)) = -I := by
    dsimp [I]
    rw [← intervalIntegral.integral_neg]
    congr 1
    ext u
    ring
  rw [hneg] at hb
  have hI : (α - 2) * (-I) ≤ α * powerPhi α ρ := by
    have hh := mul_le_mul_of_nonneg_left hb hα.le
    have hc : α * (1 - 2/α) = α - 2 := by field_simp
    simpa only [← mul_assoc, hc] using hh
  have hmean := log_moment_to_band_mean hα (sub_pos.2 hα2) (power_phi_pos hα hρ hρ1).le hI
  calc
    _ = a⁻¹ ^ 2 * (powerPhi α ρ + (-I) / (α * Real.log 2)) := by dsimp [I]; ring
    _ ≤ a⁻¹ ^ 2 * (powerPhi α ρ + 2 * powerPhi α ρ / (α - 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hmean) (sq_nonneg _)
    _ = _ := by ring

theorem power_core_lower_moment (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a) (hα2 : α < 2) :
    Integrable (fun d : Gap => (d : ℝ)⁻¹ ^ 2 *
      (1 + Real.log ((d : ℝ) / (a * powerQuantileScale α ρ)) / Real.log 2)) (quantileCore μ ρ) ∧
    (∫ d : Gap, (d : ℝ)⁻¹ ^ 2 *
      (1 + Real.log ((d : ℝ) / (a * powerQuantileScale α ρ)) / Real.log 2) ∂quantileCore μ ρ) ≤
      (a⁻¹ ^ 2 * powerPhi α ρ) * (1 + 2 / |α - 2|) := by
  obtain ⟨hi, he⟩ := power_core_oriented_log μ hα ha ha2 hρ hρ1 hm 1 (Real.log ρ)
  have ht := mul_pos ha (quantile_scale_pos (α := α) hρ)
  have hf (d : Gap) : 1 + 1 * (Real.log (d : ℝ) - Real.log a - α⁻¹ * Real.log ρ) / Real.log 2 =
      1 + Real.log ((d : ℝ) / (a * powerQuantileScale α ρ)) / Real.log 2 := by
    rw [Real.log_div d.2.1.ne' ht.ne', Real.log_mul ha.ne' (quantile_scale_pos hρ).ne',
      powerQuantileScale, Real.log_rpow hρ, one_div α]
    ring
  simp_rw [hf] at hi he
  refine ⟨hi, ?_⟩
  rw [he, abs_of_neg (sub_neg.2 hα2)]
  let I := ∫ u in ρ..1, u ^ (-2/α) * (Real.log u - Real.log ρ)
  have hb := lower_log_moment_bound hρ hρ1 (1 - 2/α)
  rw [show (1 - 2/α : ℝ) - 1 = -2/α by ring, uniform_power_integral hα hρ hρ1] at hb
  have hI : (2 - α) * I ≤ α * powerPhi α ρ := by
    have hh := mul_le_mul_of_nonneg_left hb hα.le
    have hc : α * (-(1 - 2/α)) = 2 - α := by field_simp; ring
    simpa only [← mul_assoc, hc] using hh
  have hmean := log_moment_to_band_mean hα (sub_pos.2 hα2) (power_phi_pos hα hρ hρ1).le hI
  calc
    _ = a⁻¹ ^ 2 * (powerPhi α ρ + I / (α * Real.log 2)) := by dsimp [I]; ring
    _ ≤ a⁻¹ ^ 2 * (powerPhi α ρ + 2 * powerPhi α ρ / (2 - α)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hmean) (sq_nonneg _)
    _ = _ := by ring

end ThresholdHC.PowerWindow
