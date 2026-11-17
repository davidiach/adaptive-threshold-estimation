import ThresholdHC.PowerWindow.DensityBounds

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile
open ThresholdHC.PsiGap

theorem power_core_band_integral (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a) (j : ℕ) :
    bandCost (quantileCore μ ρ) j = a⁻¹ ^ 2 *
      ∫ u in Ioc ρ 1 ∩ Ioc ((bandEdge j / 2 / a)^α) ((bandEdge j / a)^α), u ^ (-2/α) := by
  have hf := measurable_powerQuantile α a hα ha ha2
  rw [EntropyTailQuantile.bandCost, power_quantile_core μ hα ha ha2 hρ hρ1.le hm,
    setIntegral_map (measurableSet_band j)
      (show Measurable (fun d : Gap => (d : ℝ)⁻¹ ^ 2) from
        measurable_subtype_coe.inv.pow_const 2).aestronglyMeasurable hf.aemeasurable,
    Measure.restrict_restrict (hf (measurableSet_band j))]
  have hset : powerQuantile α a hα ha ha2 ⁻¹' band j ∩ Ioc ρ 1 =
      Ioc ρ 1 ∩ Ioc ((bandEdge j / 2 / a)^α) ((bandEdge j / a)^α) := by
    ext u
    by_cases hu : u ∈ Ioc ρ 1
    · have hu' : 0 < u ∧ u ≤ 1 := ⟨hρ.trans hu.1, hu.2⟩
      have hb : powerQuantile α a hα ha ha2 u ∈ band j ↔
          u ∈ Ioc ((bandEdge j / 2 / a)^α) ((bandEdge j / a)^α) := by
        change (bandEdge j / 2 < (powerQuantile α a hα ha ha2 u : ℝ) ∧
          (powerQuantile α a hα ha ha2 u : ℝ) ≤ bandEdge j) ↔ _
        rw [lt_iff_not_ge, powerQuantile_le_iff α a hα ha ha2 u _ hu'
          (div_pos (bandEdge_pos j) (by norm_num)), not_le,
          powerQuantile_le_iff α a hα ha ha2 u _ hu' (bandEdge_pos j)]
        rfl
      simp only [mem_inter_iff, mem_preimage, hu, and_true, true_and, hb]
    · simp [hu]
  rw [hset, ← integral_const_mul]
  apply setIntegral_congr_fun (measurableSet_Ioc.inter measurableSet_Ioc)
  intro u hu
  have hu0 := hρ.trans hu.1.1
  simp only [powerQuantile, dite_eq_left (show 0 < u ∧ u ≤ 1 from ⟨hu0, hu.1.2⟩),
    mul_inv, mul_pow]
  congr 1
  rw [← Real.rpow_neg hu0.le, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
  congr 1
  ring

theorem power_band_log_width {α a : ℝ} (hα : 0 < α) (ha : 0 < a) (j : ℕ) :
    Real.log (((bandEdge j / a)^α) / ((bandEdge j / 2 / a)^α)) = α * Real.log 2 := by
  have hu := div_pos (bandEdge_pos j) ha
  have hl : 0 < bandEdge j / 2 / a := div_pos (div_pos (bandEdge_pos j) (by norm_num)) ha
  rw [Real.log_div (Real.rpow_pos_of_pos hu _).ne' (Real.rpow_pos_of_pos hl _).ne',
    Real.log_rpow hu, Real.log_rpow hl,
    Real.log_div (bandEdge_pos j).ne' ha.ne',
    Real.log_div (div_pos (bandEdge_pos j) (by norm_num)).ne' ha.ne',
    Real.log_div (bandEdge_pos j).ne' (by norm_num)]
  ring

theorem power_core_band_peak (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a) (j : ℕ) :
    bandCost (quantileCore μ ρ) j ≤ a⁻¹ ^ 2 *
      (max 1 (ρ ^ (1 - 2/α)) * (α * Real.log 2)) := by
  rw [power_core_band_integral μ hα ha ha2 hρ hρ1 hm j]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hlu : (bandEdge j / 2 / a)^α ≤ (bandEdge j / a)^α :=
    Real.rpow_le_rpow (by positivity [bandEdge_pos j])
      ((div_le_div_iff_of_pos_right ha).2 (by linarith [bandEdge_pos j])) hα.le
  have h := power_density_band_bound hρ hρ1
    (Real.rpow_pos_of_pos (div_pos (div_pos (bandEdge_pos j) (by norm_num)) ha) _) hlu (1 - 2/α)
  rw [power_band_log_width hα ha j] at h
  simpa only [show (1 - 2/α : ℝ) - 1 = -2/α by ring] using h

theorem power_core_band_bound (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a) (j : ℕ) :
    bandCost (quantileCore μ ρ) j ≤
      (a⁻¹ ^ 2 * powerPhi α ρ) *
        (1 / (Real.logb 2 (1/ρ) / α) + |α - 2| * Real.log 2) := by
  have hp := power_density_peak hρ hρ1 (1 - 2/α)
  rw [show (1 - 2/α : ℝ) - 1 = -2/α by ring, uniform_power_integral hα hρ hρ1] at hp
  have habs : α * |1 - 2/α| = |α - 2| := by
    calc
      _ = |α * (1 - 2/α)| := by rw [abs_mul, abs_of_pos hα]
      _ = _ := congrArg abs (by field_simp)
  have hl : Real.logb 2 (1/ρ) / α = (-Real.log ρ) / (α * Real.log 2) := by
    rw [Real.logb, one_div, Real.log_inv]
    ring
  have h2 : 0 ≤ α * Real.log 2 := mul_nonneg hα.le (Real.log_nonneg (by norm_num))
  calc
    _ ≤ a⁻¹ ^ 2 * (max 1 (ρ ^ (1 - 2/α)) * (α * Real.log 2)) :=
      power_core_band_peak μ hα ha ha2 hρ hρ1 hm j
    _ ≤ a⁻¹ ^ 2 * (((-Real.log ρ)⁻¹ + |1 - 2/α|) * powerPhi α ρ * (α * Real.log 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp h2) (sq_nonneg _)
    _ = _ := by
      rw [hl, one_div_div, ← habs]
      ring

end ThresholdHC.PowerWindow
