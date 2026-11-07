import ThresholdHC.ArbitraryLawAdaptation.LightContractionCells

/-! The light multiplier's inverse first moment controls every residual tail. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

def lightInverse (v : Gap) : ℝ≥0∞ := ENNReal.ofReal (2/(v : ℝ))

theorem measurable_lightInverse : Measurable lightInverse := by unfold lightInverse; fun_prop

theorem lightInverse_band {v : Gap} {n : ℕ} (hn : bandIndex v = n+1) :
    2/(v : ℝ) ≤ (1/16 : ℝ)*(4 : ℝ)^(n+4) := by
  have hi := inv_anti₀ (by positivity : 0 < (1/2 : ℝ)^(n+3))
    (show (1/2 : ℝ)^(n+3) ≤ (v : ℝ) from by simpa [hn] using (mem_bandIndex v).1.le)
  have hv : (v : ℝ)⁻¹ ≤ (2 : ℝ)^(n+3) := by
    simpa only [one_div, inv_pow, inv_inv] using hi
  have hp : (2 : ℝ)^n ≤ (4 : ℝ)^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hm := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2)
  simp only [pow_add] at hm ⊢
  rw [div_eq_mul_inv]
  norm_num at hm ⊢
  linarith

theorem lightInverse_cell_zero (ν : Measure Gap)
    (hv : ∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) : cellCost ν bandIndex lightInverse 0 = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hv] with v h
  have hn : bandIndex v ≠ 0 := by
    have hb := (mem_bandIndex v).1
    intro he
    rw [he] at hb
    norm_num at hb
    linarith
  simp only [hn, ite_false, Pi.zero_apply]

theorem lightInverse_cell_budget (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hp : ∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤
      ENNReal.ofReal (2*Real.exp (-((4 : ℝ)^(n+2)/2)))) (n : ℕ) :
    cellCost ν bandIndex lightInverse (n+1) ≤ ENNReal.ofReal (1/16 : ℝ)*ENNReal.ofReal (lightCostBound n) := by
  have hm : Measurable (fun v : Gap => if bandIndex v = n+1 then (1 : ℝ≥0∞) else 0) :=
    measurable_const.ite (measurableSet_eq_fun measurable_bandIndex measurable_const) measurable_const
  calc
    _ ≤ (ENNReal.ofReal (1/16 : ℝ)*ENNReal.ofReal ((4 : ℝ)^(n+4)))*
        ∫⁻ v, if bandIndex v = n+1 then (1 : ℝ≥0∞) else 0 ∂ν := by
      rw [← lintegral_const_mul _ hm]
      apply lintegral_mono
      intro v
      by_cases h : bandIndex v = n+1
      · simp only [h, ite_true, mul_one]
        exact (ENNReal.ofReal_le_ofReal (lightInverse_band h)).trans_eq
          (ENNReal.ofReal_mul (by norm_num))
      · simp [h]
    _ = ENNReal.ofReal (1/16 : ℝ)*
        (ENNReal.ofReal ((4 : ℝ)^(n+4))*ν (band (n+1))) := by
      rw [lintegral_bandIndex_indicator, mul_assoc]
    _ ≤ _ := mul_le_mul_right (light_band_budget ν hp n) _

theorem lightCostBound_tsum : (∑' n, ENNReal.ofReal (lightCostBound n)) ≤ 257 := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  rw [Finset.sum_range, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => lightCostBound_nonneg k.val)]
  exact (ENNReal.ofReal_le_ofReal (lightCostBound_prefix n)).trans_eq (by norm_num)

theorem lightInverse_integral (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hv : ∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4)
    (hp : ∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤
      ENNReal.ofReal (2*Real.exp (-((4 : ℝ)^(n+2)/2)))) :
    (∫⁻ v, lightInverse v ∂ν) ≤ 32 := by
  have he := cellCost_merge ν measurable_bandIndex measurable_lightInverse (fun _ : ℕ => ()) ()
  simp only [ite_true] at he
  rw [← he, tsum_eq_zero_add' ENNReal.summable, lightInverse_cell_zero ν hv, zero_add]
  calc
    _ ≤ ∑' n, ENNReal.ofReal (1/16 : ℝ)*ENNReal.ofReal (lightCostBound n) :=
      ENNReal.tsum_le_tsum (lightInverse_cell_budget ν hp)
    _ = ENNReal.ofReal (1/16 : ℝ)*(∑' n, ENNReal.ofReal (lightCostBound n)) :=
      ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (1/16 : ℝ)*257 := mul_le_mul_right lightCostBound_tsum _
    _ ≤ 32 := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
      exact (ENNReal.ofReal_le_ofReal (by norm_num : (1/16 : ℝ)*257 ≤ 32)).trans_eq (by norm_num)

theorem lightGap_tail_kernel (z : Gap × Gap) {h : ℝ} (hh : 0 ≤ h) :
    ENNReal.ofReal (min 1 (h/(lightGap z : ℝ))) ≤
      ENNReal.ofReal (min 1 (h/(z.1 : ℝ)))*lightInverse z.2 := by
  have hr : 1 ≤ 2/(z.2 : ℝ) := (le_div_iff₀ z.2.property.1).mpr (by linarith [z.2.property.2])
  have hr0 : 0 ≤ 2/(z.2 : ℝ) := le_trans zero_le_one hr
  have he : h/(lightGap z : ℝ) = h/(z.1 : ℝ)*(2/(z.2 : ℝ)) := by
    dsimp [lightGap]; field_simp
  have hm : min 1 (h/(lightGap z : ℝ)) ≤ min 1 (h/(z.1 : ℝ))*(2/(z.2 : ℝ)) := by
    rw [min_mul_of_nonneg _ _ hr0, one_mul]
    exact le_min ((min_le_left _ _).trans hr) ((min_le_right _ _).trans_eq he)
  exact (ENNReal.ofReal_le_ofReal hm).trans_eq
    (ENNReal.ofReal_mul (le_min zero_le_one (div_nonneg hh z.1.property.1.le)))

theorem tailCost_light_contraction (σ ν : Measure Gap) [IsFiniteMeasure σ] [IsProbabilityMeasure ν]
    (hv : ∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4)
    (hp : ∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤
      ENNReal.ofReal (2*Real.exp (-((4 : ℝ)^(n+2)/2)))) {h : ℝ} (hh : 0 ≤ h) :
    tailCost ((σ.prod ν).map lightGap) h ≤ 32*tailCost σ h := by
  rw [tailCost, lintegral_map (measurable_tailWeight h) measurable_lightGap]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (min 1 (h/(z.1 : ℝ)))*lightInverse z.2 ∂σ.prod ν :=
      lintegral_mono (fun z => lightGap_tail_kernel z hh)
    _ = tailCost σ h*(∫⁻ v, lightInverse v ∂ν) :=
      lintegral_prod_mul (measurable_tailWeight h).aemeasurable measurable_lightInverse.aemeasurable
    _ ≤ tailCost σ h*32 := mul_le_mul_right (lightInverse_integral ν hv hp) _
    _ = _ := mul_comm _ _

end ThresholdHC.ArbitraryLawAdaptation
