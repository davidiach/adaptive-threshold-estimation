import ThresholdHC.LightContractionConstant.Series

/-! Inverse moments of the light multiplier. The inverse square is split into
the canonical band cells. The cell of band `0` is null because `V ≤ 1/4`
almost surely, and on band `j+1` (the paper's band `k = j+2`) the inverse square
is at most `4^{j+3} = 4^{k+1}`. Since the bracket `1 + log(1/p_k) + log 2` is
at least one, `E V^{-2} ≤ C_V`. The inverse first moment is half of the
existing bound `E[2/V] ≤ 32`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.LightContractionConstant
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.EntropyTail

theorem cellCost_band_zero (ν : Measure Gap) (w : Gap → ℝ≥0∞)
    (hv : ∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) : cellCost ν bandIndex w 0 = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hv] with v h
  have hn : bandIndex v ≠ 0 := by
    have hb := (mem_bandIndex v).1
    intro he
    rw [he] at hb
    norm_num at hb
    linarith
  simp only [hn, ite_false, Pi.zero_apply]

theorem inverseSquare_le_of_bandIndex {v : Gap} {j : ℕ} (h : bandIndex v = j+1) :
    ((v : ℝ)⁻¹)^2 ≤ (4 : ℝ)^(j+3) := by
  have hi := inv_anti₀ (by positivity : 0 < (1/2 : ℝ)^(j+3))
    (show (1/2 : ℝ)^(j+3) ≤ (v : ℝ) from by simpa [h] using (mem_bandIndex v).1.le)
  have hv : (v : ℝ)⁻¹ ≤ (2 : ℝ)^(j+3) := by
    simpa only [one_div, inv_pow, inv_inv] using hi
  calc ((v : ℝ)⁻¹)^2 ≤ ((2 : ℝ)^(j+3))^2 := pow_le_pow_left₀ (inv_nonneg.2 v.2.1.le) hv 2
    _ = (4 : ℝ)^(j+3) := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num

theorem cellCost_inverseWeight_succ (ν : Measure Gap) (j : ℕ) :
    cellCost ν bandIndex inverseWeight (j+1) ≤ ENNReal.ofReal ((4 : ℝ)^(j+3)) * ν (band (j+1)) := by
  have hm : Measurable (fun v : Gap => if bandIndex v = j+1 then (1 : ℝ≥0∞) else 0) :=
    measurable_const.ite (measurableSet_eq_fun measurable_bandIndex measurable_const)
      measurable_const
  calc cellCost ν bandIndex inverseWeight (j+1)
      ≤ ∫⁻ v, ENNReal.ofReal ((4 : ℝ)^(j+3)) *
          (if bandIndex v = j+1 then (1 : ℝ≥0∞) else 0) ∂ν := by
        apply lintegral_mono
        intro v
        by_cases h : bandIndex v = j+1
        · simp only [h, ite_true, mul_one]
          exact ENNReal.ofReal_le_ofReal (inverseSquare_le_of_bandIndex h)
        · simp [h]
    _ = ENNReal.ofReal ((4 : ℝ)^(j+3)) * ν (band (j+1)) := by
        rw [lintegral_const_mul _ hm, lintegral_bandIndex_indicator]

theorem cellCost_le_cvTerm (ν : Measure Gap) [IsProbabilityMeasure ν] (j : ℕ) :
    cellCost ν bandIndex inverseWeight (j+1) ≤ ENNReal.ofReal (cvTerm ν (j+2)) := by
  have h0 := bandProb_nonneg ν (j+2)
  have hl := log_one_div_nonneg_of_le_one h0 (bandProb_le_one ν (j+2))
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hb : ν (band (j+1)) = ENNReal.ofReal (bandProb ν (j+2)) := by
    rw [bandProb_band, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hr : (4 : ℝ)^(j+3) * bandProb ν (j+2) ≤ cvTerm ν (j+2) := by
    unfold cvTerm
    exact le_mul_of_one_le_right (mul_nonneg (by positivity) h0) (by linarith)
  calc cellCost ν bandIndex inverseWeight (j+1)
      ≤ ENNReal.ofReal ((4 : ℝ)^(j+3)) * ν (band (j+1)) := cellCost_inverseWeight_succ ν j
    _ = ENNReal.ofReal ((4 : ℝ)^(j+3) * bandProb ν (j+2)) := by
        rw [hb, ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (cvTerm ν (j+2)) := ENNReal.ofReal_le_ofReal hr

/-- `E V^{-2} ≤ C_V`. -/
theorem inverseSquare_le_lightCV (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) :
    (∫⁻ v, ENNReal.ofReal (((v : ℝ)⁻¹)^2) ∂ν) ≤ ENNReal.ofReal (lightCV ν) := by
  have he := cellCost_merge ν measurable_bandIndex measurable_inverseWeight
    (fun _ : ℕ => ()) ()
  simp only [ite_true] at he
  change (∫⁻ v, inverseWeight v ∂ν) ≤ _
  rw [← he, tsum_eq_zero_add' ENNReal.summable,
    cellCost_band_zero ν inverseWeight (lightCDF_support ν hCDF), zero_add, lightCV,
    ENNReal.ofReal_tsum_of_nonneg (fun j => cvTerm_nonneg ν (j+2)) (cvTerm_summable ν hCDF)]
  exact ENNReal.tsum_le_tsum (cellCost_le_cvTerm ν)

/-- `E V^{-2} ≤ 256`. -/
theorem inverseSquare_le_256 (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) :
    (∫⁻ v, ENNReal.ofReal (((v : ℝ)⁻¹)^2) ∂ν) ≤ 256 :=
  (inverseSquare_le_lightCV ν hCDF).trans
    ((ENNReal.ofReal_le_ofReal (lightCV_lt ν hCDF).le).trans_eq (by norm_num))

/-- `E V^{-1} ≤ 16`. -/
theorem inverse_le_16 (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) :
    (∫⁻ v, ENNReal.ofReal ((v : ℝ)⁻¹) ∂ν) ≤ 16 := by
  have h := lightInverse_integral ν (lightCDF_support ν hCDF) (lightCDF_band_bound ν hCDF)
  have he : (∫⁻ v, lightInverse v ∂ν) = 2 * ∫⁻ v, ENNReal.ofReal ((v : ℝ)⁻¹) ∂ν := by
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    apply lintegral_congr
    intro v
    rw [lightInverse, div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [he, show (32 : ℝ≥0∞) = 2 * 16 by norm_num] at h
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).mp h

end ThresholdHC.LightContractionConstant
