import ThresholdHC.MarginClasses.Gap

/-! The rows `0 < α < 1` and `α > 1` of Corollary `cor:power`. The lower
bounds use the exact reference law with CDF `min 1 (C t^α)` and the point
mass at `1/2`; the upper bounds use the sublinear modulus bound and the
inverse-moment bound, each inverted at an explicit budget. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.MarginClasses
open ThresholdHC.Tier6 ThresholdHC.Confidence ThresholdHC.Envelope
open ThresholdHC.RareAboveTwo ThresholdHC.SubcriticalPower

/-- Lower half of the row `0 < α < 1`. -/
theorem sub_lower {α C ε δ : ℝ} (hα : 0 < α) (hC : 2^α ≤ C) (hε : 0 < ε) (hε' : ε ≤ 1/25)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4) :
    ENNReal.ofReal ((15 * C / (256 * Real.sqrt 2)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α))
      ≤ classWork (PowerClass α C) ε δ := by
  apply le_sInf
  rintro t ⟨R,mR,A,B,hA,rfl⟩
  have hC0 := class_const_pos hC
  have ha := ref_pos (α := α) hC0
  obtain ⟨hw,hc⟩ := hA (powerGapLaw α (C^(-(1/α))) hα ha (ref_le_half hα hC)) (refLaw_mem hα hC)
  obtain ⟨hB,h⟩ := witness_lower _ A hε hε' hδ hδ' hw hc
  apply ENNReal.ofReal_le_ofReal
  have hB0 : 0 < B := by linarith
  have hsq := scale_sq hB0 hδ hδ'
  have hs0 := confidenceScale_pos hB0 hδ hδ'
  have hf := mass_le_modulus (powerGapLaw α (C^(-(1/α))) hα ha (ref_le_half hα hC)) hs0.le
  rw [powerGapLaw_cdf _ _ _ _ _ _ hs0,ref_power hα hC0 hs0.le] at hf
  have hc0 := cutoff_lt
  have hcp : 0 < 15/(256*Real.sqrt 2) := by positivity
  have hK : 15 * C / (256 * Real.sqrt 2) = 15/(256*Real.sqrt 2) * C := by ring
  have hK0 : 0 < 15 * C / (256 * Real.sqrt 2) := by positivity
  rcases min_cases 1 (C * (confidenceScale B δ)^α) with ⟨h1,_⟩ | ⟨h1,_⟩
  · rw [h1] at hf
    nlinarith
  · rw [h1] at hf
    have h2 : (confidenceScale B δ)^α * (15 * C / (256 * Real.sqrt 2)) ≤ ε := by
      rw [hK]
      nlinarith
    have h3 : (confidenceScale B δ)^α ≤ ε / (15 * C / (256 * Real.sqrt 2)) :=
      (le_div_iff₀ hK0).mpr h2
    have he : α * (2/α) = 2 := by field_simp
    have h4 : (confidenceScale B δ)^2 ≤ (ε / (15 * C / (256 * Real.sqrt 2)))^(2/α) := by
      have h5 := Real.rpow_le_rpow (Real.rpow_nonneg hs0.le α) h3 (by positivity : (0:ℝ) ≤ 2/α)
      rwa [← Real.rpow_mul hs0.le,he,Real.rpow_two] at h5
    rw [Real.div_rpow hε.le hK0.le] at h4
    have hE : 0 < ε^(2/α) := Real.rpow_pos_of_pos hε _
    have hKE : 0 < (15 * C / (256 * Real.sqrt 2))^(2/α) := Real.rpow_pos_of_pos hK0 _
    rw [le_div_iff₀ hKE] at h4
    rw [neg_div,Real.rpow_neg hε.le,mul_inv_le_iff₀ hE]
    calc (15 * C / (256 * Real.sqrt 2))^(2/α) * Real.log (1/δ)
        = ((confidenceScale B δ)^2 * (15 * C / (256 * Real.sqrt 2))^(2/α)) * B := by
          rw [← hsq]; ring
      _ ≤ ε^(2/α) * B := mul_le_mul_of_nonneg_right h4 hB0.le
      _ = B * ε^(2/α) := by ring

/-- The upper budget of the row `0 < α < 1` is at least one, and at it every
law of the class has modulus at most `ε/8192` at the confidence scale. -/
theorem sub_scale {α C ε δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hC : 2^α ≤ C) (hε : 0 < ε)
    (hε' : ε ≤ 1/25) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (ν : Measure Gap) [IsProbabilityMeasure ν] (hν : PowerClass α C ν) :
    1 ≤ (8192 * C / (1 - α)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α) ∧
      8192 * modulus ν
        (confidenceScale ((8192 * C / (1 - α)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α)) δ) ≤ ε := by
  have hC0 := class_const_pos hC
  have hK0 : 0 < 8192 * C / (1 - α) := div_pos (by positivity) (by linarith)
  have hL := log_ge hδ hδ'
  have hεK : 0 ≤ ε / (8192 * C / (1 - α)) := div_nonneg hε.le hK0.le
  have hx : 0 < (ε / (8192 * C / (1 - α)))^(1/α) := Real.rpow_pos_of_pos (div_pos hε hK0) _
  have he : (1/α) * 2 = 2/α := by ring
  have hx2 : ((ε / (8192 * C / (1 - α)))^(1/α))^2 = ε^(2/α) / (8192 * C / (1 - α))^(2/α) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hεK]
    push_cast
    rw [he,Real.div_rpow hε.le hK0.le]
  have hE : 0 < ε^(2/α) := Real.rpow_pos_of_pos hε _
  have hKE : 0 < (8192 * C / (1 - α))^(2/α) := Real.rpow_pos_of_pos hK0 _
  have hB : (8192 * C / (1 - α)) ^ (2/α) * Real.log (1/δ) * ε ^ (-2/α) *
      ((ε / (8192 * C / (1 - α)))^(1/α))^2 = Real.log (1/δ) := by
    rw [hx2,neg_div,Real.rpow_neg hε.le]
    field_simp
  refine ⟨?_,?_⟩
  · have hC1 : 1 ≤ C := le_trans (Real.one_le_rpow (by norm_num) hα.le) hC
    have hK1 : 8192 ≤ 8192 * C / (1 - α) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have hKK : 8192 * C / (1 - α) ≤ (8192 * C / (1 - α))^(2/α) := by
      have h1 := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 8192 * C / (1 - α))
        (show (1:ℝ) ≤ 2/α by rw [le_div_iff₀ hα]; linarith)
      rwa [Real.rpow_one] at h1
    have hE1 : 1 ≤ ε^(-2/α) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε (by linarith)
      (by rw [neg_div]; exact neg_nonpos.mpr (by positivity))
    have h1 : 1 ≤ (8192 * C / (1 - α))^(2/α) * Real.log (1/δ) := by nlinarith
    nlinarith
  · rw [scale_eq hδ hδ' hx hB]
    have hm := sublinear_modulus ν (powerClass_margin hα hC hν) (ref_pos hC0) hα hα1 hx
    rw [ref_power hα hC0 hx.le,← Real.rpow_mul hεK,one_div_mul_cancel hα.ne',Real.rpow_one] at hm
    have h1 : C * (ε / (8192 * C / (1 - α))) / (1 - α) = ε / 8192 := by
      have h2 : (1 - α) ≠ 0 := by linarith
      field_simp
    rw [h1] at hm
    linarith

/-- Lower half of the row `α > 1`, through the point mass at `1/2`. -/
theorem super_lower {α C ε δ : ℝ} (hα : 1 < α) (hC : 2^α ≤ C) (hε : 0 < ε) (hε' : ε ≤ 1/25)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4) :
    ENNReal.ofReal (225/32768 * Real.log (1/δ) / ε^2) ≤ classWork (PowerClass α C) ε δ := by
  apply le_sInf
  rintro t ⟨R,mR,A,B,hA,rfl⟩
  obtain ⟨hw,hc⟩ := hA (Measure.dirac (⟨1/2,by norm_num,le_rfl⟩ : Gap))
    (diracHalf_mem (by linarith) hC)
  have h : 225/131072 * Real.log (1/δ) / (ε^2 * (1/2:ℝ)^2) ≤ B :=
    dirac_lower (⟨1/2,by norm_num,le_rfl⟩ : Gap) A hε hε' hδ hδ' hw hc
  apply ENNReal.ofReal_le_ofReal
  have he : 225/32768 * Real.log (1/δ) / ε^2 = 225/131072 * Real.log (1/δ) / (ε^2 * (1/2:ℝ)^2) := by
    field_simp
    ring
  rw [he]
  exact h

/-- The upper budget of the row `α > 1` is at least one, and at it every law
of the class has modulus at most `ε/8192` at the confidence scale. -/
theorem super_scale {α C ε δ : ℝ} (hα : 1 < α) (hC : 2^α ≤ C) (hε : 0 < ε) (hε' : ε ≤ 1/25)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4) (ν : Measure Gap) [IsProbabilityMeasure ν] (hν : PowerClass α C ν) :
    1 ≤ (8192 * α * C ^ (1/α) / (α - 1)) ^ 2 * Real.log (1/δ) / ε^2 ∧
      8192 * modulus ν
        (confidenceScale ((8192 * α * C ^ (1/α) / (α - 1)) ^ 2 * Real.log (1/δ) / ε^2) δ) ≤ ε := by
  obtain ⟨hi,hI⟩ := power_inverse hα hC ν hν
  have hα0 : 0 < α := by linarith
  have hr := ref_root_ge hα0 hC
  have hJ : 2 ≤ α * C^(1/α) / (α - 1) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hJ0 : 0 < α * C^(1/α) / (α - 1) := by linarith
  have hJne : α * C^(1/α) / (α - 1) ≠ 0 := hJ0.ne'
  have hL := log_ge hδ hδ'
  have he : 8192 * α * C ^ (1/α) / (α - 1) = 8192 * (α * C^(1/α) / (α - 1)) := by ring
  rw [he]
  have hx : 0 < ε / (8192 * (α * C^(1/α) / (α - 1))) := div_pos hε (by linarith)
  have hB : (8192 * (α * C^(1/α) / (α - 1)))^2 * Real.log (1/δ) / ε^2 *
      (ε / (8192 * (α * C^(1/α) / (α - 1))))^2 = Real.log (1/δ) := by
    field_simp
  refine ⟨?_,?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have h1 : ε^2 ≤ 1 := by nlinarith
    have h2 : 1 ≤ (8192 * (α * C^(1/α) / (α - 1)))^2 := by nlinarith
    nlinarith
  · rw [scale_eq hδ hδ' hx hB]
    have hm := modulus_le_inverse ν hi hx.le
    have h3 := mul_le_mul_of_nonneg_left hI hx.le
    have h4 : ε / (8192 * (α * C^(1/α) / (α - 1))) * (α * C^(1/α) / (α - 1)) = ε / 8192 := by
      field_simp
    linarith

end ThresholdHC.MarginClasses
