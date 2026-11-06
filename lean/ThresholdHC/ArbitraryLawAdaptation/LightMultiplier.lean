import ThresholdHC.ArbitraryLawAdaptation.LightContraction
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! Construct the light multiplier from a uniform random variable, including
its atom at one quarter and its exact CDF. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal unitInterval
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

theorem lightLog_pos (u : I) (hu : 0 < (u : ℝ)) : 0 < 2*log (2/(u : ℝ)) := by
  have h : (2 : ℝ) ≤ 2/(u : ℝ) := (le_div_iff₀ hu).mpr (by linarith [u.property.2])
  exact mul_pos (by norm_num) (log_pos (by linarith))

def lightQuantile (u : I) : Gap :=
  ⟨if 0 < (u : ℝ) then min (1/4) (sqrt (2*log (2/(u : ℝ))))⁻¹ else 1/4,
    by split_ifs with hu
       · exact lt_min (by norm_num) (inv_pos.mpr (sqrt_pos.mpr (lightLog_pos u hu)))
       · norm_num,
    by split_ifs
       · exact (min_le_left _ _).trans (by norm_num)
       · norm_num⟩

theorem measurable_lightQuantile : Measurable lightQuantile := by
  apply Measurable.subtype_mk
  apply Measurable.ite (measurableSet_lt measurable_const measurable_subtype_coe)
  · fun_prop
  · exact measurable_const

theorem lightQuantile_le_quarter (u : I) : (lightQuantile u : ℝ) ≤ 1/4 := by
  dsimp [lightQuantile]
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem lightQuantile_le_iff (u : I) {x : ℝ} (hx : 0 < x) (hxq : x < 1/4) :
    (lightQuantile u : ℝ) ≤ x ↔ 0 < (u : ℝ) ∧ (u : ℝ) ≤ 2*exp (-(1/(2*x^2))) := by
  by_cases hu : 0 < (u : ℝ)
  · have hs : 0 < sqrt (2*log (2/(u : ℝ))) := sqrt_pos.mpr (lightLog_pos u hu)
    have he : x⁻¹^2 ≤ 2*log (2/(u : ℝ)) ↔ 1/(2*x^2) ≤ log (2/(u : ℝ)) := by
      rw [inv_pow, ← one_div, div_le_iff₀ (sq_pos_of_pos hx),
        div_le_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hx))]
      constructor <;> intro h <;> nlinarith only [h]
    simp only [lightQuantile, hu, ite_true, min_le_iff, not_le.mpr hxq, false_or, true_and]
    rw [inv_le_comm₀ hs hx, Real.le_sqrt' (inv_pos.mpr hx), he,
      le_log_iff_exp_le (div_pos (by norm_num) hu), exp_neg,
      le_div_iff₀ hu, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)]
    rw [mul_comm]
  · simp only [lightQuantile, hu, ite_false, false_and, iff_false]
    exact not_le.mpr hxq

def lightMultiplier : Measure Gap := (volume : Measure I).map lightQuantile

instance lightMultiplier_probability : IsProbabilityMeasure lightMultiplier :=
  (Measure.isProbabilityMeasure_map_iff measurable_lightQuantile.aemeasurable).mpr inferInstance

theorem lightMultiplier_cdf (x : ℝ) :
    lightMultiplier {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x) := by
  rw [lightMultiplier, Measure.map_apply measurable_lightQuantile
    (measurableSet_le measurable_subtype_coe measurable_const)]
  by_cases hx0 : x ≤ 0
  · have he : lightQuantile ⁻¹' {v : Gap | (v : ℝ) ≤ x} = ∅ := by
      ext u
      simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact not_le.mpr (hx0.trans_lt (lightQuantile u).property.1)
    rw [he, measure_empty]
    simp [lightCDF, hx0]
  have hx : 0 < x := lt_of_not_ge hx0
  by_cases hxq : x < 1/4
  · let y : ℝ := 2*exp (-(1/(2*x^2)))
    have hy0 : 0 ≤ y := by dsimp [y]; positivity
    have hy1 : y ≤ 1 := by
      have hxx : x^2 < (1/16 : ℝ) := by nlinarith
      have ha : (8 : ℝ) ≤ 1/(2*x^2) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
      have hl : log 2 ≤ 1/(2*x^2) := by
        have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at hlog
        linarith
      have he : (2 : ℝ) ≤ exp (1/(2*x^2)) := by
        calc
          _ = exp (log 2) := (exp_log (by norm_num)).symm
          _ ≤ _ := exp_le_exp.mpr hl
      dsimp [y]
      rw [exp_neg, ← div_eq_mul_inv, div_le_one (exp_pos _)]
      exact he
    have hs : lightQuantile ⁻¹' {v : Gap | (v : ℝ) ≤ x} =ᵐ[volume]
        Iic (⟨y, hy0, hy1⟩ : I) := by
      have hu0 : ∀ᵐ (u : I) ∂volume, u ≠ 0 := by
        rw [ae_iff]
        simp
      filter_upwards [hu0] with u hu
      have hupos : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (by
        intro he
        apply hu
        exact Subtype.ext he.symm)
      simp only [mem_preimage, mem_ofPred_eq, lightQuantile_le_iff u hx hxq, hupos, true_and,
        mem_Iic]
      rfl
    rw [measure_congr hs, unitInterval.volume_Iic]
    simp only [lightCDF, hx0, ite_false, hxq, ite_true]
    rfl
  · have he : lightQuantile ⁻¹' {v : Gap | (v : ℝ) ≤ x} = univ := by
      ext u
      simp only [mem_preimage, mem_ofPred_eq, mem_univ, iff_true]
      exact (lightQuantile_le_quarter u).trans (le_of_not_gt hxq)
    rw [he, measure_univ]
    rw [lightCDF, ite_eq_right hx0, ite_eq_right hxq, ENNReal.ofReal_one]

/-- A3 with a constructed multiplier law, rather than a CDF-existence assumption. -/
theorem selection_lightMultiplier (μ : Measure Gap) [IsFiniteMeasure μ] (ρ B : ℝ) :
    selection ((μ.prod lightMultiplier).map lightGap) ρ B ≤ 32*selection μ ρ B :=
  selection_light_contraction μ lightMultiplier lightMultiplier_cdf ρ B

end ThresholdHC.ArbitraryLawAdaptation
