import ThresholdHC.ContinuousObserved.NormalizationGeometry
import ThresholdHC.ContinuousObserved.UniformReal

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier6

theorem measurable_normalizedGap : Measurable normalizedGap := by
  unfold normalizedGap
  fun_prop

theorem measurable_inverseSlope : Measurable inverseSlope := by
  unfold inverseSlope
  fun_prop

def normalizedDensity (z : ℝ) : ℝ :=
  normalizedSupport.indicator (fun z => 4 * inverseSlope z) z

theorem measurable_normalizedDensity : Measurable normalizedDensity :=
  (measurable_const.mul measurable_inverseSlope).indicator measurableSet_Ioc

theorem normalizedDensity_bounds (z : ℝ) : 0 ≤ normalizedDensity z ∧ normalizedDensity z ≤ 2 := by
  by_cases hz : z ∈ normalizedSupport
  · simp only [normalizedDensity,indicator_of_mem hz]
    have hp := inverseSlope_pos z
    have hb := inverseSlope_le z
    constructor <;> linarith
  · simp only [normalizedDensity,indicator_of_notMem hz]
    norm_num

/-- The normalized conditional magnitude has an explicit globally bounded
density, uniformly over every sign pattern and cell construction. -/
theorem normalizedGap_density :
    uniformGaps.map (fun d : Gap => normalizedGap d) =
      volume.withDensity (fun z => ENNReal.ofReal (normalizedDensity z)) := by
  change uniformGaps.map (normalizedGap ∘ fun d : Gap => (d : ℝ)) = _
  rw [← Measure.map_map measurable_normalizedGap measurable_subtype_coe,uniformGaps_real_law]
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply measurable_normalizedGap hS,Measure.smul_apply,
    Measure.restrict_apply (measurable_normalizedGap hS),normalized_preimage]
  have hi := lintegral_deriv_eq_volume_image_of_monotoneOn (hS.inter measurableSet_Ioc)
    (fun z _ => (hasDerivAt_inverseNormalizedGap z).hasDerivWithinAt)
    (inverseNormalizedGap_strictMono.monotone.monotoneOn (s := S ∩ normalizedSupport))
  change (∫⁻ z in S ∩ normalizedSupport, ENNReal.ofReal (inverseSlope z)) =
    volume (inverseNormalizedGap '' (S ∩ normalizedSupport)) at hi
  change 4 * volume (inverseNormalizedGap '' (S ∩ normalizedSupport)) = _
  rw [← hi,withDensity_apply _ hS]
  have hf : (fun z => ENNReal.ofReal (normalizedDensity z)) =
      normalizedSupport.indicator (fun z => ENNReal.ofReal (4 * inverseSlope z)) := by
    funext z
    by_cases hz : z ∈ normalizedSupport <;> simp [normalizedDensity,hz]
  have hs : MeasurableSet normalizedSupport := measurableSet_Ioc
  rw [hf,lintegral_indicator hs,Measure.restrict_restrict hs]
  rw [inter_comm normalizedSupport S]
  simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [lintegral_const_mul _ measurable_inverseSlope.ennreal_ofReal]

end ThresholdHC.ContinuousObserved
