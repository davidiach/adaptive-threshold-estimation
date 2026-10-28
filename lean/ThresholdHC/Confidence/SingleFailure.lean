import ThresholdHC.Confidence.Amplification
import ThresholdHC.BlindUpper.BatchRealization

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.Confidence
open ThresholdHC.Tier6 ThresholdHC.BlindUpper

theorem failure_of_second_moment {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (θ w : ℝ) (hw : 0 < w)
    (hsecond : (∫⁻ z, ENNReal.ofReal ((f z-θ)^2) ∂P) ≤ ENNReal.ofReal (12751*w^2)) :
    P {z | 512*w < |f z-θ|} ≤ (1/8 : ℝ≥0∞) := by
  let ε := ENNReal.ofReal ((512*w)^2)
  have hε0 : ε ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hεtop : ε ≠ ∞ := ENNReal.ofReal_ne_top
  have hf' := ((hf.sub_const θ).pow_const 2).ennreal_ofReal
  have hsub : {z | 512*w < |f z-θ|} ⊆ {z | ε ≤ ENNReal.ofReal ((f z-θ)^2)} := by
    intro z hz
    apply ENNReal.ofReal_le_ofReal
    have hs := sq_le_sq₀ (by positivity : 0 ≤ 512*w) (abs_nonneg (f z-θ))
    simpa only [sq_abs] using hs.mpr hz.le
  calc
    _ ≤ P {z | ε ≤ ENNReal.ofReal ((f z-θ)^2)} := measure_mono hsub
    _ ≤ (∫⁻ z, ENNReal.ofReal ((f z-θ)^2) ∂P) / ε :=
      meas_ge_le_lintegral_div hf'.aemeasurable hε0 hεtop
    _ ≤ ENNReal.ofReal (12751*w^2) / ε := ENNReal.div_le_div_right hsecond ε
    _ ≤ 1/8 := by
      apply (ENNReal.div_le_iff hε0 hεtop).mpr
      have he : (1/8 : ℝ≥0∞) = ENNReal.ofReal (1/8 : ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
      rw [he,← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_nonneg w]

theorem cutoffBatch_failure (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (calibrationLaw (callMeasure μ q))
      {z | 512*modulus μ (1/Real.sqrt ((2 : ℝ)^L)) < |cutoffBatchOutput L z-signMean μ q.val|}
      ≤ (1/8 : ℝ≥0∞) :=
  failure_of_second_moment _ _ (measurable_cutoffBatchOutput L) _ _
    (modulus_pos μ (by positivity)) (cutoffBatch_mse L μ q)

end ThresholdHC.Confidence
