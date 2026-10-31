import ThresholdHC.EntropyTailAssembly.BandWeights
import ThresholdHC.EntropyTailUpper.LogSurcharge

/-! Integrating the surcharge uses the original global rarity constraint.
No pointwise or componentwise rarity bound is assumed. -/

noncomputable section
open MeasureTheory Set Real

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6 ThresholdHC.EntropyTailUpper

theorem integrable_signLaw (μ : Measure Gap) [IsFiniteMeasure μ] (q : SignLaw) :
    Integrable q.val μ := by
  apply Integrable.of_bound q.property.1.aestronglyMeasurable 1
  exact ae_of_all _ (fun d => by
    rw [Real.norm_of_nonneg (q.property.2 d).1]
    exact (q.property.2 d).2)

theorem selected_signMean_le {σ μ : Measure Gap} [IsFiniteMeasure μ] (hσ : σ ≤ μ)
    (q : SignLaw) {ρ : ℝ} (hq : ThresholdHC.RareAboveTwo.RarePrior μ ρ q) :
    (∫ d, q.val d ∂σ) ≤ ρ :=
  (integral_mono_measure hσ (ae_of_all _ (fun d => (q.property.2 d).1)) (integrable_signLaw μ q)).trans hq

theorem weighted_log_surcharge_pointwise (q : SignLaw) {z A H ρ : ℝ}
    (hz : 0 ≤ z) (hzρ : z ≤ ρ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hρ : 0 < ρ) (d : Gap) :
    q.val d*(d:ℝ)⁻¹^2*logPlus ((z+A*(d:ℝ)^2+H*(d:ℝ))/ρ) ≤
      log 3*(d:ℝ)⁻¹^2+q.val d*(A/ρ+H^2/(2*ρ^2)) := by
  have hs := mul_le_mul_of_nonneg_left (log_surcharge_bound hz hzρ hA hH hρ d.property.1) (q.property.2 d).1
  have hb := mul_le_mul_of_nonneg_right (q.property.2 d).2
    (mul_nonneg (log_nonneg (by norm_num : (1:ℝ) ≤ 3)) (sq_nonneg ((d:ℝ)⁻¹)))
  nlinarith only [hs, hb]

theorem integrated_log_surcharge (σ : Measure Gap) [IsFiniteMeasure σ] (q : SignLaw)
    (hσ : Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ) {z A H ρ : ℝ}
    (hz : 0 ≤ z) (hzρ : z ≤ ρ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hρ : 0 < ρ)
    (hq : (∫ d, q.val d ∂σ) ≤ ρ) :
    Integrable (fun d : Gap => q.val d*(d:ℝ)⁻¹^2*logPlus ((z+A*(d:ℝ)^2+H*(d:ℝ))/ρ)) σ ∧
    (∫ d : Gap, q.val d*(d:ℝ)⁻¹^2*logPlus ((z+A*(d:ℝ)^2+H*(d:ℝ))/ρ) ∂σ) ≤
      log 3*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)+A+H^2/(2*ρ) := by
  let C := A/ρ+H^2/(2*ρ^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hqi := integrable_signLaw σ q
  have hri : Integrable (fun d : Gap => log 3*(d:ℝ)⁻¹^2+q.val d*C) σ :=
    (hσ.const_mul (log 3)).add (hqi.mul_const C)
  have hpt := weighted_log_surcharge_pointwise q hz hzρ hA hH hρ
  have hki : Integrable (fun d : Gap => q.val d*(d:ℝ)⁻¹^2*logPlus ((z+A*(d:ℝ)^2+H*(d:ℝ))/ρ)) σ := by
    have hqm := q.property.1
    have hm : Measurable (fun d : Gap => q.val d*(d:ℝ)⁻¹^2*logPlus ((z+A*(d:ℝ)^2+H*(d:ℝ))/ρ)) := by
      unfold logPlus
      fun_prop
    apply hri.mono' hm.aestronglyMeasurable
    refine ae_of_all _ (fun d => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (q.property.2 d).1 (sq_nonneg _)) (logPlus_nonneg _))]
    exact hpt d
  refine ⟨hki, ?_⟩
  have h := integral_mono hki hri hpt
  rw [integral_add (hσ.const_mul (log 3)) (hqi.mul_const C), integral_const_mul, integral_mul_const] at h
  have hmass := mul_le_mul_of_nonneg_right hq hC
  have he : ρ*C = A+H^2/(2*ρ) := by dsimp [C]; field_simp [hρ.ne']
  have he' : C*ρ = A+H^2/(2*ρ) := by rw [mul_comm, he]
  nlinarith only [h, hmass, he, he']

end ThresholdHC.EntropyTailAssembly
