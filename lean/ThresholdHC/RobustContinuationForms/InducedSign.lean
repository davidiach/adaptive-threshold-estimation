import ThresholdHC.RobustContinuationForms.Specification

/-! The induced reference sign allocation.

The sign law `q` at the true gap is carried to the reference gap: the measure
`B ↦ ∫_{D₀ ∈ B} q(D₁) dπ` lies below the reference marginal, and its
Radon-Nikodym derivative, truncated at one, is the allocation. Its density
identity gives the integral identity for every measurable `F`; with `F = 1`
and the split of the true law it gives the positive fraction, and the global
rarity budget of the coupled part gives admissibility. The argument follows
`ContinuousObserved.conditionalSign`. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.RobustContinuationForms
open ThresholdHC.Tier6 (Gap SignLaw AdaptiveEstimator signMean)
open ThresholdHC.RareAboveTwo ThresholdHC.RobustContinuation

/-- The carried sign measure lies below the reference marginal. -/
theorem inducedSignMeasure_le_marginal (π : Measure (Gap × Gap)) (q : SignLaw) :
    inducedSignMeasure π q ≤ π.map Prod.fst := by
  unfold inducedSignMeasure
  refine Measure.map_mono ?_ measurable_fst
  calc π.withDensity (fun z => ENNReal.ofReal (q.val z.2)) ≤ π.withDensity 1 :=
        withDensity_mono (ae_of_all _ fun z =>
          ENNReal.ofReal_le_one.mpr (q.property.2 z.2).2)
    _ = π := withDensity_one

/-- The allocation is a density of the carried sign measure with respect to
the reference marginal. -/
theorem inducedSignLaw_density (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (q : SignLaw) :
    (π.map Prod.fst).withDensity (fun d => ENNReal.ofReal ((inducedSignLaw π q).val d)) =
      inducedSignMeasure π q := by
  have hle := inducedSignMeasure_le_marginal π q
  have : IsFiniteMeasure (inducedSignMeasure π q) := isFiniteMeasure_of_le _ hle
  have he : (fun d => ENNReal.ofReal ((inducedSignLaw π q).val d)) =ᵐ[π.map Prod.fst]
      (inducedSignMeasure π q).rnDeriv (π.map Prod.fst) := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hle] with d hd
    have hr : ((inducedSignMeasure π q).rnDeriv (π.map Prod.fst) d).toReal ≤ 1 := by
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) hd
    change ENNReal.ofReal (min 1 ((inducedSignMeasure π q).rnDeriv (π.map Prod.fst) d).toReal) = _
    rw [min_eq_right hr, ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp) hd)]
  rw [withDensity_congr_ae he]
  exact Measure.withDensity_rnDeriv_eq _ _ hle.absolutelyContinuous

/-- The allocation integrates every measurable function of the reference gap
as the sign at the true gap does. -/
theorem inducedSignLaw_integral (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (q : SignLaw)
    (F : Gap → ℝ) (hF : Measurable F) :
    (∫ z, q.val z.2 * F z.1 ∂π) =
      ∫ d, (inducedSignLaw π q).val d * F d ∂(π.map Prod.fst) := by
  have hm1 : Measurable (fun z : Gap × Gap => ENNReal.ofReal (q.val z.2)) :=
    ENNReal.measurable_ofReal.comp (q.property.1.comp measurable_snd)
  have h1 := integral_withDensity_eq_integral_toReal_smul (μ := π) hm1
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) (fun z => F z.1)
  simp_rw [ENNReal.toReal_ofReal (q.property.2 _).1, smul_eq_mul] at h1
  have hm2 : Measurable (fun d => ENNReal.ofReal ((inducedSignLaw π q).val d)) :=
    ENNReal.measurable_ofReal.comp (inducedSignLaw π q).property.1
  have h2 := integral_withDensity_eq_integral_toReal_smul (μ := π.map Prod.fst) hm2
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) F
  simp_rw [ENNReal.toReal_ofReal ((inducedSignLaw π q).property.2 _).1, smul_eq_mul] at h2
  rw [inducedSignLaw_density π q] at h2
  rw [← h1, ← h2, inducedSignMeasure,
    integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable]

/-- The induced reference sign allocation. -/
theorem induced_sign_allocation_proof : InducedSignAllocationStatement := by
  intro η _ z₀ ρ _ hz1 π μ₀ μ _ _ _ href hμ q
  have hc : 0 < 1 - z₀ := by linarith
  have hF : ∀ F : Gap → ℝ, Measurable F →
      (∫ z, q.val z.2 * F z.1 ∂π) = (1 - z₀) * ∫ d, (inducedSignLaw π q).val d * F d ∂η := by
    intro F hFm
    rw [inducedSignLaw_integral π q F hFm, href, integral_smul_measure,
      ENNReal.toReal_ofReal hc.le, smul_eq_mul]
  have h1 := hF (fun _ => 1) measurable_const
  simp only [mul_one] at h1
  have hmass : (1 - z₀) * signMean η (inducedSignLaw π q).val + (∫ d, q.val d ∂μ₀) =
      signMean μ q.val := by
    rw [signMean, ← h1]
    exact coupling_sign_mass π μ₀ μ hμ q
  refine ⟨hF, hmass, fun hq => ⟨?_, ?_⟩⟩
  · rw [hmass]
    exact hq
  · have hb := coupling_sign_budget π μ₀ μ hμ q hq
    rw [h1] at hb
    change signMean η (inducedSignLaw π q).val ≤ ρ / (1 - z₀)
    rw [le_div_iff₀ hc, mul_comm]
    exact hb

end ThresholdHC.RobustContinuationForms
