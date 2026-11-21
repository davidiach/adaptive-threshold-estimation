import ThresholdHC.LatentThreshold.Specification

/-! The threshold identity. The latent law integrates `F` to
`∫ q(d) F(1/2+d) + (1-q(d)) F(1/2-d) dμ`; for the indicator of `P > 1/2` the
integrand is `q(d)`, since `1/2 + d > 1/2 ≥ 1/2 - d`. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.LatentThreshold
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.SmoothDensity

/-- The latent parameter law of a probability gap law is a probability law. -/
theorem latentLaw_isProbability (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    IsProbabilityMeasure (latentLaw μ q) :=
  populationParameterLaw_probability μ _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)

/-- The latent law gives `P > 1/2` probability `θ`. -/
theorem threshold_mean_eq (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    signMean μ q.val = (latentLaw μ q).real {p : unitInterval | (1/2 : ℝ) < p} := by
  let S : Set unitInterval := {p | (1/2 : ℝ) < p}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_subtype_coe
  let F := S.indicator (fun _ => (1 : ℝ))
  have hm : Measurable F := measurable_const.indicator hS
  have hb (p : unitInterval) : |F p| ≤ 1 := by
    dsimp [F, Set.indicator]; split <;> norm_num
  have he := populationParameterLaw_integral μ (gapParameter false) (gapParameter true) (signUnit q)
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q) F hm 1 hb
  have hpair (d : Gap) : (signUnit q d : ℝ) * F (gapParameter true d) +
      (1 - (signUnit q d : ℝ)) * F (gapParameter false d) = q.val d := by
    have hp : gapParameter true d ∈ S := by
      change (1/2 : ℝ) < (gapParameter true d : ℝ)
      simp [gapParameter]; linarith [d.property.1]
    have hn : gapParameter false d ∉ S := by
      change ¬ (1/2 : ℝ) < (gapParameter false d : ℝ)
      simp [gapParameter]; linarith [d.property.1]
    dsimp only [F]
    rw [Set.indicator_of_mem hp, Set.indicator_of_notMem hn]
    simp [signUnit]
  simp_rw [hpair] at he
  have : IsProbabilityMeasure (latentLaw μ q) := latentLaw_isProbability μ q
  rw [signMean, ← he]
  change ∫ p, S.indicator (fun _ => (1 : ℝ)) p ∂latentLaw μ q = _
  rw [integral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]

end ThresholdHC.LatentThreshold
