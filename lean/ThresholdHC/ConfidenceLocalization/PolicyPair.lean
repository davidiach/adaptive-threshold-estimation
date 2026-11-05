import ThresholdHC.ConfidenceLocalization.PowerPair
import ThresholdHC.ConfidenceLocalization.RegularizedGeometry
import ThresholdHC.ConfidenceLocalization.ObservationCongruence

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

/-- One capped policy admits a separated half-regularized pair satisfying the
quantitative Hellinger/null-work constraint, including zero null work. -/
theorem regularized_policy_constraint {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/4)
    {b J δ : ℝ} (hJ : 0 < J) (hδ : 0 < δ) (hδb : δ ≤ b/3)
    (hobs : NullVarianceObstruction μ p₀ p₁ (c : ℝ) b J) :
    ∃ z ∈ populationPairSet μ (c : ℝ) (2*δ),
      (1-(hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ z.1) (fun _ => c)) A m)
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ z.2) (fun _ => c)) A m)).toReal)*J ≤
        42*δ^2*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal := by
  have hb := obstruction_bias_lt_half μ p₀ p₁ hJ hobs
  let K := populationPairSet μ (c : ℝ) (2*δ)
  obtain ⟨hKc,_⟩ := populationPairSet_compact_convex μ (c : ℝ) (2*δ)
  have hKn : K.Nonempty := populationPairSet_nonempty μ (c : ℝ) (2*δ) (by positivity)
    (by linarith) (by linarith)
  obtain ⟨H,hHc,_,hH⟩ := regularized_pair_geometry μ ν p₀ p₁ h₀ h₁ A m hcap c
  have hRange (z) (hz : z ∈ K) : H z ∈ Icc 0 1 := (hH z.1 hz.1.1 z.2 hz.1.2).2
  let w := (populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal
  have hw : 0 ≤ w := ENNReal.toReal_nonneg
  have hpairs : ∀ n : ℕ, (n : ℝ)*((9/2)*δ^2*w) < J →
      ∃ z ∈ K, 1/2 ≤ (1-H z)^n := by
    intro n hn
    obtain ⟨q,r,hq,hr,hgap,hpow⟩ := regularized_policy_power_pair μ ν p₀ p₁ h₀ h₁ A m hcap
      c hc0 (by linarith) (δ/2) (by positivity) n b J hobs (by linarith) (by
        change (18*(n : ℝ)*(δ/2)^2)*w < J
        convert hn using 1
        ring)
    have hgapRaw : 2*δ ≤ (∫ d, (q d : ℝ) ∂μ)-(∫ d, (r d : ℝ) ∂μ) := by
      rw [midpointPrior_integral μ q _ hq.1 measurable_const,
        midpointPrior_integral μ r _ hr.1 measurable_const] at hgap
      linarith
    obtain ⟨z,hz,her,heq⟩ := populationPairSet_covers_priors μ (c : ℝ) (2*δ) q r hq hr hgapRaw
    refine ⟨z,hz,?_⟩
    rw [(hH z.1 hz.1.1 z.2 hz.1.2).1,sub_sub_cancel]
    have hreg (u v : D → unitInterval)
        (he : (fun d => (u d : ℝ)) =ᵐ[μ] (fun d => (v d : ℝ))) :
        (fun d => (midpointPrior u (fun _ => c) d : ℝ)) =ᵐ[μ]
          (fun d => (midpointPrior v (fun _ => c) d : ℝ)) :=
      he.mono (fun d hd => congrArg (fun a : ℝ => (a+(c : ℝ))/2) hd)
    rw [capped_affinity_congr_ae μ ν p₀ p₁
      (midpointPrior (populationDualPrior μ z.1) (fun _ => c)) (midpointPrior r (fun _ => c))
      (midpointPrior (populationDualPrior μ z.2) (fun _ => c)) (midpointPrior q (fun _ => c))
      h₀ h₁
      (measurable_midpointPrior _ _ (populationDualPrior_measurable μ z.1) measurable_const)
      (measurable_midpointPrior _ _ hr.1 measurable_const)
      (measurable_midpointPrior _ _ (populationDualPrior_measurable μ z.2) measurable_const)
      (measurable_midpointPrior _ _ hq.1 measurable_const) A m hcap
      (hreg _ _ her) (hreg _ _ heq),affinity_symm]
    exact hpow
  obtain ⟨z,hz,hbound⟩ := compact_power_pair_bound K hKn hKc H hHc hRange J ((9/2)*δ^2*w)
    hJ (by positivity) hpairs
  refine ⟨z,hz,?_⟩
  rw [← (hH z.1 hz.1.1 z.2 hz.1.2).1]
  change H z*J ≤ 42*δ^2*w
  nlinarith [mul_nonneg (sq_nonneg δ) hw]

end ThresholdHC.ConfidenceLocalization
