import ThresholdHC.ConfidenceLocalization.CappedEstimator

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

theorem regularized_affinity_obstruction {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/2)
    (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ)
    (b J : ℝ) (hobs : NullVarianceObstruction μ p₀ p₁ (c : ℝ) b J) (hsmall : 6*ε ≤ b)
    (hsep : ∀ q r : D → unitInterval, CappedPrior μ (c : ℝ) q → CappedPrior μ (c : ℝ) r →
      1/2 ≤ ((hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior q (fun _ => c)) A m)
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior r (fun _ => c)) A m)).toReal)^n →
      (∫ d, (midpointPrior q (fun _ => c) d : ℝ) ∂μ)-
        (∫ d, (midpointPrior r (fun _ => c) d : ℝ) ∂μ) < 2*ε) :
    J ≤ (18*(n : ℝ)*ε^2)*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal := by
  obtain ⟨Z,hstop,hbounded,hZ⟩ := regularized_capped_estimator μ ν p₀ p₁ h₀ h₁ A m hcap
    c hc0 hc ε hε n hsep
  have hzcap (z) : Z.stop z ≤ m := by rw [hstop]; exact hcap z
  have h := hobs ν Z m hzcap hbounded (18*(n : ℝ)*ε^2) (by positivity)
    (fun q hq => (hZ q hq).2.2.1) (fun q hq => (hZ q hq).2.1.trans hsmall)
  have hzero := cappedPrior_const μ (c : ℝ) 0 (by norm_num) (by simpa using hc0.le)
  rw [(hZ _ hzero).2.2.2] at h
  exact h

theorem regularized_policy_power_pair {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/2)
    (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ)
    (b J : ℝ) (hobs : NullVarianceObstruction μ p₀ p₁ (c : ℝ) b J) (hsmall : 6*ε ≤ b)
    (hlt : (18*(n : ℝ)*ε^2)*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal < J) :
    ∃ q r : D → unitInterval, CappedPrior μ (c : ℝ) q ∧ CappedPrior μ (c : ℝ) r ∧
      2*ε ≤ (∫ d, (midpointPrior q (fun _ => c) d : ℝ) ∂μ)-
        (∫ d, (midpointPrior r (fun _ => c) d : ℝ) ∂μ) ∧
      1/2 ≤ ((hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior q (fun _ => c)) A m)
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior r (fun _ => c)) A m)).toReal)^n := by
  by_contra hn
  have hsep : ∀ q r : D → unitInterval, CappedPrior μ (c : ℝ) q → CappedPrior μ (c : ℝ) r →
      1/2 ≤ ((hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior q (fun _ => c)) A m)
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior r (fun _ => c)) A m)).toReal)^n →
      (∫ d, (midpointPrior q (fun _ => c) d : ℝ) ∂μ)-
        (∫ d, (midpointPrior r (fun _ => c) d : ℝ) ∂μ) < 2*ε := by
    intro q r hq hr ha
    apply lt_of_not_ge
    intro hgap
    exact hn ⟨q,r,hq,hr,hgap,ha⟩
  exact (not_lt_of_ge (regularized_affinity_obstruction μ ν p₀ p₁ h₀ h₁ A m hcap c hc0 hc ε hε n
    b J hobs hsmall hsep)) hlt

end ThresholdHC.ConfidenceLocalization
