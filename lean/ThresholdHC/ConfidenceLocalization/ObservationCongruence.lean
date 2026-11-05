import ThresholdHC.ConfidenceLocalization.StatisticGeometry

noncomputable section
open MeasureTheory
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

theorem affinity_symm {X : Type} [MeasurableSpace X] (P Q : Measure X) :
    hellingerAffinity P Q = hellingerAffinity Q P := by
  unfold hellingerAffinity
  rw [add_comm P Q]
  apply lintegral_congr
  intro x
  rw [mul_comm]

theorem capped_affinity_congr_ae {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q₁ q₂ r₁ r₂ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq₁ : Measurable q₁) (hq₂ : Measurable q₂) (hr₁ : Measurable r₁) (hr₂ : Measurable r₂)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (heq : (fun d => (q₁ d : ℝ)) =ᵐ[μ] (fun d => (q₂ d : ℝ)))
    (her : (fun d => (r₁ d : ℝ)) =ᵐ[μ] (fun d => (r₂ d : ℝ))) :
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q₁ A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r₁ A m)).toReal =
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q₂ A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r₂ A m)).toReal := by
  have hq := congrArg (fun v => fun i => v (some i))
    (cappedObservationVector_congr_ae μ ν p₀ p₁ q₁ q₂ h₀ h₁ hq₁ hq₂ A m hcap heq)
  have hr := congrArg (fun v => fun i => v (some i))
    (cappedObservationVector_congr_ae μ ν p₀ p₁ r₁ r₂ h₀ h₁ hr₁ hr₂ A m hcap her)
  change (fun i => (cappedStatisticLaw μ ν p₀ p₁ q₁ A m).real {i}) =
    (fun i => (cappedStatisticLaw μ ν p₀ p₁ q₂ A m).real {i}) at hq
  change (fun i => (cappedStatisticLaw μ ν p₀ p₁ r₁ A m).real {i}) =
    (fun i => (cappedStatisticLaw μ ν p₀ p₁ r₂ A m).real {i}) at hr
  rw [capped_affinity_real μ ν p₀ p₁ q₁ r₁ h₀ h₁ hq₁ hr₁ A m hcap,
    capped_affinity_real μ ν p₀ p₁ q₂ r₂ h₀ h₁ hq₂ hr₂ A m hcap,hq,hr]

end ThresholdHC.ConfidenceLocalization
