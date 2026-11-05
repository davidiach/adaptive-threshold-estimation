import ThresholdHC.TypedConfidence.PriorMixture
import ThresholdHC.ConfidenceTransfer.Creation

noncomputable section
open MeasureTheory
namespace ThresholdHC.TypedConfidence
open ThresholdHC.CriticalEntropy ThresholdHC.ConfidenceTransfer

/-- A single prior pair controls every observable capped one-coin procedure
with independent auxiliary randomness. -/
def ParameterReferenceBound (κ τ : Measure unitInterval) (K : ℝ) : Prop :=
  ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E] (ν : Measure R)
    [IsProbabilityMeasure ν] (A : StoppedProcedure R E) (N : ℕ), (∀ z, A.stop z ≤ N) →
    1-(hellingerAffinity
      ((ν.prod (parameterTapeLaw κ)).map (cappedTranscript A N))
      ((ν.prod (parameterTapeLaw τ)).map (cappedTranscript A N))).toReal ≤
      K*(∫⁻ z, stoppedProcedureWork A z ∂ν.prod (parameterTapeLaw (quarterMix κ τ))).toReal

theorem parameter_reference_of_null {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (hqhalf : ∀ x, (q x : ℝ) ≤ 1/2) (hrhalf : ∀ x, (r x : ℝ) ≤ 1/2)
    {K : ℝ} (hK : 0 ≤ K) (hlocal : LocalNullWorkBound μ p₀ p₁ q r K) :
    ParameterReferenceBound (populationParameterLaw μ p₀ p₁ q)
      (populationParameterLaw μ p₀ p₁ r) (2*K) := by
  intro R E _ _ ν _ A n hn
  have h := local_reference_of_null μ p₀ p₁ q r h₀ h₁ hq hr hqhalf hrhalf hK hlocal ν A n hn
  rw [populationInput_capped_law μ ν _ _ _ h₀ h₁ hq,
    populationInput_capped_law μ ν _ _ _ h₀ h₁ hr,
    populationInput_work μ ν _ _ _ h₀ h₁ (measurable_quarterPrior _ _ hq hr),
    population_parameter_quarter μ _ _ _ _ h₀ h₁ hq hr] at h
  exact h

end ThresholdHC.TypedConfidence
