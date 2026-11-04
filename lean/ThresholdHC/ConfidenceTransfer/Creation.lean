import ThresholdHC.ConfidenceTransfer.FiniteTransfer
import ThresholdHC.CriticalEntropy.CreationPopulation
import ThresholdHC.CriticalEntropy.PopulationWorkLaw

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceTransfer
open ThresholdHC.CriticalEntropy

/-- A common prior pair controls every capped one-coin policy with any
independent auxiliary randomness. The work law uses the all-negative prior. -/
def LocalNullWorkBound {D : Type} [MeasurableSpace D] (μ : Measure D)
    (p₀ p₁ q r : D → unitInterval) (κ : ℝ) : Prop :=
  ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E] (ν : Measure R)
    [IsProbabilityMeasure ν] (A : StoppedProcedure R E) (N : ℕ), (∀ z, A.stop z ≤ N) →
    1-(hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A N)
      (cappedTranscriptLaw μ ν p₀ p₁ r A N)).toReal ≤
      κ*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal

local instance : MeasurableSpace (Option Bool) := ⊤

theorem creation_null_work_kl {D : Type} [MeasurableSpace D] (μ : Measure D)
    [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (hqhalf : ∀ x, (q x : ℝ) ≤ 1/2) (hrhalf : ∀ x, (r x : ℝ) ≤ 1/2)
    (d : D → ℝ) (hdm : Measurable d) (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x) (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option ℕ) (n : ℕ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hlocal : LocalNullWorkBound μ p₀ p₁ q r κ) :
    let w := fun (u : D → unitInterval) =>
      creationPopulationWeight (n := n) μ pol d (fun x => (u x : ℝ))
    klDiv (finiteWeightMeasure (w (quarterPrior q r))) (finiteWeightMeasure (w (quarterPrior r q))) ≤
      ENNReal.ofReal ((16/3)*κ*∑ z, w (quarterPrior q r) z * ThresholdHC.workOf z) := by
  let cpol := ThresholdHC.Tier5.capPolicy (ThresholdHC.Tier5.coinCap n pol) pol
  let s := quarterPrior q r
  have hs := measurable_quarterPrior q r hq hr
  let : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ s) :=
    populationParameterLaw_probability μ p₀ p₁ s h₀ h₁ hs
  let ν := Measure.pi (fun _ : Fin (ThresholdHC.Tier5.coinCap n pol) =>
    parameterTapeLaw (populationParameterLaw μ p₀ p₁ s))
  have h := finite_null_work_kl μ p₀ p₁ q r h₀ h₁ hq hr hqhalf hrhalf d hdm hd
    h₀d h₁d cpol κ hκ (n := n) (fun i => hlocal ν (localSimulationProcedure i n cpol)
      n (localSimulationProcedure_capped i n cpol))
  rw [finitePopulation_work_real μ _ _ _ h₀ h₁ hs d hdm hd h₀d h₁d cpol] at h
  have he (u : D → unitInterval) (hu : Measurable u) :
      creationPopulationWeight (n := n) μ pol d (fun x => (u x : ℝ)) =
        finitePopulationWeight μ cpol d (fun _ x => (u x : ℝ)) := funext
          (creationPopulationWeight_eq_finite μ pol d _ hdm (measurable_subtype_coe.comp hu))
  dsimp only
  rw [he (quarterPrior q r) hs,he (quarterPrior r q) (measurable_quarterPrior r q hr hq)]
  exact h

end ThresholdHC.ConfidenceTransfer
