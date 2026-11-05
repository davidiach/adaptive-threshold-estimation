import ThresholdHC.AdditiveConfidence.Full
import ThresholdHC.CriticalEntropy.SeededPopulationTransfer

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.RMSLocalization
open ThresholdHC.CriticalEntropy ThresholdHC.ConfidenceTransfer

/-- The original countable-label creation experiment charges each local
Hellinger loss to work under the same midpoint population. -/
theorem creation_null_hellinger {D : Type} [MeasurableSpace D] (μ : Measure D)
    [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (hqhalf : ∀ x, (q x : ℝ) ≤ 1/2) (hrhalf : ∀ x, (r x : ℝ) ≤ 1/2)
    (d : D → ℝ) (hdm : Measurable d) (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x) (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option ℕ) (n : ℕ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hlocal : LocalNullWorkBound μ p₀ p₁ q r κ) :
    let w := fun (u : D → unitInterval) =>
      creationPopulationWeight (n := n) μ pol d (fun x => (u x : ℝ))
    1-realFiniteAffinity (w q) (w r) ≤
      2*κ*∑ z, w (midpointPrior q r) z*ThresholdHC.workOf z := by
  let cpol := ThresholdHC.Tier5.capPolicy (ThresholdHC.Tier5.coinCap n pol) pol
  let s := midpointPrior q r
  have hs := measurable_midpointPrior q r hq hr
  let : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ s) :=
    populationParameterLaw_probability μ p₀ p₁ s h₀ h₁ hs
  let ν := Measure.pi (fun _ : Fin (ThresholdHC.Tier5.coinCap n pol) =>
    parameterTapeLaw (populationParameterLaw μ p₀ p₁ s))
  have h := finite_population_transfer μ p₀ p₁ q r h₀ h₁ hq hr hqhalf hrhalf d hdm hd
    h₀d h₁d cpol 1 κ (by norm_num) hκ (n := n) (fun i => by
      simpa only [mul_one] using hlocal ν (localSimulationProcedure i n cpol)
        n (localSimulationProcedure_capped i n cpol))
  rw [finitePopulation_work_real μ _ _ _ h₀ h₁ hs d hdm hd h₀d h₁d cpol] at h
  have he (u : D → unitInterval) (hu : Measurable u) :
      creationPopulationWeight (n := n) μ pol d (fun x => (u x : ℝ)) =
        finitePopulationWeight μ cpol d (fun _ x => (u x : ℝ)) := funext
          (creationPopulationWeight_eq_finite μ pol d _ hdm (measurable_subtype_coe.comp hu))
  dsimp only
  rw [he q hq,he r hr,he (midpointPrior q r) hs]
  simpa only [mul_one] using h

end ThresholdHC.RMSLocalization
