import ThresholdHC.TypedConfidence.FiniteTransfer
import ThresholdHC.TypedConfidence.PriorMixture
import ThresholdHC.ConfidenceTransfer.Creation

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.TypedConfidence
open ThresholdHC.CriticalEntropy ThresholdHC.ConfidenceTransfer

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => trivial⟩

/-- Uniform null-work bounds transfer to heterogeneous populations with coefficient
16/3. The policy freely chooses which persistent label to observe next. -/
theorem finite_typed_null_work_kl {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Fin m → Measure D) [∀ i, IsProbabilityMeasure (μ i)]
    (p₀ p₁ q r : Fin m → D → unitInterval)
    (h₀ : ∀ i, Measurable (p₀ i)) (h₁ : ∀ i, Measurable (p₁ i))
    (hq : ∀ i, Measurable (q i)) (hr : ∀ i, Measurable (r i))
    (hqhalf : ∀ i x, (q i x : ℝ) ≤ 1/2) (hrhalf : ∀ i x, (r i x : ℝ) ≤ 1/2)
    (pol : List Bool → Option (Fin m)) (K : ℝ) (hK : 0 ≤ K)
    (hlocal : ∀ i, LocalNullWorkBound (μ i) (p₀ i) (p₁ i) (q i) (r i) K) :
    let ref := fun i => populationParameterLaw (μ i) (p₀ i) (p₁ i) (quarterPrior (q i) (r i))
    let alt := fun i => populationParameterLaw (μ i) (p₀ i) (p₁ i) (quarterPrior (r i) (q i))
    klDiv (parameterWordLaw ref pol n) (parameterWordLaw alt pol n) ≤
      ENNReal.ofReal ((16/3)*K*(parameterExpectedWork ref pol n).toReal) := by
  let κ := fun i => populationParameterLaw (μ i) (p₀ i) (p₁ i) (q i)
  let τ := fun i => populationParameterLaw (μ i) (p₀ i) (p₁ i) (r i)
  let (i : Fin m) : IsProbabilityMeasure (κ i) :=
    populationParameterLaw_probability (μ i) _ _ _ (h₀ i) (h₁ i) (hq i)
  let (i : Fin m) : IsProbabilityMeasure (τ i) :=
    populationParameterLaw_probability (μ i) _ _ _ (h₀ i) (h₁ i) (hr i)
  let ref := fun i => quarterMix (κ i) (τ i)
  let ν := Measure.pi (fun i => parameterTapeLaw (ref i))
  have he : (fun i => populationParameterLaw (μ i) (p₀ i) (p₁ i) (quarterPrior (q i) (r i))) = ref :=
    funext (fun i => population_parameter_quarter (μ i) _ _ _ _ (h₀ i) (h₁ i) (hq i) (hr i))
  have he' : (fun i => populationParameterLaw (μ i) (p₀ i) (p₁ i) (quarterPrior (r i) (q i))) =
      (fun i => quarterMix (τ i) (κ i)) :=
    funext (fun i => population_parameter_quarter (μ i) _ _ _ _ (h₀ i) (h₁ i) (hr i) (hq i))
  dsimp only
  rw [he,he',show (16/3:ℝ)*K = (8/3)*(2*K) by ring]
  apply finite_parameter_reference_kl κ τ pol (2*K) (by positivity)
  dsimp only
  intro i
  have h := local_reference_of_null (μ i) (p₀ i) (p₁ i) (q i) (r i)
    (h₀ i) (h₁ i) (hq i) (hr i) (hqhalf i) (hrhalf i) hK (hlocal i)
    ν (localSimulationProcedure i n pol) n (localSimulationProcedure_capped i n pol)
  rw [populationInput_capped_law (μ i) ν _ _ _ (h₀ i) (h₁ i) (hq i),
    populationInput_capped_law (μ i) ν _ _ _ (h₀ i) (h₁ i) (hr i),
    populationInput_work (μ i) ν _ _ _ (h₀ i) (h₁ i) (measurable_quarterPrior _ _ (hq i) (hr i)),
    population_parameter_quarter (μ i) _ _ _ _ (h₀ i) (h₁ i) (hq i) (hr i)] at h
  exact h

end ThresholdHC.TypedConfidence
