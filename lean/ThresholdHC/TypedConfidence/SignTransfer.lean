import ThresholdHC.TypedConfidence.StoppedTransfer

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.TypedConfidence
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceTransfer

/-- Bernoulli parameter law of one component's known gaps and hidden signs. -/
def signParameterLaw (μ : Measure Gap) (q : SignLaw) : Measure unitInterval :=
  populationParameterLaw μ (gapParameter false) (gapParameter true) (signUnit q)

instance signParameterLaw_probability (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    IsProbabilityMeasure (signParameterLaw μ q) :=
  populationParameterLaw_probability μ _ _ _ (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit q)

theorem signParameterLaw_quarter (μ : Measure Gap) [IsProbabilityMeasure μ] (q r : SignLaw) :
    signParameterLaw μ (smoothedSign q r) = quarterMix (signParameterLaw μ q) (signParameterLaw μ r) := by
  exact population_parameter_quarter μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r)
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q) (measurable_signUnit r)

/-- The selected-type 16/3 transfer holds through unbounded stopping. A label
may have any known gap law, and every revisit retains that label's sign and gap. -/
theorem stopped_typed_null_work_kl {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (μ : ℕ → Measure Gap) [∀ i, IsProbabilityMeasure (μ i)] (q r : ℕ → SignLaw)
    (hqhalf : ∀ i d, (q i).val d ≤ 1/2) (hrhalf : ∀ i d, (r i).val d ≤ 1/2)
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun u => pol u xs))
    (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hlocal : ∀ i, LocalNullWorkBound (μ i) (gapParameter false) (gapParameter true)
      (signUnit (q i)) (signUnit (r i)) K)
    (hw : (∫⁻ z, totalProcessWork z.2
      ∂parameterExperimentLaw ν (fun i => signParameterLaw (μ i) (smoothedSign (q i) (r i))) pol) ≤ ENNReal.ofReal B)
    (hw' : (∫⁻ z, totalProcessWork z.2
      ∂parameterExperimentLaw ν (fun i => signParameterLaw (μ i) (smoothedSign (r i) (q i))) pol) < ∞) :
    klDiv (parameterExperimentLaw ν (fun i => signParameterLaw (μ i) (smoothedSign (q i) (r i))) pol)
      (parameterExperimentLaw ν (fun i => signParameterLaw (μ i) (smoothedSign (r i) (q i))) pol) ≤
      ENNReal.ofReal ((16/3)*K*B) := by
  simp_rw [signParameterLaw_quarter] at hw hw' ⊢
  rw [show (16/3:ℝ)*K = (8/3)*(2*K) by ring]
  apply stopped_parameter_reference_kl ν (fun i => signParameterLaw (μ i) (q i))
    (fun i => signParameterLaw (μ i) (r i)) pol hp (2*K) B (by positivity) hB _ hw hw'
  intro i
  exact parameter_reference_of_null (μ i) _ _ _ _ (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit (q i)) (measurable_signUnit (r i))
    (hqhalf i) (hrhalf i) hK (hlocal i)

end ThresholdHC.TypedConfidence
