import ThresholdHC.OracleLower.Specification
import ThresholdHC.Tier6.Process

noncomputable section
open MeasureTheory
namespace ThresholdHC.OracleLower
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6

theorem oracle_realization : OracleRealizationStatement := by
  intro R _ A q
  refine ⟨inferInstance, ?_⟩
  exact creationProcessLaw_realizes A.randomLaw A.policy
    (fun r i => A.gap r i) (fun r i => q.val (A.gap r i))
    A.policy_measurable (fun i => measurable_subtype_coe.comp (A.gap_measurable i))
    (fun i => q.property.1.comp (A.gap_measurable i))
    (fun r i => ⟨(A.gap r i).property.1.le,(A.gap r i).property.2⟩)
    (fun r i => q.property.2 (A.gap r i))

/-- The old hidden-magnitude experiment embeds without any change to its law. -/
def hiddenOracle {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) : OracleEstimator (PopulationSeed R) where
  randomLaw := populationSeedLaw μ A
  probability := inferInstance
  gap := fun r i => r.2 i
  gap_measurable := fun i => (measurable_pi_apply i).comp measurable_snd
  policy := populationPolicy A
  policy_measurable := measurable_populationPolicy A
  output := populationOutput A
  output_measurable := measurable_populationOutput A

theorem hiddenOracle_law {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    oracleLaw (hiddenOracle μ A) q = experimentLaw μ A q := rfl

theorem hiddenOracle_budget {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (B : ℝ) :
    OracleBudget (hiddenOracle μ A) B ↔ UniformBudget μ A B := Iff.rfl

theorem hiddenOracle_risk {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) :
    oracleRisk μ (hiddenOracle μ A) = maximalRMSRisk μ A := rfl

theorem hiddenOracle_confidence {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (r δ : ℝ) :
    OracleConfidence μ (hiddenOracle μ A) r δ ↔ Confidence.UniformConfidence μ A r δ := Iff.rfl

end ThresholdHC.OracleLower
