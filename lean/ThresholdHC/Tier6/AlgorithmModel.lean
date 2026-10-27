import ThresholdHC.Tier6.AlgorithmCore
import ThresholdHC.Tier6.ProcessModel

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Tier6
open ThresholdHC.Tier3 ThresholdHC.Tier5

def experimentLaw {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    Measure (PopulationSeed R × ProcessTape) :=
  creationProcessLaw (populationSeedLaw μ A) (populationPolicy A)
    populationGap (populationPrior q) (measurable_populationPolicy A)
    measurable_populationGap (measurable_populationPrior q)
    populationGap_range (populationPrior_range q)

instance experimentLaw_probability {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    IsProbabilityMeasure (experimentLaw μ A q) := by
  unfold experimentLaw
  infer_instance

def expectedWork {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) : ℝ≥0∞ :=
  ∫⁻ z, totalProcessWork z.2 ∂experimentLaw μ A q

def UniformBudget {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (B : ℝ) : Prop :=
  ∀ q : SignLaw, expectedWork μ A q ≤ ENNReal.ofReal B

def maximalRMSRisk {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) : ℝ≥0∞ :=
  ⨆ q : SignLaw, rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val)

/-- Minimax risk over arbitrary measurable random-seed spaces and all adaptive
policies with a uniform expected-work budget. Infinite squared error is retained.
-/
def minimaxRisk (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    UniformBudget μ A B ∧ r = maximalRMSRisk μ A}

def PopulationRealizationStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw),
    IsProbabilityMeasure (experimentLaw μ A q) ∧
    RealizesCreationPrefixes (populationSeedLaw μ A) (experimentLaw μ A q)
      Prod.fst Prod.snd (populationPolicy A) populationGap (populationPrior q)

def AlgorithmLowerBoundStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (B : ℝ), 1 ≤ B → UniformBudget μ A B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 64) ≤ maximalRMSRisk μ A

def MinimaxLowerBoundStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 64) ≤ minimaxRisk μ B

/-- An immediate-stopping estimator makes the budget class nonempty. -/
def BudgetClassNonemptyStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 0 ≤ B →
    ∃ (A : AdaptiveEstimator Unit), UniformBudget μ A B

end ThresholdHC.Tier6
