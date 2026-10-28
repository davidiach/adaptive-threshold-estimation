import ThresholdHC.CriticalEntropy.PopulationModel

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- The capped global class used by the critical lower bound. The integral
constraint does not impose a pointwise bound by the rarity. -/
def CappedPrior {D : Type} [MeasurableSpace D] (μ : Measure D) (ρ : ℝ)
    (q : D → unitInterval) : Prop :=
  Measurable q ∧ (∀ d, (q d : ℝ) ≤ 1/2) ∧ (∫ d, (q d : ℝ) ∂μ) ≤ ρ

def halfPrior {D : Type} (E : Set D) (d : D) : unitInterval := by
  classical
  exact if d ∈ E then ⟨1/2, by norm_num⟩ else 0

/-- Uniform guarantees on the actual single-coin population experiments. All
nonnegative moments and work retain infinity. -/
structure CappedPopulationGuarantee {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) (ν : Measure R) (p₀ p₁ : D → unitInterval)
    (A : StoppedProcedure R ℝ) (ρ m : ℝ) : Prop where
  moment : ∀ q, CappedPrior μ ρ q → populationSecondMoment μ ν p₀ p₁ q A ≤ ENNReal.ofReal m
  work : ∀ q, CappedPrior μ ρ q → populationExpectedWork μ ν p₀ p₁ q A ≠ ∞
  bias : ∀ q, CappedPrior μ ρ q →
    |populationMean μ ν p₀ p₁ q A - (∫ d, (q d : ℝ) ∂μ)| ≤ ρ/64

def PopulationGoodGap {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (ν : Measure R) (p₀ p₁ : D → unitInterval) (A : StoppedProcedure R ℝ)
    (ρ m : ℝ) (d : D) : Prop :=
  conditionalSecondMoment ν (p₀ d) A ≠ ∞ ∧
  conditionalSecondMoment ν (p₁ d) A ≠ ∞ ∧
  expectedStoppedProcedureWork ν (p₀ d) A ≠ ∞ ∧
  expectedStoppedProcedureWork ν (p₁ d) A ≠ ∞ ∧
  |conditionalMean ν (p₀ d) A| ≤ 1/8 ∧
  5/8 ≤ conditionalMean ν (p₁ d) A ∧
  (conditionalSecondMoment ν (p₀ d) A).toReal ≤ 1/64 ∧
  (conditionalSecondMoment ν (p₁ d) A).toReal ≤ 1/64+2*m/ρ

end ThresholdHC.CriticalEntropy
