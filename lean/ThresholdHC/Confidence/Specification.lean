import ThresholdHC.Confidence.Model

/-!
Full targets, fixed before supporting proofs. The upper algorithm family is
chosen before the gap law. Neither direction assumes a transcript information
bound, a simulation identity, independence of repetitions, or hidden access to
coin parameters. Constants are universal and deliberately not optimized.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Confidence
open ThresholdHC.Tier6

def ConfidenceAlgorithmLowerStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (B δ r : ℝ),
    1 ≤ B → 0 < δ → δ ≤ 1/4 → 0 ≤ r →
    UniformBudget μ A B → UniformConfidence μ A r δ →
    modulus μ (confidenceScale B δ) / 64 ≤ r

def ConfidenceUpperStatement : Prop :=
  ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → ℝ → AdaptiveEstimator R),
    ∀ B δ : ℝ, 1 ≤ B → 0 < δ → δ ≤ 1/4 →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        UniformBudget μ (rule B δ) B ∧
        UniformConfidence μ (rule B δ) (8192 * modulus μ (confidenceScale B δ)) δ

def ConfidenceCharacterizationStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B δ : ℝ),
    1 ≤ B → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal (modulus μ (confidenceScale B δ) / 64) ≤ minimaxConfidenceRadius μ B δ ∧
    minimaxConfidenceRadius μ B δ ≤ ENNReal.ofReal (8192 * modulus μ (confidenceScale B δ))

def ConfidenceNonvacuityStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B δ : ℝ),
    0 ≤ B → 0 ≤ δ →
    (∃ (A : AdaptiveEstimator Unit), UniformBudget μ A B ∧ UniformConfidence μ A 1 δ) ∧
    minimaxConfidenceRadius μ B δ ≤ 1

end ThresholdHC.Confidence
