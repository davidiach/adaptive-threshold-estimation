import Mathlib
import ThresholdHC.Proofs.Tier2.ClassifierProbability

noncomputable section
open MeasureTheory Real
namespace ThresholdHC.CriticalEntropy

/-- Exact analytic target. Its packing inequality is an explicit hypothesis. -/
def EntropyPackingStatement : Prop :=
  ∀ (K c : ℝ), 0 < K → 32 ≤ log K → 0 ≤ c →
    (K / 2) * exp (-128 * c - 8) ≤
      1 + log (1024 * (16 * c + 2)) / log 4 →
    log K / 512 ≤ c

/-- Exact convex-analytic target. The statistical realization and mixture
bound remain explicit hypotheses, not conclusions of this component. -/
def CommonPointStatement : Prop :=
  ∀ (E ι : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (X : Set E), X.Nonempty → IsCompact X → Convex ℝ X →
    ∀ (f : ι → E → ℝ), (∀ i, Continuous (f i)) →
      (∀ i, ConvexOn ℝ X (f i)) →
      (∀ (s : Finset ι) (p : s → ℝ), (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
        ∃ x ∈ X, (∑ i : s, p i * f i x) ≤ 0) →
      ∃ x ∈ X, ∀ i, f i x ≤ 0

/-- Actual seeded iid tape laws and an observable of a deterministic prefix.
The information bound is a conclusion, not an assumed model property. -/
def PrefixInformationStatement : Prop :=
  ∀ (R X : Type) [MeasurableSpace R] [MeasurableSpace X]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (p q : unitInterval), 0 < (p : ℝ) → (p : ℝ) < 1 →
      0 < (q : ℝ) → (q : ℝ) < 1 →
    ∀ (n : ℕ) (f : R × (Fin n → Bool) → X), Measurable f →
      InformationTheory.klDiv
        ((ν.prod (Tier2.tapeMeasure p)).map (f ∘ Prod.map id (Tier2.tapePrefix n)))
        ((ν.prod (Tier2.tapeMeasure q)).map (f ∘ Prod.map id (Tier2.tapePrefix n))) ≤
        ENNReal.ofReal (n * ((p : ℝ)-q)^2 / ((q : ℝ)*(1-q)))

/-- The BC3 event transfer for constructed finite Bernoulli laws. Stopping
windows must still supply an event satisfying these explicit hypotheses. -/
def PrefixEventTransferStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
    (p : unitInterval), 0 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ (n : ℕ) (c : ℝ), n*((p : ℝ)-1/2)^2 ≤ 4*c+1/4 →
    ∀ (s : Set (R × (Fin n → Bool))), MeasurableSet s →
      (1/4 : ℝ) ≤ (ν.prod (Tier2.finiteMeasure p n)).real s →
      exp (-64*c-8) ≤ (ν.prod (Tier2.finiteMeasure ⟨1/2, by norm_num⟩ n)).real s

end ThresholdHC.CriticalEntropy
