import Mathlib
import ThresholdHC.Proofs.Tier2.ClassifierProbability
import ThresholdHC.CriticalEntropy.SignTest
import ThresholdHC.CriticalEntropy.EarlyDecision
import ThresholdHC.CriticalEntropy.StoppedModel
import ThresholdHC.CriticalEntropy.SequentialModel
import ThresholdHC.CriticalEntropy.RepeatedModel
import ThresholdHC.CriticalEntropy.RepeatedSignModel

noncomputable section
open MeasureTheory Real
open scoped ENNReal
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

/-- The statistical finite-gap theorem. A single test and seed law serve all
gaps and signs. Work is the actual stopping time; both signed laws terminate
in finite expectation. No fair-coin termination or information bound is assumed. -/
def FiniteGapSignEntropyStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
    (A : SignTest R) (K : ℕ) (d : Fin K → EntropyGap), 32 ≤ log (K : ℝ) →
    (∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ)) →
    (∀ i b, expectedSignTestWork ν (signParameter (d i) b) A ≠ ∞) →
    (∀ i b, (ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).real
      {z | A.output z ≠ b} ≤ 1/10) →
    (K : ℝ)*log (K : ℝ)/512 ≤
      ∑ i, (d i : ℝ)^2*(expectedSignTestWork ν (signParameter (d i) false) A).toReal

/-- Actual unused Bernoulli flips after a stopped procedure are independent
of its output and work. Work is finite in expectation under the stated law;
the procedure itself is independent of the Bernoulli parameter. -/
def StoppedSuffixStatement : Prop :=
  ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E), expectedStoppedProcedureWork ν p A ≠ ∞ →
    (ν.prod (Tier2.tapeMeasure p)).map
        (fun z => ((A.stop z, A.output z), stoppedSuffix A z)) =
      ((ν.prod (Tier2.tapeMeasure p)).map (fun z => (A.stop z, A.output z))).prod
        (Tier2.tapeMeasure p)

/-- The constructed observable sequential procedure uses successive flips
of one coin and independent seed coordinates. Its outputs have the product
law and its honest expected work adds, even if the second expectation is infinite. -/
def SequentialRestartStatement : Prop :=
  ∀ (R S E F : Type)
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]
    (ν : Measure R) (η : Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (p : unitInterval) (A : StoppedProcedure R E) (B : StoppedProcedure S F),
    expectedStoppedProcedureWork ν p A ≠ ∞ →
    ((ν.prod η).prod (Tier2.tapeMeasure p)).map (sequentialProcedure A B).output =
      ((ν.prod (Tier2.tapeMeasure p)).map A.output).prod
        ((η.prod (Tier2.tapeMeasure p)).map B.output) ∧
    expectedStoppedProcedureWork (ν.prod η) p (sequentialProcedure A B) =
      expectedStoppedProcedureWork ν p A + expectedStoppedProcedureWork η p B

/-- A fixed number of observable runs, with independent seeds and successive
unused flips of the same coin, has the iid joint output law and linear expected
work. The repeated procedure itself has no Bernoulli-parameter argument. -/
def RepeatedRestartStatement : Prop :=
  ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E), expectedStoppedProcedureWork ν p A ≠ ∞ →
    ∀ n : ℕ,
    ((Measure.pi (fun _ : Fin n => ν)).prod (Tier2.tapeMeasure p)).map
        (repeatedProcedure A n).output =
      Measure.pi (fun _ : Fin n => (ν.prod (Tier2.tapeMeasure p)).map A.output) ∧
    expectedStoppedProcedureWork (Measure.pi (fun _ : Fin n => ν)) p (repeatedProcedure A n) =
      (n : ℝ≥0∞) * expectedStoppedProcedureWork ν p A

/-- The constructed same-coin sign test has exact expected work and both
one-sided error bounds from the original output law's moments. -/
def RepeatedSignTestStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
    (p : unitInterval) (A : StoppedProcedure R ℝ),
    expectedStoppedProcedureWork ν p A ≠ ∞ →
    MemLp id 2 ((ν.prod (Tier2.tapeMeasure p)).map A.output) →
    ∀ (n : ℕ), 0 < n → ∀ (a M t : ℝ), 0 < a →
    (∫ x : ℝ, x^2 ∂(ν.prod (Tier2.tapeMeasure p)).map A.output) ≤ M →
    expectedSignTestWork (Measure.pi (fun _ : Fin n => ν)) p (repeatedSignTest A n t) =
      (n : ℝ≥0∞) * expectedStoppedProcedureWork ν p A ∧
    (t+a ≤ (∫ x : ℝ, x ∂(ν.prod (Tier2.tapeMeasure p)).map A.output) →
      ((Measure.pi (fun _ : Fin n => ν)).prod (Tier2.tapeMeasure p)).real
        {z | (repeatedSignTest A n t).output z ≠ true} ≤ M / ((n : ℝ)*a^2)) ∧
    ((∫ x : ℝ, x ∂(ν.prod (Tier2.tapeMeasure p)).map A.output)+a ≤ t →
      ((Measure.pi (fun _ : Fin n => ν)).prod (Tier2.tapeMeasure p)).real
        {z | (repeatedSignTest A n t).output z ≠ false} ≤ M / ((n : ℝ)*a^2))

/-- A statistical entropy bound charging the original real-output estimator's
negative-sign work. Its sign-test reduction is constructed in the conclusion's
proof, not supplied as a hypothesis. Continuum good-gap selection is separate. -/
def FiniteGapEstimationEntropyStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
    (A : StoppedProcedure R ℝ) (K : ℕ) (d : Fin K → EntropyGap),
    32 ≤ log (K : ℝ) →
    (∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ)) →
    ∀ (n : ℕ), 0 < n → ∀ (M : ℝ), 160*M ≤ (n : ℝ) →
    (∀ i b, expectedStoppedProcedureWork ν (signParameter (d i) b) A ≠ ∞) →
    (∀ i b, MemLp id 2 ((ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).map A.output)) →
    (∀ i b, (∫ x : ℝ, x^2
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).map A.output) ≤ M) →
    (∀ i, (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) false))).map A.output) ≤ 1/8) →
    (∀ i, 5/8 ≤ (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) true))).map A.output)) →
    (K : ℝ)*log (K : ℝ)/(512*(n : ℝ)) ≤
      ∑ i, (d i : ℝ)^2*(expectedStoppedProcedureWork ν (signParameter (d i) false) A).toReal

end ThresholdHC.CriticalEntropy
