import ThresholdHC.Statements2

/-!
Randomized finite-horizon adaptive experiments.

A seed has an arbitrary probability law, common to both hypotheses. Conditional
on the seed the policy is the deterministic policy from Statements2. The seed
can encode all of a policy's random choices. Tests may use the seed as well as
the observed transcript. No information or error bound is assumed here.
-/

noncomputable section
namespace ThresholdHC.Tier3
open MeasureTheory Real

abbrev Prefix (n : ℕ) := Fin n → Option Bool

def MeasurablePolicy {U : Type} [MeasurableSpace U] {m : ℕ}
    (pol : U → List Bool → Option (Fin m)) : Prop :=
  ∀ history action, MeasurableSet {u | pol u history = action}

def MeasurableTest {U : Type} [MeasurableSpace U] {n : ℕ}
    (A : U → Finset (Prefix n)) : Prop :=
  ∀ ω, MeasurableSet {u | ω ∈ A u}

def randomizedLaw {U : Type} [MeasurableSpace U] {m n : ℕ}
    (μ : Measure U) (pol : U → List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Prefix n) : ℝ :=
  ∫ u, transcriptLaw (pol u) d q ω ∂μ

/-- The average conditional KL, with the common seed retained. -/
def conditionalInformation {U : Type} [MeasurableSpace U] {m : ℕ}
    (μ : Measure U) (pol : U → List Bool → Option (Fin m)) (d η : Fin m → ℝ)
    (n : ℕ) : ℝ :=
  ∫ u, klFT (transcriptLaw (n := n) (pol u) d (fun i => 1/2 + η i))
    (transcriptLaw (n := n) (pol u) d (fun i => 1/2 - η i)) ∂μ

def randomizedWork {U : Type} [MeasurableSpace U] {m : ℕ}
    (μ : Measure U) (pol : U → List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (n : ℕ) : ℝ :=
  ∫ u, ∑ ω : Prefix n, transcriptLaw (pol u) d q ω * workOf ω ∂μ

def randomizedAcceptance {U : Type} [MeasurableSpace U] {m n : ℕ}
    (μ : Measure U) (pol : U → List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (A : U → Finset (Prefix n)) : ℝ :=
  ∫ u, ∑ ω ∈ A u, transcriptLaw (pol u) d q ω ∂μ

def RandomizedTotalStatement : Prop :=
  ∀ (U : Type) [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (m n : ℕ) (pol : U → List Bool → Option (Fin m)) (d q : Fin m → ℝ),
    MeasurablePolicy pol → (∀ i, 0 ≤ d i ∧ d i ≤ 1/2) →
    (∀ i, 0 ≤ q i ∧ q i ≤ 1) →
    (∀ ω : Prefix n, 0 ≤ randomizedLaw μ pol d q ω) ∧
      ∑ ω : Prefix n, randomizedLaw μ pol d q ω = 1

def RandomizedInformationStatement : Prop :=
  ∀ (U : Type) [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (m n : ℕ) (pol : U → List Bool → Option (Fin m)) (d η : Fin m → ℝ) (h : ℝ),
    MeasurablePolicy pol → 0 < h → (∀ i, 0 < d i ∧ d i ≤ 1/2) →
    (∀ i, 0 ≤ η i ∧ η i ≤ 1/8) → (∀ i, d i * η i ≤ h/8) →
    conditionalInformation μ pol d η n ≤
      (128/225) * h^2 * randomizedWork μ pol d (fun i => 1/2 + η i) n

def RandomizedMarginalKLStatement : Prop :=
  ∀ (U : Type) [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (m n : ℕ) (pol : U → List Bool → Option (Fin m)) (d η : Fin m → ℝ) (h : ℝ),
    MeasurablePolicy pol → 0 < h → (∀ i, 0 < d i ∧ d i ≤ 1/2) →
    (∀ i, 0 ≤ η i ∧ η i ≤ 1/8) → (∀ i, d i * η i ≤ h/8) →
    klFT (randomizedLaw (n := n) μ pol d (fun i => 1/2 + η i))
      (randomizedLaw (n := n) μ pol d (fun i => 1/2 - η i)) ≤
      (128/225) * h^2 * randomizedWork μ pol d (fun i => 1/2 + η i) n

def RandomizedTestingStatement : Prop :=
  ∀ (U : Type) [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (m n : ℕ) (pol : U → List Bool → Option (Fin m)) (d η : Fin m → ℝ)
    (h δ : ℝ) (A : U → Finset (Prefix n)),
    MeasurablePolicy pol → MeasurableTest A →
    0 < h → (∀ i, 0 < d i ∧ d i ≤ 1/2) →
    (∀ i, 0 ≤ η i ∧ η i ≤ 1/8) → (∀ i, d i * η i ≤ h/8) →
    0 < δ → δ < 1/2 →
    1 - δ ≤ randomizedAcceptance μ pol d (fun i => 1/2 + η i) A →
    randomizedAcceptance μ pol d (fun i => 1/2 - η i) A ≤ δ →
    klB (1 - δ) δ ≤
      (128/225) * h^2 * randomizedWork μ pol d (fun i => 1/2 + η i) n

end ThresholdHC.Tier3
