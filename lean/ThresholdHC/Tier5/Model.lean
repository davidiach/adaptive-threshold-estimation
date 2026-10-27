import ThresholdHC.Tier5.CreationModel
import ThresholdHC.Tier4.Model

/-!
Unrestricted adaptive first use, revisiting and interleaving of countably many
potential coins. A first observation of a label creates that coin. The policy
may select any natural-number label, without a deterministic allocation cap.
The common seed may contain an arbitrary measurable magnitude environment.
The finite decision-tree cap is a definition of cylinder laws, not an assumption
restricting the policy or the total number of coins.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Tier5
open ThresholdHC.Tier3 ThresholdHC.Tier4

instance creationActionMeasurableSpace : MeasurableSpace (Option ℕ) := ⊤

def MeasurableCreationPolicy {Seed : Type} [MeasurableSpace Seed]
    (pol : Seed → List Bool → Option ℕ) : Prop :=
  ∀ xs a, MeasurableSet {u | pol u xs = a}

def MeasurableEnvironment {Seed : Type} [MeasurableSpace Seed]
    (d : Seed → ℕ → ℝ) : Prop := ∀ i, Measurable (fun u => d u i)

def RealizesCreationPrefixes {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (f : Seed → Prefix n → ℝ),
    (∀ w, Measurable (fun u => f u w)) →
    (∃ C : ℝ, ∀ u w, |f u w| ≤ C) →
    (∫ ω, f (seed ω) (processPrefix n (tape ω)) ∂ν) =
      ∫ u, ∑ w, creationLaw (pol u) (d u) (q u) w * f u w ∂μ

def CreationTotalStatement : Prop :=
  ∀ (n : ℕ) (pol : List Bool → Option ℕ) (d q : ℕ → ℝ),
    (∀ i, 0 ≤ d i ∧ d i ≤ 1/2) → (∀ i, 0 ≤ q i ∧ q i ≤ 1) →
    (∀ w : Prefix n, 0 ≤ creationLaw pol d q w) ∧
      ∑ w : Prefix n, creationLaw pol d q w = 1

def CreationConsistencyStatement : Prop :=
  ∀ (n : ℕ) (pol : List Bool → Option ℕ) (d q : ℕ → ℝ) (w : Prefix n),
    (∀ i, 0 ≤ d i ∧ d i ≤ 1/2) → (∀ i, 0 ≤ q i ∧ q i ≤ 1) →
    (∑ o : Option Bool, creationLaw pol d q (Fin.snoc w o)) = creationLaw pol d q w

def CreationFiniteKLStatement : Prop :=
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d η : Seed → ℕ → ℝ) (h : ℝ),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurableCreationPolicy pol → MeasurableEnvironment d → MeasurableEnvironment η →
    RealizesCreationPrefixes μ P seed tape pol d (fun u i => 1/2 + η u i) →
    RealizesCreationPrefixes μ Q seed tape pol d (fun u i => 1/2 - η u i) →
    0 < h → (∀ u i, 0 < d u i ∧ d u i ≤ 1/2) →
    (∀ u i, 0 ≤ η u i ∧ η u i ≤ 1/8) → (∀ u i, d u i * η u i ≤ h/8) →
    InformationTheory.klDiv (prefixTranscriptLaw P seed tape n)
      (prefixTranscriptLaw Q seed tape n) ≤
      ENNReal.ofReal ((128/225) * h^2 * ∫ ω, workOf (processPrefix n (tape ω)) ∂P)

/-- Only plus-hypothesis stopping is asserted; minus-hypothesis nontermination
is permitted in the unrestricted creation model. -/
def CreationStopsStatement : Prop :=
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d q : Seed → ℕ → ℝ),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurableCreationPolicy pol →
    RealizesCreationPrefixes μ P seed tape pol d q →
    (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞ →
    ∀ᵐ ω ∂P, ∃ n, pol (seed ω) (processHistory (tape ω) n) = none

def CreationKLSupremumStatement : Prop :=
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d η : Seed → ℕ → ℝ),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurableCreationPolicy pol → MeasurableEnvironment d → MeasurableEnvironment η →
    RealizesCreationPrefixes μ P seed tape pol d (fun u i => 1/2 + η u i) →
    RealizesCreationPrefixes μ Q seed tape pol d (fun u i => 1/2 - η u i) →
    (∀ u i, 0 < d u i ∧ d u i ≤ 1/2) →
    (∀ u i, 0 ≤ η u i ∧ η u i ≤ 1/8) →
    (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞ →
    InformationTheory.klDiv (infiniteTranscriptLaw P seed tape)
      (infiniteTranscriptLaw Q seed tape) =
      ⨆ n : ℕ, InformationTheory.klDiv (prefixTranscriptLaw P seed tape n)
        (prefixTranscriptLaw Q seed tape n)

def CreationInfiniteKLStatement : Prop :=
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d η : Seed → ℕ → ℝ) (h : ℝ),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurableCreationPolicy pol → MeasurableEnvironment d → MeasurableEnvironment η →
    RealizesCreationPrefixes μ P seed tape pol d (fun u i => 1/2 + η u i) →
    RealizesCreationPrefixes μ Q seed tape pol d (fun u i => 1/2 - η u i) →
    0 < h → (∀ u i, 0 < d u i ∧ d u i ≤ 1/2) →
    (∀ u i, 0 ≤ η u i ∧ η u i ≤ 1/8) → (∀ u i, d u i * η u i ≤ h/8) →
    (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞ →
    InformationTheory.klDiv (infiniteTranscriptLaw P seed tape)
      (infiniteTranscriptLaw Q seed tape) ≤
      ENNReal.ofReal ((128/225) * h^2) * ∫⁻ ω, totalProcessWork (tape ω) ∂P

def CreationObservableKLStatement : Prop :=
  ∀ (Seed Ω Z : Type) [MeasurableSpace Seed] [MeasurableSpace Ω] [MeasurableSpace Z]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d η : Seed → ℕ → ℝ) (h : ℝ)
    (observe : Seed × ProcessTape → Z),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurableCreationPolicy pol → MeasurableEnvironment d → MeasurableEnvironment η →
    Measurable observe →
    RealizesCreationPrefixes μ P seed tape pol d (fun u i => 1/2 + η u i) →
    RealizesCreationPrefixes μ Q seed tape pol d (fun u i => 1/2 - η u i) →
    0 < h → (∀ u i, 0 < d u i ∧ d u i ≤ 1/2) →
    (∀ u i, 0 ≤ η u i ∧ η u i ≤ 1/8) → (∀ u i, d u i * η u i ≤ h/8) →
    (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞ →
    InformationTheory.klDiv (P.map (fun ω => observe (seed ω, tape ω)))
      (Q.map (fun ω => observe (seed ω, tape ω))) ≤
      ENNReal.ofReal ((128/225) * h^2) * ∫⁻ ω, totalProcessWork (tape ω) ∂P

/-- Query a new coin on every observation and stop after a seed-selected length. -/
def freshPolicy (N : ℕ) (xs : List Bool) : Option ℕ :=
  if xs.length < N+1 then some xs.length else none

/-- A realized hard pair with finite expected work but no deterministic bound
on the number of distinct coins actually observed. -/
def UnboundedCreationExampleStatement : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure ℕ) (P Q : Measure Ω)
    (seed : Ω → ℕ) (tape : Ω → ProcessTape),
    IsProbabilityMeasure μ ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
    Measurable seed ∧ (∀ n b, MeasurableSet {ω | tape ω n = b}) ∧
    RealizesCreationPrefixes μ P seed tape freshPolicy (fun _ _ => 1/2) (fun _ _ => 5/8) ∧
    RealizesCreationPrefixes μ Q seed tape freshPolicy (fun _ _ => 1/2) (fun _ _ => 3/8) ∧
    (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞ ∧
    (∀ n : ℕ, 0 < P {ω | (n : ℝ≥0∞) < totalProcessWork (tape ω)})

end ThresholdHC.Tier5
