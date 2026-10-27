import ThresholdHC.Tier3.StoppingModel
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
Tier 4 uses Mathlib's measure-theoretic relative entropy of the actual
pushforward transcript laws. The random seed is retained. No entropy limit,
absolute continuity, or information bound is assumed in the process model.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.Tier4
open ThresholdHC.Tier3

instance tapeSymbolMeasurableSpace : MeasurableSpace (Option Bool) := ⊤

def infiniteTranscriptLaw {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (ν : Measure Ω) (seed : Ω → Seed) (tape : Ω → ProcessTape) :
    Measure (Seed × ProcessTape) := ν.map (fun ω => (seed ω, tape ω))

def prefixTranscriptLaw {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (ν : Measure Ω) (seed : Ω → Seed) (tape : Ω → ProcessTape) (n : ℕ) :
    Measure (Seed × Prefix n) := ν.map (fun ω => (seed ω, processPrefix n (tape ω)))

/-- Actual joint seed/prefix KL equals the conditional finite-sum KL. -/
def FinitePrefixKLStatement : Prop :=
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (m n : ℕ) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (d η : Fin m → ℝ),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurablePolicy pol →
    RealizesPrefixes μ P seed tape pol d (fun i => 1/2 + η i) →
    RealizesPrefixes μ Q seed tape pol d (fun i => 1/2 - η i) →
    (∀ i, 0 < d i ∧ d i ≤ 1/2) →
    (∀ i, 0 ≤ η i ∧ η i ≤ 1/8) →
    InformationTheory.klDiv (prefixTranscriptLaw P seed tape n)
      (prefixTranscriptLaw Q seed tape n) =
      ENNReal.ofReal (conditionalInformation μ pol d η n)

/-- The full joint transcript entropy is the supremum of its finite-prefix
entropies. Only expected work under the plus hypothesis is required finite. -/
def InfiniteKLSupremumStatement : Prop :=
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (m : ℕ) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (d η : Fin m → ℝ),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurablePolicy pol →
    RealizesPrefixes μ P seed tape pol d (fun i => 1/2 + η i) →
    RealizesPrefixes μ Q seed tape pol d (fun i => 1/2 - η i) →
    (∀ i, 0 < d i ∧ d i ≤ 1/2) →
    (∀ i, 0 ≤ η i ∧ η i ≤ 1/8) →
    (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞ →
    InformationTheory.klDiv (infiniteTranscriptLaw P seed tape)
      (infiniteTranscriptLaw Q seed tape) =
      ⨆ n : ℕ, InformationTheory.klDiv (prefixTranscriptLaw P seed tape n)
        (prefixTranscriptLaw Q seed tape n)

/-- Full infinite-transcript KL is bounded by expected actual observations. -/
def InfiniteKLBoundStatement : Prop :=
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (m : ℕ) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (d η : Fin m → ℝ) (h : ℝ),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurablePolicy pol →
    RealizesPrefixes μ P seed tape pol d (fun i => 1/2 + η i) →
    RealizesPrefixes μ Q seed tape pol d (fun i => 1/2 - η i) →
    0 < h → (∀ i, 0 < d i ∧ d i ≤ 1/2) →
    (∀ i, 0 ≤ η i ∧ η i ≤ 1/8) → (∀ i, d i * η i ≤ h/8) →
    (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞ →
    InformationTheory.klDiv (infiniteTranscriptLaw P seed tape)
      (infiniteTranscriptLaw Q seed tape) ≤
      ENNReal.ofReal ((128/225) * h^2) * ∫⁻ ω, totalProcessWork (tape ω) ∂P

/-- In particular, the full transcript has an integrable log-likelihood ratio;
the extended-real bound is not obtained by taking `toReal` of infinity. -/
def InfiniteKLFiniteStatement : Prop :=
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (m : ℕ) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (d η : Fin m → ℝ),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurablePolicy pol →
    RealizesPrefixes μ P seed tape pol d (fun i => 1/2 + η i) →
    RealizesPrefixes μ Q seed tape pol d (fun i => 1/2 - η i) →
    (∀ i, 0 < d i ∧ d i ≤ 1/2) →
    (∀ i, 0 ≤ η i ∧ η i ≤ 1/8) →
    (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞ →
    let IP := infiniteTranscriptLaw P seed tape
    let IQ := infiniteTranscriptLaw Q seed tape
    InformationTheory.klDiv IP IQ < ∞ ∧ IP ≪ IQ ∧
      Integrable (MeasureTheory.llr IP IQ) IP

/-- Every measurable statistic of the full seed and tape obeys the same bound. -/
def ObservableKLBoundStatement : Prop :=
  ∀ (Seed Ω Z : Type) [MeasurableSpace Seed] [MeasurableSpace Ω] [MeasurableSpace Z]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (m : ℕ) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (d η : Fin m → ℝ) (h : ℝ)
    (observe : Seed × ProcessTape → Z),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurablePolicy pol → Measurable observe →
    RealizesPrefixes μ P seed tape pol d (fun i => 1/2 + η i) →
    RealizesPrefixes μ Q seed tape pol d (fun i => 1/2 - η i) →
    0 < h → (∀ i, 0 < d i ∧ d i ≤ 1/2) →
    (∀ i, 0 ≤ η i ∧ η i ≤ 1/8) → (∀ i, d i * η i ≤ h/8) →
    (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞ →
    InformationTheory.klDiv (P.map (fun ω => observe (seed ω, tape ω)))
      (Q.map (fun ω => observe (seed ω, tape ω))) ≤
      ENNReal.ofReal ((128/225) * h^2) * ∫⁻ ω, totalProcessWork (tape ω) ∂P

end ThresholdHC.Tier4
