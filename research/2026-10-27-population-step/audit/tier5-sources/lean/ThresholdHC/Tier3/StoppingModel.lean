import ThresholdHC.Tier3.RandomizedModel

/-!
Specification of unbounded adaptive experiments through their finite-prefix laws.
The realization condition identifies every bounded finite observation with the
explicit Tier 2 transcript law. It does not assume any information inequality.
Random seeds are included in that law and may be observed by the terminal test.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.Tier3

abbrev ProcessTape := ℕ → Option Bool

def processPrefix (n : ℕ) (x : ProcessTape) : Fin n → Option Bool := fun i => x i

def processHistory (x : ProcessTape) (n : ℕ) : List Bool :=
  (List.ofFn (processPrefix n x)).filterMap id

def totalProcessWork (x : ProcessTape) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (workOf (processPrefix n x))

def finiteHistory {n : ℕ} (w : Fin n → Option Bool) (k : Fin (n+1)) : List Bool :=
  (List.ofFn (fun i : Fin k.val => w (Fin.castLE (Nat.le_of_lt_succ k.isLt) i))).filterMap id

def acceptedBy {Seed : Type} {m : ℕ} (pol : Seed → List Bool → Option (Fin m))
    (decision : Seed → List Bool → Bool) (n : ℕ) (u : Seed)
    (w : Fin n → Option Bool) : Prop :=
  ∃ k : Fin (n+1), pol u (finiteHistory w k) = none ∧ decision u (finiteHistory w k) = true

def terminalAccept {Seed Ω : Type} {m : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (decision : Seed → List Bool → Bool) : Set Ω :=
  {ω | ∃ n : ℕ, pol (seed ω) (processHistory (tape ω) n) = none ∧
      decision (seed ω) (processHistory (tape ω) n) = true}

def RealizesPrefixes {Seed Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Ω]
    {m : ℕ} (μ : Measure Seed) (ν : Measure Ω) (seed : Ω → Seed)
    (tape : Ω → ProcessTape) (pol : Seed → List Bool → Option (Fin m))
    (d q : Fin m → ℝ) : Prop :=
  ∀ (n : ℕ) (f : Seed → (Fin n → Option Bool) → ℝ),
    (∀ w, Measurable (fun u => f u w)) →
    (∃ C : ℝ, ∀ u w, |f u w| ≤ C) →
    (∫ ω, f (seed ω) (processPrefix n (tape ω)) ∂ν) =
      ∫ u, ∑ w, transcriptLaw (pol u) d q w * f u w ∂μ

/-- Finite expected actual work forces the policy to halt almost surely. -/
def FiniteWorkStopsStatement : Prop :=
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (m : ℕ) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (d q : Fin m → ℝ),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurablePolicy pol →
    RealizesPrefixes μ ν seed tape pol d q →
    (∫⁻ ω, totalProcessWork (tape ω) ∂ν) < ∞ →
    ∀ᵐ ω ∂ν, ∃ n, pol (seed ω) (processHistory (tape ω) n) = none

/-- A finite plus-hypothesis expected work budget yields almost-sure halting
under both hypotheses. The finite latent-sign prior comparison transfers the
zero nontermination probability to the minus hypothesis. -/
def UnboundedStoppingStatement : Prop :=
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
    (∀ᵐ ω ∂P, ∃ n, pol (seed ω) (processHistory (tape ω) n) = none) ∧
    (∀ᵐ ω ∂Q, ∃ n, pol (seed ω) (processHistory (tape ω) n) = none)

/-- Tests of the terminal history obey the same information/work lower bound
at an unbounded stopping horizon. Work is required finite only under `P`. -/
def UnboundedTestingStatement : Prop :=
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (m : ℕ) (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (decision : Seed → List Bool → Bool)
    (d η : Fin m → ℝ) (h δ : ℝ),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurablePolicy pol →
    (∀ xs, Measurable (fun u => decision u xs)) →
    RealizesPrefixes μ P seed tape pol d (fun i => 1/2 + η i) →
    RealizesPrefixes μ Q seed tape pol d (fun i => 1/2 - η i) →
    0 < h → (∀ i, 0 < d i ∧ d i ≤ 1/2) →
    (∀ i, 0 ≤ η i ∧ η i ≤ 1/8) → (∀ i, d i * η i ≤ h/8) →
    0 < δ → δ < 1/2 →
    (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞ →
    1-δ ≤ P.real (terminalAccept seed tape pol decision) →
    Q.real (terminalAccept seed tape pol decision) ≤ δ →
    klB (1-δ) δ ≤ (128/225) * h^2 *
      (∫⁻ ω, totalProcessWork (tape ω) ∂P).toReal

end ThresholdHC.Tier3
