import ThresholdHC.CriticalEntropy.CriticalMinimax
import ThresholdHC.CriticalEntropy.PopulationTransfer
import Mathlib
import ThresholdHC.Proofs.Tier2.ClassifierProbability
import ThresholdHC.CriticalEntropy.SignTest
import ThresholdHC.CriticalEntropy.EarlyDecision
import ThresholdHC.CriticalEntropy.StoppedModel
import ThresholdHC.CriticalEntropy.SequentialModel
import ThresholdHC.CriticalEntropy.RepeatedModel
import ThresholdHC.CriticalEntropy.RepeatedSignModel
import ThresholdHC.CriticalEntropy.PopulationModel
import ThresholdHC.CriticalEntropy.GoodGapModel
import ThresholdHC.CriticalEntropy.CriticalModel
import ThresholdHC.CriticalEntropy.ActivationModel
import ThresholdHC.CriticalEntropy.ObservationModel
import ThresholdHC.CriticalEntropy.HellingerModel
import ThresholdHC.CriticalEntropy.CriticalLaw
import ThresholdHC.CriticalEntropy.ObservationGeometryModel

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

/-- Population moment and work formulas are derived for an actual hidden-parameter
tape generator. Infinite nonnegative expectations are retained. The signed mean
formula requires finite second moment under the population being evaluated. -/
def PopulationMomentStatement : Prop :=
  ∀ (D R : Type) [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval), Measurable p₀ → Measurable p₁ → Measurable q →
    ∀ (A : StoppedProcedure R ℝ),
    populationSecondMoment μ ν p₀ p₁ q A =
      (∫⁻ d, ENNReal.ofReal (q d : ℝ)*conditionalSecondMoment ν (p₁ d) A +
        ENNReal.ofReal (1-(q d : ℝ))*conditionalSecondMoment ν (p₀ d) A ∂μ) ∧
    populationExpectedWork μ ν p₀ p₁ q A =
      (∫⁻ d, ENNReal.ofReal (q d : ℝ)*expectedStoppedProcedureWork ν (p₁ d) A +
        ENNReal.ofReal (1-(q d : ℝ))*expectedStoppedProcedureWork ν (p₀ d) A ∂μ) ∧
    (populationSecondMoment μ ν p₀ p₁ q A ≠ ∞ →
      populationMean μ ν p₀ p₁ q A =
        ∫ d, (q d : ℝ)*conditionalMean ν (p₁ d) A +
          (1-(q d : ℝ))*conditionalMean ν (p₀ d) A ∂μ)

/-- Null and positive-constant population guarantees yield almost-everywhere
conditional finiteness for both signs and integrable conditional means. They also
yield finite (without a claimed numerical bound) moment and work at every prior. -/
def PopulationFinitenessStatement : Prop :=
  ∀ (D R : Type) [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval), Measurable p₀ → Measurable p₁ →
    ∀ (c : unitInterval), 0 < (c : ℝ) → ∀ (A : StoppedProcedure R ℝ),
    populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞ →
    populationSecondMoment μ ν p₀ p₁ (fun _ => c) A ≠ ∞ →
    populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A ≠ ∞ →
    populationExpectedWork μ ν p₀ p₁ (fun _ => c) A ≠ ∞ →
    (∀ᵐ d ∂μ,
      MemLp id 2 ((ν.prod (Tier2.tapeMeasure (p₀ d))).map A.output) ∧
      MemLp id 2 ((ν.prod (Tier2.tapeMeasure (p₁ d))).map A.output) ∧
      expectedStoppedProcedureWork ν (p₀ d) A ≠ ∞ ∧
      expectedStoppedProcedureWork ν (p₁ d) A ≠ ∞) ∧
    Integrable (fun d => conditionalMean ν (p₀ d) A) μ ∧
    Integrable (fun d => conditionalMean ν (p₁ d) A) μ ∧
    (∀ (q : D → unitInterval), Measurable q →
      populationSecondMoment μ ν p₀ p₁ q A ≠ ∞ ∧
      populationExpectedWork μ ν p₀ p₁ q A ≠ ∞)

/-- The variance floor uses genuine extended-variance finiteness, so totalized
real variance cannot conceal a non-square-integrable output. -/
def PopulationVarianceFloorStatement : Prop :=
  ∀ (D R : Type) [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval), Measurable p₀ → Measurable p₁ →
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ (A : StoppedProcedure R ℝ),
    ProbabilityTheory.evariance (fun z => A.output (populationInput p₀ p₁ (fun _ => 0) z))
      (populationMeasure μ ν) ≠ ∞ →
    ProbabilityTheory.evariance (fun z => A.output (populationInput p₀ p₁ (fun _ => ρ) z))
      (populationMeasure μ ν) ≠ ∞ →
    |populationMean μ ν p₀ p₁ (fun _ => 0) A| ≤ (ρ : ℝ)/64 →
    |populationMean μ ν p₀ p₁ (fun _ => ρ) A-(ρ : ℝ)| ≤ (ρ : ℝ)/64 →
    ENNReal.ofReal (2*(ρ : ℝ)/3) ≤
      ProbabilityTheory.evariance (fun z => A.output (populationInput p₀ p₁ (fun _ => ρ) z))
        (populationMeasure μ ν)

/-- An actual extended-variance bound and bias control imply the raw moment
bound. Finiteness of the raw moment is derived, not assumed. -/
def PopulationMomentFromVarianceStatement : Prop :=
  ∀ (D R : Type) [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval), Measurable p₀ → Measurable p₁ → Measurable q →
    ∀ (A : StoppedProcedure R ℝ) (ρ V : ℝ), 0 < ρ → ρ ≤ 1/4 → 2*ρ/3 ≤ V →
    (∫ d, (q d : ℝ) ∂μ) ≤ ρ →
    |populationMean μ ν p₀ p₁ q A - (∫ d, (q d : ℝ) ∂μ)| ≤ ρ/64 →
    ProbabilityTheory.evariance (fun z => A.output (populationInput p₀ p₁ q z))
      (populationMeasure μ ν) ≤ ENNReal.ofReal V →
    populationSecondMoment μ ν p₀ p₁ q A ≤ ENNReal.ofReal (3*V/2)

/-- Construct the good set from uniform population guarantees over the capped
global class on an atomless bounded real gap law. The conditional bounds and
almost-everywhere finiteness are conclusions. Annulus selection is separate. -/
def PopulationGoodGapsStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : ℝ → unitInterval), Measurable p₀ → Measurable p₁ →
    ∀ (a b : ℝ), a ≤ b → μ (Set.Ioc a b)ᶜ = 0 →
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ (m : ℝ), 2*(ρ : ℝ)/3 ≤ m → ∀ (A : StoppedProcedure R ℝ),
    CappedPopulationGuarantee μ ν p₀ p₁ A (ρ : ℝ) m →
    ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ Set.Ioc a b ∧ μ.real Gᶜ ≤ 70*m ∧
      ∀ d ∈ G, PopulationGoodGap ν p₀ p₁ A (ρ : ℝ) m d

/-- The gap law is an atomless probability law with the claimed quadratic CDF.
The observation parameter equals the untruncated Bernoulli parameter everywhere
on its support. No probability instance or density identity is assumed. -/
def CriticalLawStatement : Prop :=
  IsProbabilityMeasure criticalGapLaw ∧ NullSingletonClass criticalGapLaw ∧
    criticalGapLaw (Set.Ioc (0 : ℝ) (1/4))ᶜ = 0 ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ 1/4 →
      criticalGapLaw (Set.Ioc (0 : ℝ) x) = ENNReal.ofReal (16*x^2)) ∧
    (∀ d ∈ Set.Ioc (0 : ℝ) (1/4), ∀ b : Bool,
      (criticalParameter d b : ℝ) = 1/2+(if b then d else -d))

/-- Finite-scale null-cost product for the actual quadratic population model.
Only uniform population guarantees are supplied: good conditional gaps, their
moments, restarts and sign-test information are derived. The explicit annulus
mass and scale-count hypotheses remain; this does not yet state the full
rarity-dependent base-cost bound. -/
def CriticalScaleProductStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ (m : ℝ), 2*(ρ : ℝ)/3 ≤ m →
    CappedPopulationGuarantee criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) A (ρ : ℝ) m →
    ∀ (K : ℕ), 32 ≤ Real.log (K : ℝ) →
    (∀ i : Fin K, 140*m ≤ criticalGapLaw.real (criticalAnnulus (i.val+3))) →
    (ρ : ℝ)*((K : ℝ)*Real.log (K : ℝ)) ≤
      (656384/3)*m*(populationExpectedWork criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true)
        (fun _ => 0) A).toReal

/-- The conditioned observable procedure and its quantitative BC7 bounds. -/
def ActivationNormalizationStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : ℝ → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ : unitInterval) (hρ : 0 < (ρ : ℝ))
    (hρ' : (ρ : ℝ) ≤ 1/4) (M : ℝ) (hM : 0 ≤ M)
    (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ : ℝ) M),
    let p := ν.real (activeSeeds A)
    let m := p*M+2*(ρ : ℝ)^2
    let W := (populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal
    let WZ := (populationExpectedWork μ (ProbabilityTheory.cond ν (activeSeeds A)) p₀ p₁ (fun _ => 0)
      (activeProcedure ν A)).toReal
    ν (activeSeeds A) ≠ 0 ∧
    CappedPopulationGuarantee μ (ProbabilityTheory.cond ν (activeSeeds A)) p₀ p₁ (activeProcedure ν A) (ρ : ℝ) m ∧
    2*(ρ : ℝ)/3 ≤ m ∧ 1 ≤ WZ ∧ WZ = W/p ∧
    m ≤ 4*(M*W) ∧ m*WZ ≤ 4*(M*W) ∧ (ρ : ℝ)/6 ≤ M*W

/-- Actual critical raw-moment base cost; no sign test or scale bound is assumed. -/
def CriticalRawBaseCostStatement : Prop := ∃ c : ℝ, 0 < c ∧
    ∀ (R : Type) [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
      (A : StoppedProcedure R ℝ) (ρ : unitInterval),
      0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 → ∀ (M : ℝ), 0 ≤ M →
      CappedPopulationGuarantee criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) A (ρ : ℝ) M →
      c*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        M*(populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal

/-- Actual critical variance base cost, retaining infinity in variance and work. -/
def CriticalBaseCostStatement : Prop := ∃ c : ℝ, 0 < c ∧
    ∀ (R : Type) [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
      (A : StoppedProcedure R ℝ) (ρ : unitInterval),
      0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 → ∀ (V : ℝ), 0 ≤ V →
      (∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q →
        ProbabilityTheory.evariance (fun z => A.output (populationInput
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q z))
          (populationMeasure criticalGapLaw ν) ≤ ENNReal.ofReal V) →
      (∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q →
        populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A ≠ ∞) →
      (∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q →
        |populationMean criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A -
          (∫ d,(q d : ℝ) ∂criticalGapLaw)| ≤ (ρ : ℝ)/64) →
      c*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        V*(populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal

/-- Exact recovery of the full observation law from a finite statistic. The
reconstruction measure is defined independently of the population sign law. -/
def CriticalObservationReconstructionStatement : Prop :=
  ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (q : ℝ → unitInterval), Measurable q →
    ∀ (A : StoppedProcedure R E) (m : ℕ), (∀ z, A.stop z ≤ m) →
    cappedTranscriptLaw criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m =
      ∑ i, cappedStatisticLaw criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m {i} •
          transcriptReconstruction ν A m i

/-- Affinity is defined by Radon--Nikodym derivatives of the actual full
observation laws. Equality to the finite expression is a conclusion. -/
def CriticalObservationAffinityStatement : Prop :=
  ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (q r : ℝ → unitInterval),
    Measurable q → Measurable r →
    ∀ (A : StoppedProcedure R E) (m : ℕ), (∀ z, A.stop z ≤ m) →
    hellingerAffinity
      (cappedTranscriptLaw criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m)
      (cappedTranscriptLaw criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m) =
      finiteAffinity
        (fun i => cappedStatisticLaw criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m {i})
        (fun i => cappedStatisticLaw criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m {i})

/-- The finite representation preserves the actual expected flip count. -/
def CriticalObservationWorkStatement : Prop :=
  ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (q : ℝ → unitInterval), Measurable q →
    ∀ (A : StoppedProcedure R E) (m : ℕ), (∀ z, A.stop z ≤ m) →
    populationExpectedWork criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A =
      ∑ i : Fin (m+1) × Fin (m+1), (i.1.val : ℝ≥0∞)*cappedStatisticLaw criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m {i}

/-- Actual population compactness and finite-experiment geometry. These
targets do not assert the missing risk comparison or a common hard pair. -/
def CriticalPopulationRepresentationStatement : Prop :=
  ∀ (ρ : ℝ), 0 ≤ ρ →
    IsCompact (populationDualSet criticalGapLaw ρ) ∧
    Convex ℝ (populationDualSet criticalGapLaw ρ) ∧
    (populationDualSet criticalGapLaw ρ).Nonempty ∧
    (∀ f ∈ populationDualSet criticalGapLaw ρ,
      CappedPrior criticalGapLaw ρ (populationDualPrior criticalGapLaw f) ∧
      populationTarget criticalGapLaw f =
        ∫ d, (populationDualPrior criticalGapLaw f d : ℝ) ∂criticalGapLaw) ∧
    (∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw ρ q →
      ∃ f ∈ populationDualSet criticalGapLaw ρ,
        (fun d => (populationDualPrior criticalGapLaw f d : ℝ)) =ᵐ[criticalGapLaw]
          (fun d => (q d : ℝ)))

def CriticalObservationGeometryStatement : Prop :=
  ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (m : ℕ), (∀ z, A.stop z ≤ m) → ∀ (ρ : ℝ), 0 ≤ ρ →
    (∃ F : PopulationDual criticalGapLaw →ᵃ[ℝ] (Option (Fin (m+1) × Fin (m+1)) → ℝ),
      Continuous F ∧ ∀ f ∈ populationDualSet criticalGapLaw ρ,
        F f = cappedObservationVector criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true)
          (populationDualPrior criticalGapLaw f) A m) ∧
    IsCompact (cappedObservationImage criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) A m ρ) ∧
    Convex ℝ (cappedObservationImage criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) A m ρ) ∧
    (cappedObservationImage criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) A m ρ).Nonempty ∧
    (∀ i : Fin (m+1) × Fin (m+1),
      ((stoppedReference ν A m).map (fun z => stoppedStatistic m z.2)) {i} ≠ 0 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ cappedObservationImage criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) A m ρ,
        ε ≤ v (some i))

def CriticalPairGeometryStatement : Prop :=
  ∀ (ρ δ : ℝ), 0 ≤ δ → δ ≤ 1/2 → δ ≤ ρ →
    IsCompact (populationPairSet criticalGapLaw ρ δ) ∧
    Convex ℝ (populationPairSet criticalGapLaw ρ δ) ∧
    (populationPairSet criticalGapLaw ρ δ).Nonempty ∧
    (∀ z ∈ populationPairSet criticalGapLaw ρ δ,
      CappedPrior criticalGapLaw ρ (populationDualPrior criticalGapLaw z.1) ∧
      CappedPrior criticalGapLaw ρ (populationDualPrior criticalGapLaw z.2) ∧
      δ ≤ (∫ d, (populationDualPrior criticalGapLaw z.2 d : ℝ) ∂criticalGapLaw) -
        (∫ d, (populationDualPrior criticalGapLaw z.1 d : ℝ) ∂criticalGapLaw)) ∧
    ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
      (m : ℕ), (∀ z, A.stop z ≤ m) →
      ∃ H : PopulationDual criticalGapLaw × PopulationDual criticalGapLaw → ℝ,
        Continuous H ∧ ConvexOn ℝ (populationPairSet criticalGapLaw ρ δ) H ∧
        ∀ z ∈ populationPairSet criticalGapLaw ρ δ,
          H z = 1-(hellingerAffinity
            (cappedTranscriptLaw criticalGapLaw ν
              (fun d => criticalParameter d false) (fun d => criticalParameter d true)
              (populationDualPrior criticalGapLaw z.1) A m)
            (cappedTranscriptLaw criticalGapLaw ν
              (fun d => criticalParameter d false) (fun d => criticalParameter d true)
              (populationDualPrior criticalGapLaw z.2) A m)).toReal ∧ H z ∈ Set.Icc 0 1

/-- Actual estimator realization and a separated pair for each capped policy.
The common pair and unrestricted population transfer are not asserted. -/
def CriticalCappedEstimatorStatement : Prop := ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (n : ℕ)
    (hsep : ∀ q r : ℝ → unitInterval, CappedPrior criticalGapLaw ρ q → CappedPrior criticalGapLaw ρ r →
      1/2 ≤ ((hellingerAffinity
        (cappedTranscriptLaw criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m)
        (cappedTranscriptLaw criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m)).toReal)^n →
      (∫ d, (q d : ℝ) ∂criticalGapLaw)-(∫ d, (r d : ℝ) ∂criticalGapLaw) < 2*ε),
    ∃ Z : StoppedProcedure R ℝ, Z.stop = A.stop ∧
      ∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw ρ q →
      MemLp (Z.output ∘ populationInput
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q) 2
        (populationMeasure criticalGapLaw ν) ∧
      |populationMean criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q Z-
        (∫ d, (q d : ℝ) ∂criticalGapLaw)| ≤ 3*ε ∧
      ProbabilityTheory.evariance (Z.output ∘ populationInput
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q)
        (populationMeasure criticalGapLaw ν) ≤ ENNReal.ofReal ((n : ℝ)*(9*ε^2)) ∧
      populationExpectedWork criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q Z =
      populationExpectedWork criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A

def CriticalCappedAffinityObstructionStatement : Prop := ∃ c : ℝ, 0 < c ∧
    ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
      (m : ℕ), (∀ z, A.stop z ≤ m) → ∀ (ρ : unitInterval),
      0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 → ∀ (n : ℕ) (ε : ℝ),
      0 ≤ ε → 3*ε ≤ (ρ : ℝ)/64 →
      (∀ q r : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q →
        CappedPrior criticalGapLaw (ρ : ℝ) r →
        1/2 ≤ ((hellingerAffinity
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m)
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m)).toReal)^n →
        (∫ d, (q d : ℝ) ∂criticalGapLaw)-(∫ d, (r d : ℝ) ∂criticalGapLaw) < 2*ε) →
      c*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        ((n : ℝ)*(9*ε^2))*(populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal

def CriticalCappedPolicyPairStatement : Prop := ∃ c : ℝ, 0 < c ∧
    ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
      (m : ℕ), (∀ z, A.stop z ≤ m) → ∀ (ρ : unitInterval),
      0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 → ∀ (n : ℕ) (ε : ℝ),
      0 ≤ ε → 3*ε ≤ (ρ : ℝ)/64 →
      ((n : ℝ)*(9*ε^2))*(populationExpectedWork criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal <
        c*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) →
      ∃ q r : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q ∧
        CappedPrior criticalGapLaw (ρ : ℝ) r ∧
        2*ε ≤ (∫ d, (q d : ℝ) ∂criticalGapLaw)-(∫ d, (r d : ℝ) ∂criticalGapLaw) ∧
        1/2 ≤ ((hellingerAffinity
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m)
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m)).toReal)^n

/-- Actual normalized policy constraint and one common pair for all capped
policies. Unrestricted population transfer is not asserted. -/
def CriticalCappedConstraintStatement : Prop := ∃ C : ℝ, 0 < C ∧
    ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
      (m : ℕ), (∀ z, A.stop z ≤ m) → ∀ (ρ : unitInterval),
      0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 → ∀ δ : ℝ, 0 ≤ δ → δ ≤ (ρ : ℝ)/96 →
      ∃ z ∈ populationPairSet criticalGapLaw (ρ : ℝ) δ,
        (1-(hellingerAffinity
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true)
            (populationDualPrior criticalGapLaw z.1) A m)
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true)
            (populationDualPrior criticalGapLaw z.2) A m)).toReal)*
          (ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        C*δ^2*(populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal

def CriticalCommonCappedPairStatement : Prop := ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ (ρ : ℝ)/96 →
    ∃ q r : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q ∧
      CappedPrior criticalGapLaw (ρ : ℝ) r ∧
      δ ≤ (∫ d, (r d : ℝ) ∂criticalGapLaw)-(∫ d, (q d : ℝ) ∂criticalGapLaw) ∧
      ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
        (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
        (m : ℕ), (∀ z, A.stop z ≤ m) →
        (1-(hellingerAffinity
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m)
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m)).toReal)*
          (ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        C*δ^2*(populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal

/-- Exact finite-population simulation and cost identities, followed by the
critical common pair for fixed finite families and horizons. Arbitrary seed
laws, unrestricted creation and termination limits are not asserted here. -/
def PopulationTapeLawStatement : Prop :=
  letI : MeasurableSpace (Option Bool) := ⊤
  ∀ {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q : Fin m → D → unitInterval) (hq : ∀ i, Measurable (q i))
    (d : D → ℝ) (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x)
    (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option (Fin m)),
    (Measure.pi (fun i => parameterTapeLaw (populationParameterLaw μ p₀ p₁ (q i)))).map
      (fun s => (populationSimulation pol n s).2) =
      finiteWeightMeasure (finitePopulationWeight (n := n) μ pol d (fun i x => (q i x : ℝ)))

def PopulationLocalWorkStatement : Prop :=
  letI : MeasurableSpace (Option Bool) := ⊤
  ∀ {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (pol : List Bool → Option (Fin m)),
    let τ := parameterTapeLaw (populationParameterLaw μ p₀ p₁ q)
    (∑ i : Fin m, populationExpectedWork μ (Measure.pi (fun _ : Fin m => τ)) p₀ p₁ q
      (localSimulationProcedure i n pol)) =
      ∫⁻ s, ((∑ t : Fin n, if ((populationSimulation pol n s).2 t).isSome then 1 else 0 : ℕ) : ℝ≥0∞)
        ∂Measure.pi (fun _ : Fin m => τ)

def CriticalFinitePopulationPairStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ (ρ : ℝ)/96 →
    ∃ q r : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q ∧
      CappedPrior criticalGapLaw (ρ : ℝ) r ∧
      δ ≤ (∫ d, (r d : ℝ) ∂criticalGapLaw)-(∫ d, (q d : ℝ) ∂criticalGapLaw) ∧
      ∀ (m n : ℕ) (pol : List Bool → Option (Fin m)),
        (1-realFiniteAffinity
          (finitePopulationWeight (n := n) criticalGapLaw pol id (fun _ d => (q d : ℝ)))
          (finitePopulationWeight criticalGapLaw pol id (fun _ d => (r d : ℝ))))*
          (ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        C*δ^2*(finitePopulationExpectedWork criticalGapLaw
          (fun d => criticalParameter d false) (fun d => criticalParameter d true)
          (midpointPrior q r) pol n).toReal

end ThresholdHC.CriticalEntropy

namespace ThresholdHC.CriticalEntropy
open MeasureTheory Filter ThresholdHC.Tier3 ThresholdHC.Tier4
open scoped ENNReal

def SeedKernelDensityStatement : Prop :=
  ∀ {R I : Type} [MeasurableSpace R] [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure R) [IsFiniteMeasure ν] (P : Measure (R × I)) [IsFiniteMeasure P]
    (p : R → I → ℝ),
    (∀ i, Measurable (fun r => p r i)) → (∀ r i, 0 ≤ p r i) → (∀ r i, p r i ≤ 1) →
    Tier5.FiniteKernelRealization ν P p →
    P = (ν.prod Measure.count).withDensity (fun z => ENNReal.ofReal (p z.1 z.2))

def CriticalExperimentPrefixPairStatement : Prop := ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ (ρ : ℝ)/96 →
    ∃ (q r : ℝ → unitInterval) (hq : CappedPrior criticalGapLaw (ρ : ℝ) q)
      (hr : CappedPrior criticalGapLaw (ρ : ℝ) r),
      δ ≤ (∫ d, (r d : ℝ) ∂criticalGapLaw)-(∫ d, (q d : ℝ) ∂criticalGapLaw) ∧
      ∀ (R : Type) [MeasurableSpace R] (A : Tier6.AdaptiveEstimator R) (n : ℕ),
        (1-(hellingerAffinity (criticalPrefixLaw A q hq.1 n)
          (criticalPrefixLaw A r hr.1 n)).toReal)*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        C*δ^2*∫ z, ThresholdHC.workOf (processPrefix n z.2)
          ∂criticalExperimentLaw A (midpointPrior q r) (measurable_midpointPrior q r hq.1 hr.1)

def CriticalEndpointStoppingStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : Tier6.AdaptiveEstimator R)
    (q : ℝ → unitInterval) (hq : Measurable q),
    criticalExpectedWork A q hq < ∞ →
    ∀ᵐ z ∂criticalExperimentLaw A q hq, ∃ n, A.policy z.1.1 (processHistory z.2 n) = none

def CriticalEventualReconstructionStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : Tier6.AdaptiveEstimator R)
    (q : ℝ → unitInterval) (hq : Measurable q),
    criticalExpectedWork A q hq < ∞ →
    ∀ᵐ z ∂criticalExperimentLaw A q hq,
      ∀ᶠ n in atTop, padPrefix n (processPrefix n z.2) = z.2

def CriticalTerminalPairStatement : Prop := ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ (ρ : ℝ)/96 →
    ∃ (q r : ℝ → unitInterval) (hq : CappedPrior criticalGapLaw (ρ : ℝ) q)
      (hr : CappedPrior criticalGapLaw (ρ : ℝ) r),
      δ ≤ (∫ d, (r d : ℝ) ∂criticalGapLaw)-(∫ d, (q d : ℝ) ∂criticalGapLaw) ∧
      ∀ (R I : Type) [MeasurableSpace R] [Fintype I] [MeasurableSpace I]
        [MeasurableSingletonClass I] (A : Tier6.AdaptiveEstimator R)
        (B : ℝ), 0 ≤ B → CriticalUniformBudget A (ρ : ℝ) B →
        ∀ (f : R × ProcessTape → I), Measurable f →
        (1-(hellingerAffinity (criticalObservationLaw A q hq.1 f)
          (criticalObservationLaw A r hr.1 f)).toReal)*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
          C*δ^2*B

def CriticalAlgorithmLowerStatement : Prop := ∃ c : ℝ, 0 < c ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ B : ℝ, 1 ≤ B → ∀ (R : Type) [MeasurableSpace R]
      (A : Tier6.AdaptiveEstimator R), CriticalUniformBudget A (ρ : ℝ) B →
      ENNReal.ofReal (c*min (ρ : ℝ)
        (Real.sqrt ((ρ : ℝ)*criticalLogFactor (ρ : ℝ)/B))) ≤
          criticalMaximalRMSRisk A (ρ : ℝ)

def CriticalMinimaxLowerStatement : Prop := ∃ c : ℝ, 0 < c ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ B : ℝ, 1 ≤ B →
      ENNReal.ofReal (c*min (ρ : ℝ)
        (Real.sqrt ((ρ : ℝ)*criticalLogFactor (ρ : ℝ)/B))) ≤
          criticalMinimaxRisk (ρ : ℝ) B

def CriticalBudgetNonemptyStatement : Prop :=
  ∀ ρ B : ℝ, ∃ A : Tier6.AdaptiveEstimator Unit, CriticalUniformBudget A ρ B

def CriticalTrivialUpperStatement : Prop :=
  ∀ ρ B : ℝ, criticalMinimaxRisk ρ B ≤ ENNReal.ofReal ρ

end ThresholdHC.CriticalEntropy
