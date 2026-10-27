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

end ThresholdHC.CriticalEntropy
