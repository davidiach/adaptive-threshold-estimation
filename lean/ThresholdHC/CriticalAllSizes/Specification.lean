import ThresholdHC.CriticalEntropy.BaseCost

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
namespace ThresholdHC.CriticalAllSizes
open CriticalEntropy

/-! Explicit target types. Recorded during implementation, not claimed as
an independent or before-proof specification. -/

def AllGapStatement : Prop := ∀ {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : SignTest R)
    (K : ℕ) (d : Fin K → EntropyGap)
    (hgap : ∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ))
    (hfinite : ∀ i b, expectedSignTestWork ν (signParameter (d i) b) A ≠ ∞)
    (herror : ∀ i b, (ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).real
      {z | A.output z ≠ b} ≤ 1/10),
    (K : ℝ)*log (K : ℝ)/4096 ≤
      ∑ i, (d i : ℝ)^2*(expectedSignTestWork ν (signParameter (d i) false) A).toReal

def AllGapEstimationStatement : Prop := ∀ {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (K : ℕ) (d : Fin K → EntropyGap)
    (hgap : ∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ))
    (n : ℕ) (hn : 0 < n) (M : ℝ) (hnM : 160*M ≤ (n : ℝ))
    (hfinite : ∀ i b, expectedStoppedProcedureWork ν (signParameter (d i) b) A ≠ ∞)
    (hmem : ∀ i b, MemLp id 2
      ((ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).map A.output))
    (hM : ∀ i b, (∫ x : ℝ, x^2
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).map A.output) ≤ M)
    (hminus : ∀ i, (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) false))).map A.output) ≤ 1/8)
    (hplus : ∀ i, 5/8 ≤ (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) true))).map A.output)),
    (K : ℝ)*Real.log (K : ℝ)/(4096*(n : ℝ)) ≤
      ∑ i, (d i : ℝ)^2*(expectedStoppedProcedureWork ν (signParameter (d i) false) A).toReal

def ExplicitRawBaseCostStatement : Prop :=
    ∀ (R : Type) [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
      (A : StoppedProcedure R ℝ) (ρ : unitInterval),
      0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 → ∀ (M : ℝ), 0 ≤ M →
      CappedPopulationGuarantee criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) A (ρ : ℝ) M →
      (1/10000000000 : ℝ)*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        M*(populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal

def ExplicitBaseCostStatement : Prop :=
    ∀ (R : Type) [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
      (A : StoppedProcedure R ℝ) (ρ : unitInterval),
      0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 → ∀ (V : ℝ), 0 ≤ V →
      (∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q →
        evariance (fun z => A.output (populationInput
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q z))
          (populationMeasure criticalGapLaw ν) ≤ ENNReal.ofReal V) →
      (∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q →
        populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A ≠ ∞) →
      (∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q →
        |populationMean criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A -
          (∫ d,(q d : ℝ) ∂criticalGapLaw)| ≤ (ρ : ℝ)/64) →
      (1/15000000000 : ℝ)*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        V*(populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal

end ThresholdHC.CriticalAllSizes
