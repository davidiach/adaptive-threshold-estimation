"""Audit the common-pair and additive confidence-localization development."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ConfidenceLocalization.PowerPair
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier4
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceLocalization

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/2)
    (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ)
    (hsep : ∀ q r : D → unitInterval, CappedPrior μ (c : ℝ) q → CappedPrior μ (c : ℝ) r →
      1/2 ≤ ((hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior q (fun _ => c)) A m)
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior r (fun _ => c)) A m)).toReal)^n →
      (∫ d, (midpointPrior q (fun _ => c) d : ℝ) ∂μ)-
        (∫ d, (midpointPrior r (fun _ => c) d : ℝ) ∂μ) < 2*ε),
    ∃ Z : StoppedProcedure R ℝ, Z.stop = A.stop ∧
      (∃ C : ℝ, ∀ z, |Z.output z| ≤ C) ∧
      ∀ q : D → unitInterval, CappedPrior μ (c : ℝ) q →
      MemLp (Z.output ∘ populationInput p₀ p₁ q) 2 (populationMeasure μ ν) ∧
      |populationMean μ ν p₀ p₁ q Z-(∫ d, (q d : ℝ) ∂μ)| ≤ 6*ε ∧
      evariance (Z.output ∘ populationInput p₀ p₁ q) (populationMeasure μ ν) ≤
        ENNReal.ofReal (18*(n : ℝ)*ε^2) ∧
      populationExpectedWork μ ν p₀ p₁ q Z = populationExpectedWork μ ν p₀ p₁ q A :=
  @ThresholdHC.ConfidenceLocalization.regularized_capped_estimator

example : ∀ (κ τ : Measure unitInterval)
    [IsProbabilityMeasure κ] [IsProbabilityMeasure τ],
    parameterTapeLaw ((1/2 : ℝ≥0) • κ + (1/2 : ℝ≥0) • τ) =
      (1/2 : ℝ≥0) • parameterTapeLaw κ + (1/2 : ℝ≥0) • parameterTapeLaw τ :=
  @ThresholdHC.ConfidenceLocalization.tape_midpoint_law

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (n : ℕ),
    cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior q r) A n =
      (1/2 : ℝ≥0) • cappedTranscriptLaw μ ν p₀ p₁ q A n +
      (1/2 : ℝ≥0) • cappedTranscriptLaw μ ν p₀ p₁ r A n :=
  @ThresholdHC.ConfidenceLocalization.capped_law_midpoint

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (n : ℕ),
    cappedStatisticLaw μ ν p₀ p₁ (midpointPrior q r) A n =
      (1/2 : ℝ≥0) • cappedStatisticLaw μ ν p₀ p₁ q A n +
      (1/2 : ℝ≥0) • cappedStatisticLaw μ ν p₀ p₁ r A n :=
  @ThresholdHC.ConfidenceLocalization.statistic_law_midpoint

example : ∀ (κ τ : Measure unitInterval) (h : κ ≤ τ),
    parameterTapeLaw κ ≤ parameterTapeLaw τ :=
  @ThresholdHC.ConfidenceLocalization.tape_law_mono

example : ∀ (κ : Measure unitInterval) (c : ℝ≥0∞),
    parameterTapeLaw (c • κ) = c • parameterTapeLaw κ :=
  @ThresholdHC.ConfidenceLocalization.tape_law_smul

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (c : unitInterval) (hc : (c : ℝ) ≤ 1/2)
    (A : StoppedProcedure R E) (n : ℕ),
    ENNReal.ofReal (c : ℝ) • cappedTranscriptLaw μ ν p₀ p₁ q A n ≤
      cappedTranscriptLaw μ ν p₀ p₁ (fun _ => c) A n :=
  @ThresholdHC.ConfidenceLocalization.capped_law_const_domination

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (c : unitInterval) (hc : (c : ℝ) ≤ 1/2)
    (A : StoppedProcedure R E) (n : ℕ),
    ENNReal.ofReal (c : ℝ) • cappedStatisticLaw μ ν p₀ p₁ q A n ≤
      cappedStatisticLaw μ ν p₀ p₁ (fun _ => c) A n :=
  @ThresholdHC.ConfidenceLocalization.statistic_law_const_domination

example : ∀ {X : Type} [MeasurableSpace X]
    (P Q ξ : Measure X) [SigmaFinite P] [SigmaFinite Q] [SigmaFinite ξ]
    (hP : P ≪ ξ) (hQ : Q ≪ ξ),
    hellingerAffinity P Q =
      ∫⁻ x, (P.rnDeriv ξ x * Q.rnDeriv ξ x)^(1/2 : ℝ) ∂ξ :=
  @ThresholdHC.ConfidenceLocalization.affinity_reference

example : ∀ {X : Type} [MeasurableSpace X]
    (ξ : Measure X) [SigmaFinite ξ] (f g : X → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hf_top : ∀ x, f x ≠ ∞) (hg_top : ∀ x, g x ≠ ∞),
    hellingerAffinity (ξ.withDensity f) (ξ.withDensity g) =
      ∫⁻ x, (f x*g x)^(1/2 : ℝ) ∂ξ :=
  @ThresholdHC.ConfidenceLocalization.affinity_with_density

example : ∀ {X I : Type}
    [MeasurableSpace X] [MeasurableSpace I]
    (ξ : Measure X) [IsFiniteMeasure ξ] (T : X → I) (hT : Measurable T)
    (f g : I → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hf_top : ∀ i, f i ≠ ∞) (hg_top : ∀ i, g i ≠ ∞),
    hellingerAffinity (ξ.withDensity (f ∘ T)) (ξ.withDensity (g ∘ T)) =
      hellingerAffinity ((ξ.withDensity (f ∘ T)).map T) ((ξ.withDensity (g ∘ T)).map T) :=
  @ThresholdHC.ConfidenceLocalization.affinity_factored_statistic

example : ∀ {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P Q M : Measure I) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure M]
    (hM : M = (1/2 : ℝ≥0) • P + (1/2 : ℝ≥0) • Q) (f : I → ℝ),
    (∫ i, f i ∂M) = ((∫ i, f i ∂P)+(∫ i, f i ∂Q))/2 :=
  @ThresholdHC.ConfidenceLocalization.half_mixture_mean

example : ∀ {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P Q M : Measure I) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure M]
    (hM : M = (1/2 : ℝ≥0) • P + (1/2 : ℝ≥0) • Q) (f : I → ℝ),
    variance f P ≤ 2*variance f M :=
  @ThresholdHC.ConfidenceLocalization.half_mixture_variance

example : ∀ {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P Q M : Measure I) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure M]
    (hM : M = (1/2 : ℝ≥0) • P + (1/2 : ℝ≥0) • Q)
    (f : I → ℝ) (c θ ε V : ℝ) (hV : 0 ≤ V)
    (hb : |(∫ i, f i ∂M)-(θ+c)/2| ≤ ε)
    (hv : evariance f M ≤ ENNReal.ofReal V),
    let Z := fun i => f i+((∫ j, f j ∂Q)-c)
    |(∫ i, Z i ∂P)-θ| ≤ 2*ε ∧ evariance Z P ≤ ENNReal.ofReal (2*V) :=
  @ThresholdHC.ConfidenceLocalization.half_score_transfer

example : ∀ {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ : D → unitInterval)
    {ρ b J : ℝ} (hJ : 0 < J)
    (hobs : NullVarianceObstruction μ p₀ p₁ ρ b J),
    b < ρ/2 :=
  @ThresholdHC.ConfidenceLocalization.obstruction_bias_lt_half

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/2)
    (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ)
    (b J : ℝ) (hobs : NullVarianceObstruction μ p₀ p₁ (c : ℝ) b J) (hsmall : 6*ε ≤ b)
    (hsep : ∀ q r : D → unitInterval, CappedPrior μ (c : ℝ) q → CappedPrior μ (c : ℝ) r →
      1/2 ≤ ((hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior q (fun _ => c)) A m)
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior r (fun _ => c)) A m)).toReal)^n →
      (∫ d, (midpointPrior q (fun _ => c) d : ℝ) ∂μ)-
        (∫ d, (midpointPrior r (fun _ => c) d : ℝ) ∂μ) < 2*ε),
    J ≤ (18*(n : ℝ)*ε^2)*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal :=
  @ThresholdHC.ConfidenceLocalization.regularized_affinity_obstruction

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/2)
    (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ)
    (b J : ℝ) (hobs : NullVarianceObstruction μ p₀ p₁ (c : ℝ) b J) (hsmall : 6*ε ≤ b)
    (hlt : (18*(n : ℝ)*ε^2)*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal < J),
    ∃ q r : D → unitInterval, CappedPrior μ (c : ℝ) q ∧ CappedPrior μ (c : ℝ) r ∧
      2*ε ≤ (∫ d, (midpointPrior q (fun _ => c) d : ℝ) ∂μ)-
        (∫ d, (midpointPrior r (fun _ => c) d : ℝ) ∂μ) ∧
      1/2 ≤ ((hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior q (fun _ => c)) A m)
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior r (fun _ => c)) A m)).toReal)^n :=
  @ThresholdHC.ConfidenceLocalization.regularized_policy_power_pair

example : ∀ {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (F : unitInterval → ℝ≥0∞) (hF : Measurable F),
    (∫⁻ p, F p ∂populationParameterLaw μ p₀ p₁ q) =
      ∫⁻ d, ENNReal.ofReal (q d : ℝ)*F (p₁ d) + ENNReal.ofReal (1-(q d : ℝ))*F (p₀ d) ∂μ :=
  @ThresholdHC.ConfidenceLocalization.parameter_lintegral

example : ∀ {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (c : unitInterval) (hc : (c : ℝ) ≤ 1/2),
    ENNReal.ofReal (c : ℝ) • populationParameterLaw μ p₀ p₁ q ≤
      populationParameterLaw μ p₀ p₁ (fun _ => c) :=
  @ThresholdHC.ConfidenceLocalization.parameter_law_const_domination

example : ∀ {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r),
    populationParameterLaw μ p₀ p₁ (midpointPrior q r) =
      (1/2 : ℝ≥0) • populationParameterLaw μ p₀ p₁ q +
        (1/2 : ℝ≥0) • populationParameterLaw μ p₀ p₁ r :=
  @ThresholdHC.ConfidenceLocalization.parameter_midpoint_law

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/2)
    (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ)
    (hsep : ∀ q r : D → unitInterval, CappedPrior μ (c : ℝ) q → CappedPrior μ (c : ℝ) r →
      1/2 ≤ ((hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior q (fun _ => c)) A m)
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior r (fun _ => c)) A m)).toReal)^n →
      (∫ d, (midpointPrior q (fun _ => c) d : ℝ) ∂μ)-
        (∫ d, (midpointPrior r (fun _ => c) d : ℝ) ∂μ) < 2*ε),
    ∃ f : Fin (m+1) × Fin (m+1) → ℝ,
      ∀ q : D → unitInterval, CappedPrior μ (c : ℝ) q →
      |(∫ i, f i ∂cappedStatisticLaw μ ν p₀ p₁ q A m)-(∫ d, (q d : ℝ) ∂μ)| ≤ 6*ε ∧
      evariance f (cappedStatisticLaw μ ν p₀ p₁ q A m) ≤ ENNReal.ofReal (18*(n : ℝ)*ε^2) :=
  @ThresholdHC.ConfidenceLocalization.regularized_observation_score

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m),
    hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m) (cappedTranscriptLaw μ ν p₀ p₁ r A m) =
      hellingerAffinity (cappedStatisticLaw μ ν p₀ p₁ q A m) (cappedStatisticLaw μ ν p₀ p₁ r A m) :=
  @ThresholdHC.ConfidenceLocalization.capped_affinity_statistic

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m),
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r A m)).toReal =
      realFiniteAffinity
        (fun i => (cappedStatisticLaw μ ν p₀ p₁ q A m).real {i})
        (fun i => (cappedStatisticLaw μ ν p₀ p₁ r A m).real {i}) :=
  @ThresholdHC.ConfidenceLocalization.capped_affinity_real

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (ρ : ℝ),
    ∃ H : PopulationDual μ × PopulationDual μ → ℝ, Continuous H ∧
      ConvexOn ℝ (populationDualSet μ ρ ×ˢ populationDualSet μ ρ) H ∧
      ∀ f ∈ populationDualSet μ ρ, ∀ g ∈ populationDualSet μ ρ,
        H (f,g) = 1-(hellingerAffinity
          (cappedTranscriptLaw μ ν p₀ p₁ (populationDualPrior μ f) A m)
          (cappedTranscriptLaw μ ν p₀ p₁ (populationDualPrior μ g) A m)).toReal :=
  @ThresholdHC.ConfidenceLocalization.capped_pair_geometry

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (n : ℕ)
    (i : Fin (n+1) × Fin (n+1)),
    (cappedStatisticLaw μ ν p₀ p₁ (midpointPrior q r) A n).real {i} =
      ((cappedStatisticLaw μ ν p₀ p₁ q A n).real {i}+
        (cappedStatisticLaw μ ν p₀ p₁ r A n).real {i})/2 :=
  @ThresholdHC.ConfidenceLocalization.statistic_mass_midpoint

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/2)
    (A : StoppedProcedure R E) (n : ℕ) (i : Fin (n+1) × Fin (n+1))
    (hz : (cappedStatisticLaw μ ν p₀ p₁ (fun _ => c) A n).real {i} = 0),
    (cappedStatisticLaw μ ν p₀ p₁ q A n).real {i} = 0 :=
  @ThresholdHC.ConfidenceLocalization.statistic_common_support
""".lstrip()
    roots = {
        'ThresholdHC.ConfidenceLocalization.affinity_factored_statistic',
        'ThresholdHC.ConfidenceLocalization.affinity_reference',
        'ThresholdHC.ConfidenceLocalization.affinity_with_density',
        'ThresholdHC.ConfidenceLocalization.capped_affinity_real',
        'ThresholdHC.ConfidenceLocalization.capped_affinity_statistic',
        'ThresholdHC.ConfidenceLocalization.capped_law_const_domination',
        'ThresholdHC.ConfidenceLocalization.capped_law_midpoint',
        'ThresholdHC.ConfidenceLocalization.capped_pair_geometry',
        'ThresholdHC.ConfidenceLocalization.half_mixture_mean',
        'ThresholdHC.ConfidenceLocalization.half_mixture_variance',
        'ThresholdHC.ConfidenceLocalization.half_score_transfer',
        'ThresholdHC.ConfidenceLocalization.obstruction_bias_lt_half',
        'ThresholdHC.ConfidenceLocalization.parameter_law_const_domination',
        'ThresholdHC.ConfidenceLocalization.parameter_lintegral',
        'ThresholdHC.ConfidenceLocalization.parameter_midpoint_law',
        'ThresholdHC.ConfidenceLocalization.regularized_affinity_obstruction',
        'ThresholdHC.ConfidenceLocalization.regularized_capped_estimator',
        'ThresholdHC.ConfidenceLocalization.regularized_observation_score',
        'ThresholdHC.ConfidenceLocalization.regularized_policy_power_pair',
        'ThresholdHC.ConfidenceLocalization.statistic_common_support',
        'ThresholdHC.ConfidenceLocalization.statistic_law_const_domination',
        'ThresholdHC.ConfidenceLocalization.statistic_law_midpoint',
        'ThresholdHC.ConfidenceLocalization.statistic_mass_midpoint',
        'ThresholdHC.ConfidenceLocalization.tape_law_mono',
        'ThresholdHC.ConfidenceLocalization.tape_law_smul',
        'ThresholdHC.ConfidenceLocalization.tape_midpoint_law',
    }
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ConfidenceLocalization.PowerPair"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
