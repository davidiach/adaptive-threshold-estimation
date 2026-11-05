import ThresholdHC.ConfidenceLocalization.ConfidenceRate
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier4
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceLocalization
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.ConfidenceTransfer

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

example : ∀ {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/4)
    {b J δ : ℝ} (hJ : 0 < J) (hδ : 0 < δ) (hδb : δ ≤ b/3)
    (hobs : NullVarianceObstruction μ p₀ p₁ (c : ℝ) b J),
    ∃ q r : D → unitInterval, CappedPrior μ (c : ℝ) q ∧ CappedPrior μ (c : ℝ) r ∧
      δ ≤ (∫ d, (r d : ℝ) ∂μ)-(∫ d, (q d : ℝ) ∂μ) ∧
      ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
        (m : ℕ), (∀ z, A.stop z ≤ m) →
        1-(hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m)
          (cappedTranscriptLaw μ ν p₀ p₁ r A m)).toReal ≤
          (42*δ^2/J)*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal :=
  @ThresholdHC.ConfidenceLocalization.common_pair_of_obstruction

example : ∀ {μ : Measure Gap} [IsProbabilityMeasure μ]
    {ρ b J : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/4) (hJ : 0 < J)
    (hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b J),
    CommonPairBound μ ρ b J :=
  @ThresholdHC.ConfidenceLocalization.common_pair_bound

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {ρ b J B ε δ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/4)
    (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b J)
    (hw : RareBudget μ A ρ B)
    (hconf : ∀ q : SignLaw, RarePrior μ ρ q →
      ThresholdHC.Confidence.failureProbability μ A q ε ≤ ENNReal.ofReal δ),
    min b (Real.sqrt (J*Real.log (1/δ)/B))/128 ≤ ε :=
  @ThresholdHC.ConfidenceLocalization.confidence_rate_of_obstruction

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ b J B δ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/4)
    (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b J),
    ENNReal.ofReal (min b (Real.sqrt (J*Real.log (1/δ)/B))/128) ≤
      rareConfidenceRadius μ ρ B δ :=
  @ThresholdHC.ConfidenceLocalization.minimax_confidence_of_obstruction

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

example : ∀ {X : Type} [MeasurableSpace X] (P Q : Measure X),
    hellingerAffinity P Q = hellingerAffinity Q P :=
  @ThresholdHC.ConfidenceLocalization.affinity_symm

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q₁ q₂ r₁ r₂ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq₁ : Measurable q₁) (hq₂ : Measurable q₂) (hr₁ : Measurable r₁) (hr₂ : Measurable r₂)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (heq : (fun d => (q₁ d : ℝ)) =ᵐ[μ] (fun d => (q₂ d : ℝ)))
    (her : (fun d => (r₁ d : ℝ)) =ᵐ[μ] (fun d => (r₂ d : ℝ))),
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q₁ A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r₁ A m)).toReal =
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q₂ A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r₂ A m)).toReal :=
  @ThresholdHC.ConfidenceLocalization.capped_affinity_congr_ae

example : ∀ {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ : D → unitInterval)
    {ρ b J : ℝ} (hJ : 0 < J)
    (hobs : NullVarianceObstruction μ p₀ p₁ ρ b J),
    b < ρ/2 :=
  @ThresholdHC.ConfidenceLocalization.obstruction_bias_lt_half

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (A : StoppedProcedure R E) {m M : ℕ} (h : m ≤ M) (hcap : ∀ z, A.stop z ≤ m),
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A M)
      (cappedTranscriptLaw μ ν p₀ p₁ r A M)).toReal =
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r A m)).toReal :=
  @ThresholdHC.ConfidenceLocalization.capped_affinity_enlarge

example : ∀ {D R S E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (f : S → R) (hf : Measurable f),
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q (reseedProcedure A f hf) m)
      (cappedTranscriptLaw μ ν p₀ p₁ r (reseedProcedure A f hf) m)).toReal =
    (hellingerAffinity (cappedTranscriptLaw μ (ν.map f) p₀ p₁ q A m)
      (cappedTranscriptLaw μ (ν.map f) p₀ p₁ r A m)).toReal :=
  @ThresholdHC.ConfidenceLocalization.reseed_affinity

example : ∀ {D I R E : Type} [Fintype I]
    [MeasurableSpace D] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (κ : Measure I) [IsProbabilityMeasure κ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (A : I → StoppedProcedure R E) (m : ℕ) (hcap : ∀ i z, (A i).stop z ≤ m),
    (hellingerAffinity (cappedTranscriptLaw μ (κ.prod ν) p₀ p₁ q (selectedProcedure A) m)
      (cappedTranscriptLaw μ (κ.prod ν) p₀ p₁ r (selectedProcedure A) m)).toReal =
      ∑ i, κ.real {i}*(hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q (A i) m)
        (cappedTranscriptLaw μ ν p₀ p₁ r (A i) m)).toReal :=
  @ThresholdHC.ConfidenceLocalization.selected_affinity

example : ∀ {D : Type} [MeasurableSpace D] (μ : Measure D) (p₀ p₁ : D → unitInterval) {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (q r : D → unitInterval),
    localAffinity μ p₀ p₁ (cappedPolicyOfProcedure ν A m hcap) q r =
      (hellingerAffinity
        (cappedTranscriptLaw μ ν
          p₀ p₁ q A m)
        (cappedTranscriptLaw μ ν
          p₀ p₁ r A m)).toReal :=
  @ThresholdHC.ConfidenceLocalization.localPolicyOfProcedure_affinity

example : ∀ {D : Type} [MeasurableSpace D] (μ : Measure D) (p₀ p₁ : D → unitInterval) {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m),
    localNullWork μ p₀ p₁ (cappedPolicyOfProcedure ν A m hcap) =
      (populationExpectedWork μ ν
        p₀ p₁ (fun _ => 0) A).toReal :=
  @ThresholdHC.ConfidenceLocalization.localPolicyOfProcedure_nullWork

example : ∀ {D : Type} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) {I : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (κ : Measure I) [IsProbabilityMeasure κ] (B : I → CappedPolicy),
    ∃ M : CappedPolicy,
      localNullWork μ p₀ p₁ M = ∑ i, κ.real {i}*localNullWork μ p₀ p₁ (B i) ∧
      ∀ q r : D → unitInterval, Measurable q → Measurable r →
        localAffinity μ p₀ p₁ M q r = ∑ i, κ.real {i}*localAffinity μ p₀ p₁ (B i) q r :=
  @ThresholdHC.ConfidenceLocalization.local_policy_mixture

example : ∀ {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/4)
    {b J δ : ℝ} (hJ : 0 < J) (hδ : 0 < δ) (hδb : δ ≤ b/3)
    (hobs : NullVarianceObstruction μ p₀ p₁ (c : ℝ) b J),
    ∃ z ∈ populationPairSet μ (c : ℝ) (2*δ),
      (1-(hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ z.1) (fun _ => c)) A m)
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ z.2) (fun _ => c)) A m)).toReal)*J ≤
        42*δ^2*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal :=
  @ThresholdHC.ConfidenceLocalization.regularized_policy_constraint

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
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (c : unitInterval),
    ∃ H : PopulationDual μ × PopulationDual μ → ℝ, Continuous H ∧
      ConvexOn ℝ (populationDualSet μ (c : ℝ) ×ˢ populationDualSet μ (c : ℝ)) H ∧
      ∀ f ∈ populationDualSet μ (c : ℝ), ∀ g ∈ populationDualSet μ (c : ℝ),
        H (f,g) = 1-(hellingerAffinity
          (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ f) (fun _ => c)) A m)
          (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ g) (fun _ => c)) A m)).toReal ∧
        H (f,g) ∈ Icc 0 1 :=
  @ThresholdHC.ConfidenceLocalization.regularized_pair_geometry

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
#print axioms ThresholdHC.ConfidenceLocalization.affinity_factored_statistic
#print axioms ThresholdHC.ConfidenceLocalization.affinity_reference
#print axioms ThresholdHC.ConfidenceLocalization.affinity_symm
#print axioms ThresholdHC.ConfidenceLocalization.affinity_with_density
#print axioms ThresholdHC.ConfidenceLocalization.capped_affinity_congr_ae
#print axioms ThresholdHC.ConfidenceLocalization.capped_affinity_enlarge
#print axioms ThresholdHC.ConfidenceLocalization.capped_affinity_real
#print axioms ThresholdHC.ConfidenceLocalization.capped_affinity_statistic
#print axioms ThresholdHC.ConfidenceLocalization.capped_law_const_domination
#print axioms ThresholdHC.ConfidenceLocalization.capped_law_midpoint
#print axioms ThresholdHC.ConfidenceLocalization.capped_pair_geometry
#print axioms ThresholdHC.ConfidenceLocalization.common_pair_bound
#print axioms ThresholdHC.ConfidenceLocalization.common_pair_of_obstruction
#print axioms ThresholdHC.ConfidenceLocalization.confidence_rate_of_obstruction
#print axioms ThresholdHC.ConfidenceLocalization.half_mixture_mean
#print axioms ThresholdHC.ConfidenceLocalization.half_mixture_variance
#print axioms ThresholdHC.ConfidenceLocalization.half_score_transfer
#print axioms ThresholdHC.ConfidenceLocalization.localPolicyOfProcedure_affinity
#print axioms ThresholdHC.ConfidenceLocalization.localPolicyOfProcedure_nullWork
#print axioms ThresholdHC.ConfidenceLocalization.local_policy_mixture
#print axioms ThresholdHC.ConfidenceLocalization.minimax_confidence_of_obstruction
#print axioms ThresholdHC.ConfidenceLocalization.obstruction_bias_lt_half
#print axioms ThresholdHC.ConfidenceLocalization.parameter_law_const_domination
#print axioms ThresholdHC.ConfidenceLocalization.parameter_lintegral
#print axioms ThresholdHC.ConfidenceLocalization.parameter_midpoint_law
#print axioms ThresholdHC.ConfidenceLocalization.regularized_affinity_obstruction
#print axioms ThresholdHC.ConfidenceLocalization.regularized_capped_estimator
#print axioms ThresholdHC.ConfidenceLocalization.regularized_observation_score
#print axioms ThresholdHC.ConfidenceLocalization.regularized_pair_geometry
#print axioms ThresholdHC.ConfidenceLocalization.regularized_policy_constraint
#print axioms ThresholdHC.ConfidenceLocalization.regularized_policy_power_pair
#print axioms ThresholdHC.ConfidenceLocalization.reseed_affinity
#print axioms ThresholdHC.ConfidenceLocalization.selected_affinity
#print axioms ThresholdHC.ConfidenceLocalization.statistic_common_support
#print axioms ThresholdHC.ConfidenceLocalization.statistic_law_const_domination
#print axioms ThresholdHC.ConfidenceLocalization.statistic_law_midpoint
#print axioms ThresholdHC.ConfidenceLocalization.statistic_mass_midpoint
#print axioms ThresholdHC.ConfidenceLocalization.tape_law_mono
#print axioms ThresholdHC.ConfidenceLocalization.tape_law_smul
#print axioms ThresholdHC.ConfidenceLocalization.tape_midpoint_law
