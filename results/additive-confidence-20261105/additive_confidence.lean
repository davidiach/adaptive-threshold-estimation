import ThresholdHC.AdditiveConfidence.Full
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier4
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceLocalization
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.ConfidenceTransfer
open ThresholdHC.AdditiveConfidence

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ b J B ℓ : ℝ} (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B) (hℓ : 0 < ℓ)
    (cp : CommonPairBound μ ρ b J),
    ∃ q r : SignLaw, RarePrior μ ρ q ∧ RarePrior μ ρ r ∧
      (∀ d, q.val d ≤ 1/2) ∧ (∀ d, r.val d ≤ 1/2) ∧
      min b (Real.sqrt (J*ℓ/B))/32 ≤ signMean μ r.val-signMean μ q.val ∧
      LocalNullWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r)
        (42*ℓ/(1024*B)) :=
  @ThresholdHC.AdditiveConfidence.component_pair_uniform

example : ∀ {I R : Type} [Fintype I] [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (M : GapMixture I μ) (A : AdaptiveEstimator R)
    (ρ b J : I → ℝ) {ρtotal B ε δ : ℝ}
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hρ : ∑ i, (M.weight i : ℝ)*ρ i ≤ ρtotal)
    (cp : ∀ i, CommonPairBound (M.law i) (ρ i) (b i) (J i))
    (hw : RareBudget μ A ρtotal B)
    (hconf : ∀ u : SignLaw, RarePrior μ ρtotal u →
      ThresholdHC.Confidence.failureProbability μ A u ε ≤ ENNReal.ofReal δ),
    (∑ i, (M.weight i : ℝ)*min (b i) (Real.sqrt (J i*Real.log (1/δ)/B)))/128 ≤ ε :=
  @ThresholdHC.AdditiveConfidence.confidence_rate_of_mixture

example : ∀ {I : Type} [Fintype I] {μ : Measure Gap}
    (M : GapMixture I μ),
    M.residual ≤ μ :=
  @ThresholdHC.AdditiveConfidence.GapMixture.residual_le

example : ∀ {I : Type} [Fintype I] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ),
    M.residual.real Set.univ + ∑ i, (M.weight i : ℝ) = 1 :=
  @ThresholdHC.AdditiveConfidence.GapMixture.mass_balance

example : ∀ {I : Type} [Fintype I] {μ : Measure Gap}
    (M : GapMixture I μ) (i : I),
    M.weight i • M.law i ≤ μ :=
  @ThresholdHC.AdditiveConfidence.GapMixture.component_le

example : ∀ {I Z : Type} [Fintype I] [Fintype Z]
    (p q : I → Z → ℝ) (hp : ∀ i z, 0 ≤ p i z) (hq : ∀ i z, 0 ≤ q i z),
    ∑ i, realFiniteAffinity (p i) (q i) ≤
      realFiniteAffinity (fun z => ∑ i, p i z) (fun z => ∑ i, q i z) :=
  @ThresholdHC.AdditiveConfidence.finite_affinity_sum

example : ∀ {Z : Type} [Fintype Z]
    (p q : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (a : ℝ) (ha : 0 ≤ a),
    realFiniteAffinity (fun z => a*p z) (fun z => a*q z) =
      a*realFiniteAffinity p q :=
  @ThresholdHC.AdditiveConfidence.finite_affinity_scale

example : ∀ {Z : Type} [Fintype Z]
    (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z),
    realFiniteAffinity p p = ∑ z, p z :=
  @ThresholdHC.AdditiveConfidence.finite_affinity_self

example : ∀ {I Z : Type} [Fintype I] [Fintype Z]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (p q : I → Z → ℝ)
    (hp : ∀ i z, 0 ≤ p i z) (hq : ∀ i z, 0 ≤ q i z)
    (res : Z → ℝ) (hr : ∀ z, 0 ≤ res z) (hmass : (∑ z, res z)+(∑ i, w i) = 1),
    1-realFiniteAffinity (fun z => res z+∑ i, w i*p i z) (fun z => res z+∑ i, w i*q i z) ≤
      ∑ i, w i*(1-realFiniteAffinity (p i) (q i)) :=
  @ThresholdHC.AdditiveConfidence.finite_mixture_loss

example : ∀ {I R : Type} [Fintype I] [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (M : GapMixture I μ) (A : AdaptiveEstimator R)
    (ρ b J : I → ℝ) {ρtotal B ε δ : ℝ}
    (hρpos : ∀ i, 0 < ρ i) (hρquarter : ∀ i, ρ i ≤ 1/4)
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hρ : ∑ i, (M.weight i : ℝ)*ρ i ≤ ρtotal)
    (hobs : ∀ i, NullVarianceObstruction (M.law i)
      (gapParameter false) (gapParameter true) (ρ i) (b i) (J i))
    (hw : RareBudget μ A ρtotal B)
    (hconf : ∀ u : SignLaw, RarePrior μ ρtotal u →
      ThresholdHC.Confidence.failureProbability μ A u ε ≤ ENNReal.ofReal δ),
    (∑ i, (M.weight i : ℝ)*min (b i) (Real.sqrt (J i*Real.log (1/δ)/B)))/128 ≤ ε :=
  @ThresholdHC.AdditiveConfidence.confidence_rate_of_obstructions

example : ∀ {I R : Type} [Fintype I] [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (σ : I → Measure Gap)
    (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0)
    (A : AdaptiveEstimator R) (ρ b J : I → ℝ) {ρtotal B ε δ : ℝ}
    (hρpos : ∀ i, 0 < ρ i) (hρquarter : ∀ i, ρ i ≤ 1/4)
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hρ : ∑ i, (σ i).real Set.univ*ρ i ≤ ρtotal)
    (hobs : ∀ i, NullVarianceObstruction (normalizedGapLaw (σ i))
      (gapParameter false) (gapParameter true) (ρ i) (b i) (J i))
    (hw : RareBudget μ A ρtotal B)
    (hconf : ∀ u : SignLaw, RarePrior μ ρtotal u →
      ThresholdHC.Confidence.failureProbability μ A u ε ≤ ENNReal.ofReal δ),
    (∑ i, (σ i).real Set.univ*min (b i) (Real.sqrt (J i*Real.log (1/δ)/B)))/128 ≤ ε :=
  @ThresholdHC.AdditiveConfidence.confidence_rate_of_submeasures

example : ∀ {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (σ : I → Measure Gap)
    (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0)
    (ρ b J : I → ℝ) {ρtotal B δ : ℝ}
    (hρpos : ∀ i, 0 < ρ i) (hρquarter : ∀ i, ρ i ≤ 1/4)
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hρ : ∑ i, (σ i).real Set.univ*ρ i ≤ ρtotal)
    (hobs : ∀ i, NullVarianceObstruction (normalizedGapLaw (σ i))
      (gapParameter false) (gapParameter true) (ρ i) (b i) (J i)),
    ENNReal.ofReal ((∑ i, (σ i).real Set.univ*min (b i)
      (Real.sqrt (J i*Real.log (1/δ)/B)))/128) ≤ rareConfidenceRadius μ ρtotal B δ :=
  @ThresholdHC.AdditiveConfidence.minimax_confidence_of_submeasures

example : ∀ (μ σ : Measure Gap) (d : Gap),
    (halfSign μ σ).val d ≤ 1/2 :=
  @ThresholdHC.AdditiveConfidence.halfSign_le_half

example : ∀ {X : Type} [MeasurableSpace X] (μ σ : Measure X)
    (h : (2 : ℝ≥0) • σ ≤ μ),
    σ ≤ μ :=
  @ThresholdHC.AdditiveConfidence.measure_le_of_twice_le

example : ∀ (μ σ : Measure Gap) [IsProbabilityMeasure μ] [IsFiniteMeasure σ]
    (h : (2 : ℝ≥0) • σ ≤ μ),
    μ.withDensity (fun d => ENNReal.ofReal ((halfSign μ σ).val d)) = σ :=
  @ThresholdHC.AdditiveConfidence.halfSign_density

example : ∀ (μ σ : Measure Gap) [IsProbabilityMeasure μ] [IsFiniteMeasure σ]
    (h : (2 : ℝ≥0) • σ ≤ μ) (F : Gap → ℝ),
    (∫ d, (halfSign μ σ).val d*F d ∂μ) = ∫ d, F d ∂σ :=
  @ThresholdHC.AdditiveConfidence.halfSign_integral

example : ∀ (μ σ : Measure Gap) [IsProbabilityMeasure μ] [IsFiniteMeasure σ]
    (h : (2 : ℝ≥0) • σ ≤ μ),
    signMean μ (halfSign μ σ).val = σ.real Set.univ :=
  @ThresholdHC.AdditiveConfidence.halfSign_mean

example : ∀ {I : Type} [Fintype I] (κ : I → Measure unitInterval),
    parameterTapeLaw (∑ i, κ i) = ∑ i, parameterTapeLaw (κ i) :=
  @ThresholdHC.AdditiveConfidence.tape_law_sum

example : ∀ {I R : Type} [Fintype I] [MeasurableSpace R]
    (ν : Measure R) [SFinite ν] (η : Measure unitInterval) [IsFiniteMeasure η]
    (κ : I → Measure unitInterval) [∀ i, IsFiniteMeasure (κ i)] (w : I → ℝ≥0),
    ν.prod (parameterTapeLaw (η+∑ i, w i • κ i)) =
      ν.prod (parameterTapeLaw η)+∑ i, w i • (ν.prod (parameterTapeLaw (κ i))) :=
  @ThresholdHC.AdditiveConfidence.input_law_mixture

example : ∀ {I R : Type} [Fintype I] [MeasurableSpace R] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ) (ν : Measure R) [SFinite ν]
    (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q : I → SignLaw) (hq : ∀ i d, (q i).val d ≤ 1/2),
    ν.prod (parameterTapeLaw (populationParameterLaw μ p₀ p₁ (signUnit (M.mixedSign q)))) =
      ν.prod (parameterTapeLaw (M.residual.map p₀))+
        ∑ i, M.weight i • (ν.prod (parameterTapeLaw (populationParameterLaw (M.law i) p₀ p₁ (signUnit (q i))))) :=
  @ThresholdHC.AdditiveConfidence.GapMixture.input_law

example : ∀ {I : Type} [Fintype I] {μ : Measure Gap} [IsProbabilityMeasure μ]
    (M : GapMixture I μ) (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q r : I → SignLaw) (hq : ∀ i d, (q i).val d ≤ 1/2) (hr : ∀ i d, (r i).val d ≤ 1/2)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hloc : ∀ i, LocalNullWorkBound (M.law i) p₀ p₁ (signUnit (q i)) (signUnit (r i)) κ),
    LocalNullWorkBound μ p₀ p₁ (signUnit (M.mixedSign q)) (signUnit (M.mixedSign r)) κ :=
  @ThresholdHC.AdditiveConfidence.GapMixture.local_bound

example : ∀ (μ : Measure Gap) (q : SignLaw),
    positiveMeasure μ q+positiveMeasure μ (complementSign q) = μ :=
  @ThresholdHC.AdditiveConfidence.positive_complement_sum

example : ∀ {I : Type} [Fintype I] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ) (q : I → SignLaw)
    (hq : ∀ i d, (q i).val d ≤ 1/2),
    positiveMeasure μ (complementSign (M.mixedSign q)) =
      M.residual+∑ i, M.weight i • positiveMeasure (M.law i) (complementSign (q i)) :=
  @ThresholdHC.AdditiveConfidence.GapMixture.mixedSign_complement

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (q : SignLaw),
    populationParameterLaw μ p₀ p₁ (signUnit q) =
      (positiveMeasure μ q).map p₁+(positiveMeasure μ (complementSign q)).map p₀ :=
  @ThresholdHC.AdditiveConfidence.parameter_positive_negative

example : ∀ {I : Type} [Fintype I] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ)
    (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q : I → SignLaw) (hq : ∀ i d, (q i).val d ≤ 1/2),
    populationParameterLaw μ p₀ p₁ (signUnit (M.mixedSign q)) =
      M.residual.map p₀+∑ i, M.weight i • populationParameterLaw (M.law i) p₀ p₁ (signUnit (q i)) :=
  @ThresholdHC.AdditiveConfidence.GapMixture.parameter_law

example : ∀ (μ : Measure Gap) (q : SignLaw),
    positiveMeasure μ q ≤ μ :=
  @ThresholdHC.AdditiveConfidence.positiveMeasure_le

example : ∀ (μ : Measure Gap) (q : SignLaw) (hq : ∀ d, q.val d ≤ 1/2),
    (2 : ℝ≥0) • positiveMeasure μ q ≤ μ :=
  @ThresholdHC.AdditiveConfidence.positiveMeasure_twice_le

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (F : Gap → ℝ),
    (∫ d, q.val d*F d ∂μ) = ∫ d, F d ∂positiveMeasure μ q :=
  @ThresholdHC.AdditiveConfidence.positiveMeasure_integral

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (positiveMeasure μ q).real Set.univ = signMean μ q.val :=
  @ThresholdHC.AdditiveConfidence.positiveMeasure_mass

example : ∀ {I : Type} [Fintype I] {μ : Measure Gap}
    (M : GapMixture I μ) (q : I → SignLaw) (hq : ∀ i d, (q i).val d ≤ 1/2),
    (2 : ℝ≥0) • M.positiveMass q ≤ μ :=
  @ThresholdHC.AdditiveConfidence.GapMixture.positiveMass_twice_le

example : ∀ {I : Type} [Fintype I] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ) (q : I → SignLaw)
    (hq : ∀ i d, (q i).val d ≤ 1/2),
    positiveMeasure μ (M.mixedSign q) = M.positiveMass q :=
  @ThresholdHC.AdditiveConfidence.GapMixture.mixedSign_density

example : ∀ {I : Type} [Fintype I] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ) (q : I → SignLaw)
    (hq : ∀ i d, (q i).val d ≤ 1/2),
    signMean μ (M.mixedSign q).val = ∑ i, (M.weight i : ℝ)*signMean (M.law i) (q i).val :=
  @ThresholdHC.AdditiveConfidence.GapMixture.mixedSign_mean

example : ∀ {I R E : Type} [Fintype I]
    [MeasurableSpace R] [MeasurableSpace E] {μ : Measure Gap} [IsProbabilityMeasure μ]
    (M : GapMixture I μ) (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q : I → SignLaw) (hq : ∀ i d, (q i).val d ≤ 1/2)
    (A : StoppedProcedure R E) (n : ℕ) (z : Fin (n+1) × Fin (n+1)),
    (cappedStatisticLaw μ ν p₀ p₁ (signUnit (M.mixedSign q)) A n).real {z} =
      (tapeStatisticLaw ν (M.residual.map p₀) A n).real {z}+
        ∑ i, (M.weight i : ℝ)*(cappedStatisticLaw (M.law i) ν p₀ p₁ (signUnit (q i)) A n).real {z} :=
  @ThresholdHC.AdditiveConfidence.GapMixture.statistic_mass

example : ∀ {I R E : Type} [Fintype I]
    [MeasurableSpace R] [MeasurableSpace E] {μ : Measure Gap} [IsProbabilityMeasure μ]
    (M : GapMixture I μ) (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ : Gap → unitInterval) (h₀ : Measurable p₀) (A : StoppedProcedure R E) (n : ℕ),
    (∑ z, (tapeStatisticLaw ν (M.residual.map p₀) A n).real {z})+
      ∑ i, (M.weight i : ℝ) = 1 :=
  @ThresholdHC.AdditiveConfidence.GapMixture.statistic_mass_balance

example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (κ : Measure unitInterval) [IsFiniteMeasure κ]
    (A : StoppedProcedure R E) (n : ℕ),
    (tapeStatisticLaw ν κ A n).real Set.univ = κ.real Set.univ :=
  @ThresholdHC.AdditiveConfidence.tapeStatisticLaw_mass

example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q : SignLaw) (A : StoppedProcedure R E) (n : ℕ),
    cappedStatisticLaw μ ν p₀ p₁ (signUnit q) A n =
      tapeStatisticLaw ν (populationParameterLaw μ p₀ p₁ (signUnit q)) A n :=
  @ThresholdHC.AdditiveConfidence.capped_statistic_tape

example : ∀ {I R E : Type} [Fintype I]
    [MeasurableSpace R] [MeasurableSpace E] {μ : Measure Gap} [IsProbabilityMeasure μ]
    (M : GapMixture I μ) (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q : I → SignLaw) (hq : ∀ i d, (q i).val d ≤ 1/2) (A : StoppedProcedure R E) (n : ℕ),
    cappedStatisticLaw μ ν p₀ p₁ (signUnit (M.mixedSign q)) A n =
      tapeStatisticLaw ν (M.residual.map p₀) A n+
        ∑ i, M.weight i • cappedStatisticLaw (M.law i) ν p₀ p₁ (signUnit (q i)) A n :=
  @ThresholdHC.AdditiveConfidence.GapMixture.statistic_law

example : ∀ {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (σ : I → Measure Gap)
    (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0) (i : I),
    (submeasureMixture μ σ hs hn).law i = normalizedGapLaw (σ i) :=
  @ThresholdHC.AdditiveConfidence.submeasureMixture_law

example : ∀ {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (σ : I → Measure Gap)
    (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0) (i : I),
    ((submeasureMixture μ σ hs hn).weight i : ℝ) = (σ i).real Set.univ :=
  @ThresholdHC.AdditiveConfidence.submeasureMixture_weight

example : ∀ {I R E : Type} [Fintype I]
    [MeasurableSpace R] [MeasurableSpace E] {μ : Measure Gap} [IsProbabilityMeasure μ]
    (M : GapMixture I μ) (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : Gap → unitInterval) (A : StoppedProcedure R E),
    populationExpectedWork μ ν p₀ p₁ q A =
      populationExpectedWork M.residual ν p₀ p₁ q A+
        ∑ i, (M.weight i : ℝ≥0∞)*populationExpectedWork (M.law i) ν p₀ p₁ q A :=
  @ThresholdHC.AdditiveConfidence.GapMixture.work_decomposition

example : ∀ {I R E : Type} [Fintype I]
    [MeasurableSpace R] [MeasurableSpace E] {μ : Measure Gap} [IsProbabilityMeasure μ]
    (M : GapMixture I μ) (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : Gap → unitInterval) (A : StoppedProcedure R E)
    (n : ℕ) (hcap : ∀ z, A.stop z ≤ n),
    (∑ i, (M.weight i : ℝ)*(populationExpectedWork (M.law i) ν p₀ p₁ q A).toReal) ≤
      (populationExpectedWork μ ν p₀ p₁ q A).toReal :=
  @ThresholdHC.AdditiveConfidence.GapMixture.component_work_le
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.component_le
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.component_work_le
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.input_law
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.local_bound
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.mass_balance
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.mixedSign_complement
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.mixedSign_density
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.mixedSign_mean
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.parameter_law
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.positiveMass_twice_le
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.residual_le
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.statistic_law
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.statistic_mass
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.statistic_mass_balance
#print axioms ThresholdHC.AdditiveConfidence.GapMixture.work_decomposition
#print axioms ThresholdHC.AdditiveConfidence.capped_statistic_tape
#print axioms ThresholdHC.AdditiveConfidence.component_pair_uniform
#print axioms ThresholdHC.AdditiveConfidence.confidence_rate_of_mixture
#print axioms ThresholdHC.AdditiveConfidence.confidence_rate_of_obstructions
#print axioms ThresholdHC.AdditiveConfidence.confidence_rate_of_submeasures
#print axioms ThresholdHC.AdditiveConfidence.finite_affinity_scale
#print axioms ThresholdHC.AdditiveConfidence.finite_affinity_self
#print axioms ThresholdHC.AdditiveConfidence.finite_affinity_sum
#print axioms ThresholdHC.AdditiveConfidence.finite_mixture_loss
#print axioms ThresholdHC.AdditiveConfidence.halfSign_density
#print axioms ThresholdHC.AdditiveConfidence.halfSign_integral
#print axioms ThresholdHC.AdditiveConfidence.halfSign_le_half
#print axioms ThresholdHC.AdditiveConfidence.halfSign_mean
#print axioms ThresholdHC.AdditiveConfidence.input_law_mixture
#print axioms ThresholdHC.AdditiveConfidence.measure_le_of_twice_le
#print axioms ThresholdHC.AdditiveConfidence.minimax_confidence_of_submeasures
#print axioms ThresholdHC.AdditiveConfidence.parameter_positive_negative
#print axioms ThresholdHC.AdditiveConfidence.positiveMeasure_integral
#print axioms ThresholdHC.AdditiveConfidence.positiveMeasure_le
#print axioms ThresholdHC.AdditiveConfidence.positiveMeasure_mass
#print axioms ThresholdHC.AdditiveConfidence.positiveMeasure_twice_le
#print axioms ThresholdHC.AdditiveConfidence.positive_complement_sum
#print axioms ThresholdHC.AdditiveConfidence.submeasureMixture_law
#print axioms ThresholdHC.AdditiveConfidence.submeasureMixture_weight
#print axioms ThresholdHC.AdditiveConfidence.tapeStatisticLaw_mass
#print axioms ThresholdHC.AdditiveConfidence.tape_law_sum
