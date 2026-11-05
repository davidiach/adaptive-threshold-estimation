import ThresholdHC.RMSLocalization.Full
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory InformationTheory Set Real
open scoped ENNReal NNReal
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier4
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceLocalization
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.ConfidenceTransfer
open ThresholdHC.AdditiveConfidence ThresholdHC.RMSLocalization

example : ∀ {I R : Type} [Fintype I] [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (M : GapMixture I μ) (A : AdaptiveEstimator R)
    (ρ b J : I → ℝ) {ρtotal B : ℝ}
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hρ : ∑ i, (M.weight i : ℝ)*ρ i ≤ ρtotal)
    (cp : ∀ i, CommonPairBound (M.law i) (ρ i) (b i) (J i))
    (hw : RareBudget μ A ρtotal B),
    ENNReal.ofReal ((∑ i, (M.weight i : ℝ)*min (b i) (Real.sqrt (J i/B)))/128) ≤ rareRisk μ A ρtotal :=
  @ThresholdHC.RMSLocalization.rms_rate_of_mixture

example : ∀ (P Q : Measure Bool)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hp : P.real {true} ≤ 1/4) (hq : Q.real {false} ≤ 1/4),
    (hellingerAffinity P Q).toReal ≤ 7/8 :=
  @ThresholdHC.RMSLocalization.bool_affinity_quarter_errors

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {ρ b J B : ℝ} (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B)
    (cp : CommonPairBound μ ρ b J) (hw : RareBudget μ A ρ B),
    ENNReal.ofReal (min b (Real.sqrt (J/B))/128) ≤ rareRisk μ A ρ :=
  @ThresholdHC.RMSLocalization.rms_rate_of_common_pair

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {ρ b J B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B)
    (hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b J)
    (hw : RareBudget μ A ρ B),
    ENNReal.ofReal (min b (Real.sqrt (J/B))/128) ≤ rareRisk μ A ρ :=
  @ThresholdHC.RMSLocalization.rms_rate_of_obstruction

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ b J B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B)
    (hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b J),
    ENNReal.ofReal (min b (Real.sqrt (J/B))/128) ≤ rareMinimaxRisk μ ρ B :=
  @ThresholdHC.RMSLocalization.minimax_rms_of_obstruction

example : ∀ {D : Type} [MeasurableSpace D] (μ : Measure D)
    [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (hqhalf : ∀ x, (q x : ℝ) ≤ 1/2) (hrhalf : ∀ x, (r x : ℝ) ≤ 1/2)
    (d : D → ℝ) (hdm : Measurable d) (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x) (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option ℕ) (n : ℕ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hlocal : LocalNullWorkBound μ p₀ p₁ q r κ),
    let w := fun (u : D → unitInterval) =>
      creationPopulationWeight (n := n) μ pol d (fun x => (u x : ℝ))
    1-realFiniteAffinity (w q) (w r) ≤
      2*κ*∑ z, w (midpointPrior q r) z*ThresholdHC.workOf z :=
  @ThresholdHC.RMSLocalization.creation_null_hellinger

example : ∀ {I R : Type} [Fintype I] [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (M : GapMixture I μ) (A : AdaptiveEstimator R)
    (ρ b J : I → ℝ) {ρtotal B : ℝ}
    (hρpos : ∀ i, 0 < ρ i) (hρquarter : ∀ i, ρ i ≤ 1/4)
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hρ : ∑ i, (M.weight i : ℝ)*ρ i ≤ ρtotal)
    (hobs : ∀ i, NullVarianceObstruction (M.law i)
      (gapParameter false) (gapParameter true) (ρ i) (b i) (J i))
    (hw : RareBudget μ A ρtotal B),
    ENNReal.ofReal ((∑ i, (M.weight i : ℝ)*min (b i) (Real.sqrt (J i/B)))/128) ≤ rareRisk μ A ρtotal :=
  @ThresholdHC.RMSLocalization.rms_rate_of_obstructions

example : ∀ {I R : Type} [Fintype I] [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (σ : I → Measure Gap)
    (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0)
    (A : AdaptiveEstimator R) (ρ b J : I → ℝ) {ρtotal B : ℝ}
    (hρpos : ∀ i, 0 < ρ i) (hρquarter : ∀ i, ρ i ≤ 1/4)
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hρ : ∑ i, (σ i).real Set.univ*ρ i ≤ ρtotal)
    (hobs : ∀ i, NullVarianceObstruction (normalizedGapLaw (σ i))
      (gapParameter false) (gapParameter true) (ρ i) (b i) (J i))
    (hw : RareBudget μ A ρtotal B),
    ENNReal.ofReal ((∑ i, (σ i).real Set.univ*min (b i) (Real.sqrt (J i/B)))/128) ≤ rareRisk μ A ρtotal :=
  @ThresholdHC.RMSLocalization.rms_rate_of_submeasures

example : ∀ {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (σ : I → Measure Gap)
    (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0)
    (ρ b J : I → ℝ) {ρtotal B : ℝ}
    (hρpos : ∀ i, 0 < ρ i) (hρquarter : ∀ i, ρ i ≤ 1/4)
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hρ : ∑ i, (σ i).real Set.univ*ρ i ≤ ρtotal)
    (hobs : ∀ i, NullVarianceObstruction (normalizedGapLaw (σ i))
      (gapParameter false) (gapParameter true) (ρ i) (b i) (J i)),
    ENNReal.ofReal ((∑ i, (σ i).real Set.univ*min (b i) (Real.sqrt (J i/B)))/128) ≤ rareMinimaxRisk μ ρtotal B :=
  @ThresholdHC.RMSLocalization.minimax_rms_of_submeasures

example : ∀ (q r : SignLaw),
    signUnit (ThresholdHC.StoppingProgram.midpointPrior q r) =
      midpointPrior (signUnit q) (signUnit r) :=
  @ThresholdHC.RMSLocalization.signUnit_midpoint

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q r : SignLaw)
    (hqhalf : ∀ d, q.val d ≤ 1/2) (hrhalf : ∀ d, r.val d ≤ 1/2)
    (n : ℕ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hloc : LocalNullWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) κ),
    1-(hellingerAffinity (observablePrefixLaw μ A q n) (observablePrefixLaw μ A r n)).toReal ≤
      2*κ*∫ z, ThresholdHC.workOf (processPrefix n z.2)
        ∂experimentLaw μ A (ThresholdHC.StoppingProgram.midpointPrior q r) :=
  @ThresholdHC.RMSLocalization.observable_null_hellinger

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q r : SignLaw)
    {ρ B κ δ : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r)
    (hqhalf : ∀ d, q.val d ≤ 1/2) (hrhalf : ∀ d, r.val d ≤ 1/2)
    (hloc : LocalNullWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) κ)
    (hw : RareBudget μ A ρ B) (hinfo : 2*κ*B ≤ 1/10)
    (hsep : δ ≤ signMean μ r.val-signMean μ q.val),
    ENNReal.ofReal (δ/4) ≤ rareRisk μ A ρ :=
  @ThresholdHC.RMSLocalization.pair_rms_risk

example : ∀ {R I : Type} [MeasurableSpace R]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q r : SignLaw)
    (hqhalf : ∀ d, q.val d ≤ 1/2) (hrhalf : ∀ d, r.val d ≤ 1/2)
    (κ B : ℝ) (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hloc : LocalNullWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) κ)
    (hwq : expectedWork μ A q < ∞) (hwr : expectedWork μ A r < ∞)
    (hwm : expectedWork μ A (ThresholdHC.StoppingProgram.midpointPrior q r) ≤ ENNReal.ofReal B)
    (f : R × ProcessTape → I) (hf : Measurable f),
    1-(hellingerAffinity (observableDecisionLaw μ A q f) (observableDecisionLaw μ A r f)).toReal ≤ 2*κ*B :=
  @ThresholdHC.RMSLocalization.terminal_null_hellinger

example : ∀ {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (a b : ℝ) (hf : Measurable f) (hab : a < b)
    (haff : (9/10:ℝ) ≤ (hellingerAffinity
      (P.map (thresholdDecision f ((a+b)/2)))
      (Q.map (thresholdDecision f ((a+b)/2)))).toReal),
    ENNReal.ofReal ((b-a)^2/16) ≤ max (Tier6.squaredRisk P f a) (Tier6.squaredRisk Q f b) :=
  @ThresholdHC.RMSLocalization.squared_risk_lower_of_affinity

example : ∀ {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) (f : Ω → ℝ) (a b δ : ℝ) (hδ : 0 ≤ δ) (hsep : δ ≤ b-a)
    (hsq : ENNReal.ofReal ((b-a)^2/16) ≤
      max (Tier6.squaredRisk P f a) (Tier6.squaredRisk Q f b)),
    ENNReal.ofReal (δ/4) ≤ max (Tier6.rootMeanRisk P f a) (Tier6.rootMeanRisk Q f b) :=
  @ThresholdHC.RMSLocalization.rms_pair_lower
#print axioms ThresholdHC.RMSLocalization.bool_affinity_quarter_errors
#print axioms ThresholdHC.RMSLocalization.creation_null_hellinger
#print axioms ThresholdHC.RMSLocalization.minimax_rms_of_obstruction
#print axioms ThresholdHC.RMSLocalization.minimax_rms_of_submeasures
#print axioms ThresholdHC.RMSLocalization.observable_null_hellinger
#print axioms ThresholdHC.RMSLocalization.pair_rms_risk
#print axioms ThresholdHC.RMSLocalization.rms_pair_lower
#print axioms ThresholdHC.RMSLocalization.rms_rate_of_common_pair
#print axioms ThresholdHC.RMSLocalization.rms_rate_of_mixture
#print axioms ThresholdHC.RMSLocalization.rms_rate_of_obstruction
#print axioms ThresholdHC.RMSLocalization.rms_rate_of_obstructions
#print axioms ThresholdHC.RMSLocalization.rms_rate_of_submeasures
#print axioms ThresholdHC.RMSLocalization.signUnit_midpoint
#print axioms ThresholdHC.RMSLocalization.squared_risk_lower_of_affinity
#print axioms ThresholdHC.RMSLocalization.terminal_null_hellinger
