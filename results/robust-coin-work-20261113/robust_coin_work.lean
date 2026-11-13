
import ThresholdHC.RobustContinuation.RobustCoinWork
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set Real
open scoped ENNReal NNReal BigOperators
open ThresholdHC.RobustContinuation
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.Uniform713 ThresholdHC.BlindUpper ThresholdHC.EntropyTailUpper

example : ∀ {M : ℝ} (hM : 0 < M) {d d' : Gap} (h : (d:ℝ) ≤ d'),
    ordinaryWorkKernel M (d':ℝ) ≤ ordinaryWorkKernel M (d:ℝ) := @ordinaryWorkKernel_antitone_gap
example : ∀ (neg pos : PrefixTest) (L : ℕ) (s : Bool) {d₀ d : Gap} (h : (d₀:ℝ) ≤ d),
    (∫ ω, (raceCost neg pos L ω : ℝ) ∂tapeMeasure (gapParameter s d)) ≤
      2*ordinaryWorkKernel (cap L) (d₀:ℝ) := @race_work_le_ordinary_of_le
example : ∀ {d d' r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (h : d ≤ d'),
    negativeReferenceDrift d r ≤ negativeReferenceDrift d' r := @negativeReferenceDrift_mono
example : ∀ {d₀ d : Gap} (h : (d₀:ℝ) ≤ d) {r b : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (hdr : (d₀:ℝ)/2 ≤ r) (hrd : r ≤ (d₀:ℝ)) (hb : 0 ≤ b) (M : ℕ),
    (∫ ω, (scoreStop (negativeBitScore r) b M ω : ℝ) ∂tapeMeasure (gapParameter false d)) ≤
      (3/(4*(d₀:ℝ)^2))*(1+b) := @negative_scoreStop_work_of_le
example : ∀ (μ : Measure Gap) (weights : ℕ → ℝ≥0) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (u : ℝ) (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d),
    (∫ ω, (raceCost (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω : ℝ)
      ∂tapeMeasure (gapParameter false d)) ≤
      (3/(2*(d₀:ℝ)^2))*(1+log (ε*(weights j:ℝ))⁻¹) := @bank_race_negative_work_of_le
example : ∀ (n : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω'),
    prefixMean observations n ω ≤ prefixMean observations n ω' := @prefixMean_mono
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (weights : ℕ → ℝ≥0) (ε : ℝ) {u V U : ℝ} (hu : 0 ≤ u) (j L : ℕ) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d) {n : ℕ} (hn : 0 < n) (hU : U ≤ n*(d₀:ℝ)^2/3) (hLap : nullLaplace μ n ≤ V) (hV : V ≤ u*(weights j:ℝ)*exp U),
    (tapeMeasure (gapParameter true d)).real
      {ω | n < raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω} ≤
      exp (-(n:ℝ)*(d₀:ℝ)^2/2) := @positive_race_survival_of_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (weights : ℕ → ℝ≥0) (ε : ℝ) {u V U : ℝ} (hu : 0 ≤ u) (hU : 1 ≤ U) (j L : ℕ) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d) (hLap : ∀ n : ℕ, 1 ≤ n*(d₀:ℝ)^2 → nullLaplace μ n ≤ V) (hV : V ≤ u*(weights j:ℝ)*exp U),
    (∫ ω, (raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω : ℝ)
      ∂tapeMeasure (gapParameter true d)) ≤ 6*U/(d₀:ℝ)^2 := @positive_raceRounds_work_of_le
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] (hσ : Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ) (hτ : Integrable (fun x : Gap => (x:ℝ)⁻¹) τ) (weights : ℕ → ℝ≥0) {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d),
    (∫ ω, (raceCost (negativeBankTest weights ε) (positiveBankTest (σ+τ+ζ) weights (ρ*ε)) L ω : ℝ)
      ∂tapeMeasure (gapParameter true d)) ≤
      12*positiveAllowance ε (weights j:ℝ) ρ (threePieceEnvelope σ τ ζ d₀)/(d₀:ℝ)^2 := @bank_race_positive_work_of_le
#print axioms ThresholdHC.RobustContinuation.bank_race_negative_work_of_le
#print axioms ThresholdHC.RobustContinuation.bank_race_positive_work_of_le
#print axioms ThresholdHC.RobustContinuation.negativeReferenceDrift_mono
#print axioms ThresholdHC.RobustContinuation.negative_scoreStop_work_of_le
#print axioms ThresholdHC.RobustContinuation.ordinaryWorkKernel_antitone_gap
#print axioms ThresholdHC.RobustContinuation.positive_raceRounds_work_of_le
#print axioms ThresholdHC.RobustContinuation.positive_race_survival_of_le
#print axioms ThresholdHC.RobustContinuation.prefixMean_mono
#print axioms ThresholdHC.RobustContinuation.race_work_le_ordinary_of_le
