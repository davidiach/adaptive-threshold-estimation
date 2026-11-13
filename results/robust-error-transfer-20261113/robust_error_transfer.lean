
import ThresholdHC.RobustContinuation.RobustLevelError
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open ThresholdHC.RobustContinuation
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.BlindUpper ThresholdHC.EntropyTailUpper ThresholdHC.RareAboveTwo

example : ∀ (t : PrefixTest), DownwardTest t ↔
    ∀ (n : ℕ) (w w' : Fin n → Bool), w ≤ w' → t n w' → t n w := fun _ => Iff.rfl
example : ∀ (t : PrefixTest), UpwardTest t ↔
    ∀ (n : ℕ) (w w' : Fin n → Bool), w ≤ w' → t n w → t n w' := fun _ => Iff.rfl
example : ∀ (π : Measure (Gap × Gap)) (q : SignLaw) (neg pos : PrefixTest) (L : ℕ),
    coupledRaceError π q neg pos L =
      ∫ z, q.val z.2 * raceConditionalError neg pos L true z.1 +
        (1 - q.val z.2) * raceConditionalError neg pos L false z.1 ∂π := by
  intros; rfl
example : ∀ {p p' : unitInterval} (h : (p:ℝ) ≤ p') (u : ℝ),
    uniformCoinFlip p u ≤ uniformCoinFlip p' u := @uniformCoinFlip_mono
example : ∀ {p p' : unitInterval} (h : (p:ℝ) ≤ p') (u : ℕ → ℝ),
    uniformCoinTape p u ≤ uniformCoinTape p' u := @uniformCoinTape_mono
example : ∀ {p p' : unitInterval} (h : (p:ℝ) ≤ p') {E : Set (ℕ → Bool)} (hE : MeasurableSet E) (hup : IsUpperSet E),
    tapeMeasure p E ≤ tapeMeasure p' E := @tapeMeasure_le_of_isUpperSet
example : ∀ {p p' : unitInterval} (h : (p:ℝ) ≤ p') {E : Set (ℕ → Bool)} (hE : MeasurableSet E) (hlow : IsLowerSet E),
    tapeMeasure p' E ≤ tapeMeasure p E := @tapeMeasure_le_of_isLowerSet
example : ∀ (n : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω'),
    tapePrefix n ω ≤ tapePrefix n ω' := @tapePrefix_mono
example : ∀ {b b' : Bool} (h : b ≤ b'),
    bit b ≤ bit b' := @bit_mono
example : ∀ {p : ℝ} (hp : 1/2 ≤ p) (hp1 : p ≤ 1) {n : ℕ} {w w' : Fin n → Bool} (h : w ≤ w'),
    streamProb p w ≤ streamProb p w' := @streamProb_mono
example : ∀ {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2) {n : ℕ} {w w' : Fin n → Bool} (h : w ≤ w'),
    streamProb p w' ≤ streamProb p w := @streamProb_anti
example : ∀ (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) (hd : firstDecision b m L = 1),
    1/2 < m (firstStop b m L) := @half_lt_of_firstDecision_one
example : ∀ (b : ℕ → ℕ → ℝ) {m m' : ℕ → ℝ} (h : ∀ k, m k ≤ m' k) (L : ℕ) (hd : firstDecision b m L = 1),
    firstStop b m' L ≤ firstStop b m L := @firstStop_le_of_decision_one
example : ∀ (b : ℕ → ℕ → ℝ) {m m' : ℕ → ℝ} (h : ∀ k, m k ≤ m' k) (L : ℕ) (hlt : firstStop b m' L < firstStop b m L),
    firstDecision b m' L = 1 := @firstDecision_one_of_stop_lt
example : ∀ (b : ℕ → ℕ → ℝ) {m m' : ℕ → ℝ} (h : ∀ k, m k ≤ m' k) (L : ℕ) (hd : firstDecision b m L = 1),
    firstDecision b m' L = 1 := @firstDecision_one_of_le
example : ∀ (k : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω'),
    dyadicMean Tier2.observations k ω ≤ dyadicMean Tier2.observations k ω' := @dyadicMean_mono
example : ∀ (L : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω') (hv : classifierValue L ω = 1),
    classifierStop L ω' ≤ classifierStop L ω := @classifierStop_le_of_value_one
example : ∀ (L : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω') (hlt : classifierStop L ω' < classifierStop L ω),
    classifierValue L ω' = 1 := @classifierValue_one_of_stop_lt
example : ∀ (L : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω') (hv : classifierValue L ω = 1),
    classifierValue L ω' = 1 := @classifierValue_one_of_le
example : ∀ (L : ℕ),
    Monotone (classifierValue L) := @classifierValue_mono
example : ∀ (b : Fin 2) {ω ω' : ℕ → Bool} (h : ω ≤ ω'),
    parityTape b ω ≤ parityTape b ω' := @parityTape_mono
example : ∀ (neg pos : PrefixTest) (L : ℕ) (ω : ℕ → Bool),
    raceValue neg pos L ω = 1 ↔
      ¬ neg (raceRounds neg pos L ω)
      (tapePrefix (raceRounds neg pos L ω) (parityTape 0 ω)) ∧
      (pos (raceRounds neg pos L ω)
      (tapePrefix (raceRounds neg pos L ω) (parityTape 0 ω)) ∨
      classifierValue L (parityTape 1 ω) = 1) := @raceValue_eq_one_iff
example : ∀ {neg pos : PrefixTest} (hneg : DownwardTest neg) (hpos : UpwardTest pos) (L : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω') (h1 : raceValue neg pos L ω = 1),
    raceValue neg pos L ω' = 1 := @raceValue_one_of_le
example : ∀ {neg pos : PrefixTest} (hneg : DownwardTest neg) (hpos : UpwardTest pos) (L : ℕ),
    Monotone (raceValue neg pos L) := @raceValue_mono
example : ∀ (weights : ℕ → ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε),
    DownwardTest (negativeBankTest weights ε) := @negativeBankTest_downward
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {n : ℕ} {w w' : Fin n → Bool} (h : w ≤ w'),
    allNegativeLaw μ (tapePrefix n ⁻¹' {w'}) ≤ allNegativeLaw μ (tapePrefix n ⁻¹' {w}) := @null_prefix_anti
example : ∀ (weights : ℕ → ℝ≥0) {n : ℕ} {w w' : Fin n → Bool} (h : w ≤ w'),
    positiveBankLaw weights (tapePrefix n ⁻¹' {w}) ≤
      positiveBankLaw weights (tapePrefix n ⁻¹' {w'}) := @positiveBank_prefix_mono
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (weights : ℕ → ℝ≥0) (u : ℝ),
    UpwardTest (positiveBankTest μ weights u) := @positiveBankTest_upward
example : ∀ {neg pos : PrefixTest} (hneg : DownwardTest neg) (hpos : UpwardTest pos) (L : ℕ) (s : Bool) {d d' : Gap} (h : (d:ℝ) ≤ d'),
    raceConditionalError neg pos L s d' ≤ raceConditionalError neg pos L s d := @raceConditionalError_antitone
example : ∀ (q : SignLaw) (neg pos : PrefixTest) (L : ℕ),
    Measurable (fun z : Gap × Gap => q.val z.2 * raceConditionalError neg pos L true z.1 +
      (1 - q.val z.2) * raceConditionalError neg pos L false z.1) := @measurable_coupledIntegrand
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (q : SignLaw) (neg pos : PrefixTest) (L : ℕ),
    Integrable (fun z : Gap × Gap => q.val z.2 * raceConditionalError neg pos L true z.1 +
      (1 - q.val z.2) * raceConditionalError neg pos L false z.1) π := @integrable_coupledIntegrand
example : ∀ {neg pos : PrefixTest} (hneg : DownwardTest neg) (hpos : UpwardTest pos) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (q : SignLaw) (L : ℕ),
    racePopulationError (π.map Prod.snd + μ₀) q neg pos L ≤
      coupledRaceError π q neg pos L + μ₀.real univ := @coupled_population_error_le
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) {c : ℝ} (hc : 0 ≤ c) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {ε u ρ : ℝ} (hε : 0 ≤ ε) (hu : 0 ≤ u) (q : SignLaw) (hq : RarePrior (π.map Prod.snd + μ₀) ρ q) (L : ℕ),
    racePopulationError (π.map Prod.snd + μ₀) q (negativeBankTest weights ε)
      (positiveBankTest η weights u) L ≤
      ρ*ε + c*u + c*(∫ d : Gap, ordinaryErrorKernel (Uniform713.cap L) (d:ℝ) ∂η) +
      μ₀.real univ := @robust_bank_population_error
#print axioms ThresholdHC.RobustContinuation.DownwardTest
#print axioms ThresholdHC.RobustContinuation.UpwardTest
#print axioms ThresholdHC.RobustContinuation.bit_mono
#print axioms ThresholdHC.RobustContinuation.classifierStop_le_of_value_one
#print axioms ThresholdHC.RobustContinuation.classifierValue_mono
#print axioms ThresholdHC.RobustContinuation.classifierValue_one_of_le
#print axioms ThresholdHC.RobustContinuation.classifierValue_one_of_stop_lt
#print axioms ThresholdHC.RobustContinuation.coupledRaceError
#print axioms ThresholdHC.RobustContinuation.coupled_population_error_le
#print axioms ThresholdHC.RobustContinuation.dyadicMean_mono
#print axioms ThresholdHC.RobustContinuation.firstDecision_one_of_le
#print axioms ThresholdHC.RobustContinuation.firstDecision_one_of_stop_lt
#print axioms ThresholdHC.RobustContinuation.firstStop_le_of_decision_one
#print axioms ThresholdHC.RobustContinuation.half_lt_of_firstDecision_one
#print axioms ThresholdHC.RobustContinuation.integrable_coupledIntegrand
#print axioms ThresholdHC.RobustContinuation.measurable_coupledIntegrand
#print axioms ThresholdHC.RobustContinuation.negativeBankTest_downward
#print axioms ThresholdHC.RobustContinuation.null_prefix_anti
#print axioms ThresholdHC.RobustContinuation.parityTape_mono
#print axioms ThresholdHC.RobustContinuation.positiveBankTest_upward
#print axioms ThresholdHC.RobustContinuation.positiveBank_prefix_mono
#print axioms ThresholdHC.RobustContinuation.raceConditionalError_antitone
#print axioms ThresholdHC.RobustContinuation.raceValue_eq_one_iff
#print axioms ThresholdHC.RobustContinuation.raceValue_mono
#print axioms ThresholdHC.RobustContinuation.raceValue_one_of_le
#print axioms ThresholdHC.RobustContinuation.robust_bank_population_error
#print axioms ThresholdHC.RobustContinuation.streamProb_anti
#print axioms ThresholdHC.RobustContinuation.streamProb_mono
#print axioms ThresholdHC.RobustContinuation.tapeMeasure_le_of_isLowerSet
#print axioms ThresholdHC.RobustContinuation.tapeMeasure_le_of_isUpperSet
#print axioms ThresholdHC.RobustContinuation.tapePrefix_mono
#print axioms ThresholdHC.RobustContinuation.uniformCoinFlip_mono
#print axioms ThresholdHC.RobustContinuation.uniformCoinTape_mono
