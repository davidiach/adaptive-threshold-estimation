import ThresholdHC.RobustContinuation.ClassifierOrder
import ThresholdHC.EntropyTailUpper.NullMixture
import ThresholdHC.EntropyTailUpper.BankRace

/-! The raced classifier is monotone in the flips, and its error decreases
with the gap.

A prefix test is downward when turning tails into heads cannot make it fire,
and upward when that cannot stop it from firing. For a downward negative test
and an upward positive test, the output of the race is monotone in the flips:
more heads cannot bring a negative crossing earlier and cannot delay a
positive one, and the ordinary classifier is monotone.

The negative bank is downward and the positive bank is upward, for every
reference law. With flips built from common uniforms, the error of the race
on a coin of either sign therefore does not increase when the gap grows. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.RobustContinuation
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.BlindUpper ThresholdHC.EntropyTailUpper

/-- A prefix test that turning tails into heads cannot make fire. -/
def DownwardTest (t : PrefixTest) : Prop :=
  ∀ (n : ℕ) (w w' : Fin n → Bool), w ≤ w' → t n w' → t n w

/-- A prefix test that turning tails into heads cannot stop from firing. -/
def UpwardTest (t : PrefixTest) : Prop :=
  ∀ (n : ℕ) (w w' : Fin n → Bool), w ≤ w' → t n w → t n w'

/-- The even and the odd flips of ordered tapes are ordered. -/
theorem parityTape_mono (b : Fin 2) {ω ω' : ℕ → Bool} (h : ω ≤ ω') :
    parityTape b ω ≤ parityTape b ω' := fun k => h (2*k+b)

/-- The race decides positive exactly when the negative test does not fire
at its stop, and the positive test fires there or the ordinary classifier
decides positive. -/
theorem raceValue_eq_one_iff (neg pos : PrefixTest) (L : ℕ) (ω : ℕ → Bool) :
    raceValue neg pos L ω = 1 ↔
      ¬ neg (raceRounds neg pos L ω)
          (tapePrefix (raceRounds neg pos L ω) (parityTape 0 ω)) ∧
        (pos (raceRounds neg pos L ω)
            (tapePrefix (raceRounds neg pos L ω) (parityTape 0 ω)) ∨
          classifierValue L (parityTape 1 ω) = 1) := by
  unfold raceValue
  dsimp only
  split_ifs with hn hp
  · exact ⟨fun h => absurd h zero_ne_one, fun h => absurd hn h.1⟩
  · exact ⟨fun _ => ⟨hn, Or.inl hp⟩, fun _ => rfl⟩
  · exact ⟨fun h => ⟨hn, Or.inr h⟩, fun h => h.2.resolve_left hp⟩

/-- More heads keep a positive output of the race. -/
theorem raceValue_one_of_le {neg pos : PrefixTest} (hneg : DownwardTest neg)
    (hpos : UpwardTest pos) (L : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω')
    (h1 : raceValue neg pos L ω = 1) : raceValue neg pos L ω' = 1 := by
  obtain ⟨hn0, hpc⟩ := (raceValue_eq_one_iff neg pos L ω).mp h1
  have he : ∀ m, tapePrefix m (parityTape 0 ω) ≤ tapePrefix m (parityTape 0 ω') :=
    fun m => tapePrefix_mono m (parityTape_mono 0 h)
  have ho : parityTape 1 ω ≤ parityTape 1 ω' := parityTape_mono 1 h
  -- The race on the larger tape has stopped by the stop of the smaller one.
  have hhit : raceHit neg pos L ω' (raceRounds neg pos L ω) := by
    rcases raceRounds_hit neg pos L ω with hh | hh | hh
    · exact absurd hh hn0
    · exact Or.inr (Or.inl (hpos _ _ _ (he _) hh))
    · rcases hpc with hp | hc
      · exact Or.inr (Or.inl (hpos _ _ _ (he _) hp))
      · exact Or.inr (Or.inr ((classifierStop_le_of_value_one L ho hc).trans hh))
  have hle : raceRounds neg pos L ω' ≤ raceRounds neg pos L ω :=
    boundedFirst_le_of_hit _ _ _ hhit
  -- Its negative test has not fired there.
  have hnoneg : ¬ neg (raceRounds neg pos L ω')
      (tapePrefix (raceRounds neg pos L ω') (parityTape 0 ω')) := by
    intro hc
    have hc' := hneg _ _ _ (he _) hc
    rcases hle.lt_or_eq with hlt | heq
    · exact boundedFirst_before (raceHit neg pos L ω) (2^L) _ hlt (Or.inl hc')
    · rw [heq] at hc'
      exact hn0 hc'
  refine (raceValue_eq_one_iff neg pos L ω').mpr ⟨hnoneg, ?_⟩
  by_cases hp' : pos (raceRounds neg pos L ω')
      (tapePrefix (raceRounds neg pos L ω') (parityTape 0 ω'))
  · exact Or.inl hp'
  · right
    have hstop' : classifierStop L (parityTape 1 ω') ≤ raceRounds neg pos L ω' := by
      rcases raceRounds_hit neg pos L ω' with hh | hh | hh
      · exact absurd hh hnoneg
      · exact absurd hh hp'
      · exact hh
    rcases hle.lt_or_eq with hlt | heq
    · have hno : ¬ raceHit neg pos L ω (raceRounds neg pos L ω') :=
        boundedFirst_before (raceHit neg pos L ω) (2^L) _ hlt
      have hlate : raceRounds neg pos L ω' < classifierStop L (parityTape 1 ω) :=
        lt_of_not_ge fun hc => hno (Or.inr (Or.inr hc))
      exact classifierValue_one_of_stop_lt L ho (lt_of_le_of_lt hstop' hlate)
    · rw [heq] at hp'
      rcases hpc with hp | hc
      · exact absurd (hpos _ _ _ (he _) hp) hp'
      · exact classifierValue_one_of_le L ho hc

/-- The output of the race is monotone in the flips. -/
theorem raceValue_mono {neg pos : PrefixTest} (hneg : DownwardTest neg)
    (hpos : UpwardTest pos) (L : ℕ) : Monotone (raceValue neg pos L) := by
  intro ω ω' h
  rcases raceValue_zero_or_one neg pos L ω with h0 | h1
  · rw [h0]
    rcases raceValue_zero_or_one neg pos L ω' with h' | h'
    · rw [h']
    · rw [h']
      norm_num
  · rw [h1, raceValue_one_of_le hneg hpos L h h1]

/-- The negative bank is downward. -/
theorem negativeBankTest_downward (weights : ℕ → ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε) :
    DownwardTest (negativeBankTest weights ε) := by
  rintro n w w' h ⟨j, hj⟩
  have hb := EntropyTailQuantile.bandEdge_pos j
  have hb2 := bandEdge_le_half j
  refine ⟨j, ?_⟩
  calc streamProb (1/2) w ≤ streamProb (1/2) w' :=
        streamProb_mono le_rfl (by norm_num) h
    _ ≤ (ε*(weights j:ℝ)) * streamProb (1/2-EntropyTailQuantile.bandEdge j/2) w' := hj
    _ ≤ (ε*(weights j:ℝ)) * streamProb (1/2-EntropyTailQuantile.bandEdge j/2) w :=
        mul_le_mul_of_nonneg_left (streamProb_anti (by linarith) (by linarith) h)
          (mul_nonneg hε (weights j).property)

/-- The null probability of a word of flips does not increase when tails are
turned into heads. -/
theorem null_prefix_anti (μ : Measure Gap) [IsProbabilityMeasure μ] {n : ℕ}
    {w w' : Fin n → Bool} (h : w ≤ w') :
    allNegativeLaw μ (tapePrefix n ⁻¹' {w'}) ≤ allNegativeLaw μ (tapePrefix n ⁻¹' {w}) := by
  have : IsProbabilityMeasure (allNegativeLaw μ) :=
    originalPopulationTapeLaw_probability μ allNegativeSignLaw
  have hi : ∀ x : Fin n → Bool, Integrable (fun d : Gap => streamProb (1/2-(d:ℝ)) x) μ := by
    intro x
    convert integrable_tapeEventProbability μ false
      ((measurableSet_singleton x).preimage (measurable_prefix n)) using 1
    funext d
    unfold tapeEventProbability Measure.real
    rw [tape_prefix_mass, ENNReal.toReal_ofReal]
    · rfl
    · exact streamProb_nonneg_of_unit (gapParameter false d) x
  rw [← ofReal_measureReal, ← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  rw [null_prefix_real, null_prefix_real]
  exact integral_mono (hi w') (hi w) fun d =>
    streamProb_anti (by linarith [d.property.2]) (by linarith [d.property.1]) h

/-- The probability of a word of flips under the positive references does
not decrease when tails are turned into heads. -/
theorem positiveBank_prefix_mono (weights : ℕ → ℝ≥0) {n : ℕ} {w w' : Fin n → Bool}
    (h : w ≤ w') :
    positiveBankLaw weights (tapePrefix n ⁻¹' {w}) ≤
      positiveBankLaw weights (tapePrefix n ⁻¹' {w'}) := by
  have hm : ∀ x : Fin n → Bool, MeasurableSet (tapePrefix n ⁻¹' {x}) := fun x =>
    (measurableSet_singleton x).preimage (measurable_prefix n)
  unfold positiveBankLaw
  rw [Measure.sum_apply _ (hm w), Measure.sum_apply _ (hm w')]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [Measure.smul_apply, Measure.smul_apply, tape_prefix_mass, tape_prefix_mass]
  have hb := EntropyTailQuantile.bandEdge_pos j
  have hs : streamProb (positiveReference j : ℝ) w ≤ streamProb (positiveReference j : ℝ) w' :=
    streamProb_mono (by change 1/2 ≤ 1/2+EntropyTailQuantile.bandEdge j/4; linarith)
      (positiveReference j).property.2 h
  gcongr

/-- The positive bank is upward, for every reference law. -/
theorem positiveBankTest_upward (μ : Measure Gap) [IsProbabilityMeasure μ]
    (weights : ℕ → ℝ≥0) (u : ℝ) : UpwardTest (positiveBankTest μ weights u) := by
  intro n w w' h hw
  calc allNegativeLaw μ (tapePrefix n ⁻¹' {w'}) ≤ allNegativeLaw μ (tapePrefix n ⁻¹' {w}) :=
        null_prefix_anti μ h
    _ ≤ ENNReal.ofReal u * positiveBankLaw weights (tapePrefix n ⁻¹' {w}) := hw
    _ ≤ ENNReal.ofReal u * positiveBankLaw weights (tapePrefix n ⁻¹' {w'}) :=
        mul_le_mul' le_rfl (positiveBank_prefix_mono weights h)

/-- The error of the race on one coin does not increase when the gap grows,
for a coin of either sign. -/
theorem raceConditionalError_antitone {neg pos : PrefixTest} (hneg : DownwardTest neg)
    (hpos : UpwardTest pos) (L : ℕ) (s : Bool) {d d' : Gap} (h : (d:ℝ) ≤ d') :
    raceConditionalError neg pos L s d' ≤ raceConditionalError neg pos L s d := by
  have hmeas : MeasurableSet {ω | raceValue neg pos L ω ≠ bit s} :=
    (measurableSet_eq_fun (measurable_raceValue neg pos L) measurable_const).compl
  unfold raceConditionalError tapeEventProbability Measure.real
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  cases s with
  | true =>
    refine tapeMeasure_le_of_isLowerSet (p := gapParameter true d) (p' := gapParameter true d')
      (by change 1/2 + (d:ℝ) ≤ 1/2 + (d':ℝ); linarith) hmeas ?_
    intro a b hba ha hb
    have hb1 : raceValue neg pos L b = 1 := by simpa [bit] using hb
    exact ha (by simpa [bit] using raceValue_one_of_le hneg hpos L hba hb1)
  | false =>
    refine tapeMeasure_le_of_isUpperSet (p := gapParameter false d') (p' := gapParameter false d)
      (by change 1/2 + -(d':ℝ) ≤ 1/2 + -(d:ℝ); linarith) hmeas ?_
    intro a b hab ha
    have ha1 : raceValue neg pos L a = 1 := by
      rcases raceValue_zero_or_one neg pos L a with h0 | h1
      · exact absurd (by simpa [bit] using h0) ha
      · exact h1
    have hb1 := raceValue_one_of_le hneg hpos L hab ha1
    change raceValue neg pos L b ≠ bit false
    rw [hb1]
    simp [bit]

end ThresholdHC.RobustContinuation
