import ThresholdHC.FullNullBank.Specification

/-! The bank with the full null mixture: prefix probabilities, monotonicity in
the flips, Ville's bound, the integrated false positives of the positive part,
and a sufficient score condition for the positive test to fire.

On a prefix `w` of length `n`, the full null probability is
`z0 2^-n + (1 - z0) P_eta(w)`. The fair-coin term is the same for every word of
length `n`, so the test is upward in the flips as the bank with null law `eta`
is. On a word with at least `n/2` heads it is at most
`2^-n (z0 + (1 - z0) nullLaplace eta n)`. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.FullNullBank
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.EntropyTailUpper ThresholdHC.RobustContinuation

/-- The full null probability of a word of flips. -/
theorem fullNull_prefix (z₀ : ℝ) (η : Measure Gap) {n : ℕ} (w : Fin n → Bool) :
    fullNullLaw z₀ η (tapePrefix n ⁻¹' {w}) =
      ENNReal.ofReal z₀ * ENNReal.ofReal (streamProb (1/2) w) +
        ENNReal.ofReal (1 - z₀) * allNegativeLaw η (tapePrefix n ⁻¹' {w}) := by
  unfold fullNullLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, tape_prefix_mass, smul_eq_mul,
    smul_eq_mul]
  rfl

/-- The full-null bank is upward in the flips. -/
theorem fullNullBankTest_upward (z₀ : ℝ) (η : Measure Gap) [IsProbabilityMeasure η]
    (weights : ℕ → ℝ≥0) (u : ℝ) : UpwardTest (fullNullBankTest z₀ η weights u) := by
  intro n w w' h hw
  have hfair : streamProb (1/2) w' ≤ streamProb (1/2) w :=
    streamProb_anti (by norm_num) le_rfl h
  calc fullNullLaw z₀ η (tapePrefix n ⁻¹' {w'}) ≤ fullNullLaw z₀ η (tapePrefix n ⁻¹' {w}) := by
        rw [fullNull_prefix, fullNull_prefix]
        exact add_le_add (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hfair))
          (mul_le_mul' le_rfl (null_prefix_anti η h))
    _ ≤ ENNReal.ofReal u * positiveBankLaw weights (tapePrefix n ⁻¹' {w}) := hw
    _ ≤ ENNReal.ofReal u * positiveBankLaw weights (tapePrefix n ⁻¹' {w'}) :=
        mul_le_mul' le_rfl (positiveBank_prefix_mono weights h)

/-- Ville's bound under the full null mixture. -/
theorem fullNull_bank_error (z₀ : ℝ) (η : Measure Gap) (weights : ℕ → ℝ≥0)
    (hw : HasSum weights 1) (u : ℝ) :
    fullNullLaw z₀ η (everPrefixHit (fullNullBankTest z₀ η weights u)) ≤ ENNReal.ofReal u := by
  have := positiveBankLaw_probability weights hw
  exact measure_everPrefixHit_le _ (fullNullLaw z₀ η) (positiveBankLaw weights)
    (ENNReal.ofReal u) (fun _ _ h => h)

/-- The positive part of the null mixture is at most the full null mixture. -/
theorem allNegative_le_fullNull (z₀ : ℝ) (η : Measure Gap) (E : Set (ℕ → Bool)) :
    ENNReal.ofReal (1 - z₀) * allNegativeLaw η E ≤ fullNullLaw z₀ η E := by
  unfold fullNullLaw
  rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact le_add_self

/-- The integrated false positives of the positive part: at most `u`. -/
theorem fullNull_integrated_false_positive (z₀ : ℝ) (η : Measure Gap) [IsProbabilityMeasure η]
    (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) (hz1 : z₀ ≤ 1) {u : ℝ} (hu : 0 ≤ u) :
    (1 - z₀) * (∫ d, tapeEventProbability false
      (everPrefixHit (fullNullBankTest z₀ η weights u)) d ∂η) ≤ u := by
  have hE : MeasurableSet (everPrefixHit (fullNullBankTest z₀ η weights u)) :=
    measurableSet_everPrefixHit _
  rw [← null_event_mixture η hE]
  have h := (allNegative_le_fullNull z₀ η _).trans (fullNull_bank_error z₀ η weights hw u)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hu] at ht
  exact ht

/-- On a word with at least half heads, the full null probability is at most
`2^-n (z0 + (1 - z0) nullLaplace eta n)`. -/
theorem fullNull_prefix_gaussian {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1) (η : Measure Gap)
    [IsProbabilityMeasure η] {n : ℕ} (w : Fin n → Bool) (hw : (n:ℝ)/2 ≤ ∑ i, bit (w i)) :
    fullNullLaw z₀ η (tapePrefix n ⁻¹' {w}) ≤
      ENNReal.ofReal (streamProb (1/2) w * (z₀ + (1 - z₀) * nullLaplace η n)) := by
  rw [fullNull_prefix]
  have hs := (CriticalEntropy.streamProb_pos (1/2) (by norm_num) (by norm_num) w).le
  have hL : 0 ≤ nullLaplace η n := integral_nonneg (fun _ => (exp_pos _).le)
  have h1 := null_prefix_gaussian_ennreal η w hw
  calc _ ≤ ENNReal.ofReal z₀ * ENNReal.ofReal (streamProb (1/2) w) +
        ENNReal.ofReal (1 - z₀) * ENNReal.ofReal (streamProb (1/2) w * nullLaplace η n) :=
          add_le_add le_rfl (mul_le_mul' le_rfl h1)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hz0, ← ENNReal.ofReal_mul (by linarith),
        ← ENNReal.ofReal_add (mul_nonneg hz0 hs) (mul_nonneg (by linarith) (mul_nonneg hs hL))]
      congr 1
      ring

/-- A sufficient score condition for the full-null bank to fire. -/
theorem fullNull_bank_of_score (z₀ : ℝ) (η : Measure Gap) (weights : ℕ → ℝ≥0) {u V : ℝ}
    (hu : 0 ≤ u) (j : ℕ) {n : ℕ} (w : Fin n → Bool)
    (hnull : fullNullLaw z₀ η (tapePrefix n ⁻¹' {w}) ≤ ENNReal.ofReal (streamProb (1/2) w*V))
    (hscore : V ≤ u*(weights j:ℝ)*exp (∑ i, positiveBitScore (EntropyTailQuantile.bandEdge j/4) (w i))) :
    fullNullBankTest z₀ η weights u n w := by
  apply hnull.trans
  calc
    _ ≤ ENNReal.ofReal (u*((weights j:ℝ)*streamProb (1/2+EntropyTailQuantile.bandEdge j/4) w)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [positive_score_likelihood (by positivity [EntropyTailQuantile.bandEdge_pos j])
        (by linarith [bandEdge_le_half j])]
      have h := mul_le_mul_of_nonneg_left hscore
        (CriticalEntropy.streamProb_pos (1/2) (by norm_num) (by norm_num) w).le
      nlinarith only [h]
    _ = ENNReal.ofReal u *
          ENNReal.ofReal ((weights j:ℝ)*streamProb (1/2+EntropyTailQuantile.bandEdge j/4) w) :=
      ENNReal.ofReal_mul hu
    _ ≤ _ := mul_le_mul_right (positiveBankLaw_lower weights j w) (ENNReal.ofReal u)

end ThresholdHC.FullNullBank
