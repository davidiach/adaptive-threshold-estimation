import ThresholdHC.EntropyTailUpper.NullPrefix
import ThresholdHC.EntropyTailUpper.PopulationErrors

/-! The full null mixture's prefix envelope, and a sufficient score condition
for the matching positive reference to trigger the actual bank. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.CriticalEntropy

def nullLaplace (μ : Measure Gap) (n : ℕ) : ℝ :=
  ∫ d : Gap, exp (-2*n*(d:ℝ)^2) ∂μ

theorem integrable_nullLaplace (μ : Measure Gap) [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (fun d : Gap => exp (-2*n*(d:ℝ)^2)) μ := by
  apply Integrable.of_bound (show Measurable (fun d : Gap => exp (-2*n*(d:ℝ)^2)) by fun_prop).aestronglyMeasurable 1
  exact ae_of_all _ (fun d => by
    rw [Real.norm_of_nonneg (exp_pos _).le]
    apply exp_le_one_iff.mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (sq_nonneg (d:ℝ))])

theorem null_prefix_real (μ : Measure Gap) [IsProbabilityMeasure μ] {n : ℕ} (w : Fin n → Bool) :
    (allNegativeLaw μ).real (tapePrefix n ⁻¹' {w}) = ∫ d : Gap, streamProb (1/2-(d:ℝ)) w ∂μ := by
  rw [null_event_mixture μ ((measurableSet_singleton w).preimage (measurable_prefix n))]
  apply integral_congr_ae
  exact ae_of_all _ (fun d => by
    unfold tapeEventProbability Measure.real
    rw [tape_prefix_mass, ENNReal.toReal_ofReal]
    · rfl
    · exact streamProb_nonneg_of_unit (gapParameter false d) w)

theorem null_prefix_gaussian (μ : Measure Gap) [IsProbabilityMeasure μ] {n : ℕ} (w : Fin n → Bool)
    (hw : (n:ℝ)/2 ≤ ∑ i, bit (w i)) :
    (allNegativeLaw μ).real (tapePrefix n ⁻¹' {w}) ≤ streamProb (1/2) w * nullLaplace μ n := by
  rw [null_prefix_real]
  have hi : Integrable (fun d : Gap => streamProb (1/2-(d:ℝ)) w) μ := by
    convert integrable_tapeEventProbability μ false
      ((measurableSet_singleton w).preimage (measurable_prefix n)) using 1
    funext d
    unfold tapeEventProbability Measure.real
    rw [tape_prefix_mass, ENNReal.toReal_ofReal]
    · rfl
    · exact streamProb_nonneg_of_unit (gapParameter false d) w
  have h := integral_mono hi ((integrable_nullLaplace μ n).const_mul (streamProb (1/2) w))
    (fun d => negative_prefix_gaussian d.property.1.le d.property.2 w hw)
  rw [integral_const_mul] at h
  exact h

theorem null_prefix_gaussian_ennreal (μ : Measure Gap) [IsProbabilityMeasure μ] {n : ℕ} (w : Fin n → Bool)
    (hw : (n:ℝ)/2 ≤ ∑ i, bit (w i)) :
    allNegativeLaw μ (tapePrefix n ⁻¹' {w}) ≤ ENNReal.ofReal (streamProb (1/2) w * nullLaplace μ n) := by
  have : IsProbabilityMeasure (allNegativeLaw μ) := originalPopulationTapeLaw_probability μ allNegativeSignLaw
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (null_prefix_gaussian μ w hw)

theorem positiveBankLaw_lower (weights : ℕ → ℝ≥0) (j : ℕ) {n : ℕ} (w : Fin n → Bool) :
    ENNReal.ofReal ((weights j:ℝ)*streamProb (1/2+EntropyTailQuantile.bandEdge j/4) w) ≤
      positiveBankLaw weights (tapePrefix n ⁻¹' {w}) := by
  have h := Measure.le_sum (fun k => (weights k:ℝ≥0∞) • tapeMeasure (positiveReference k)) j
  have hs := h (tapePrefix n ⁻¹' {w})
  rw [ENNReal.ofReal_mul (show 0 ≤ (weights j:ℝ) by positivity), ENNReal.ofReal_coe_nnreal]
  simpa only [Measure.smul_apply, smul_eq_mul, tape_prefix_mass, positiveReference, positiveBankLaw] using hs

theorem positive_bank_of_score (μ : Measure Gap) (weights : ℕ → ℝ≥0) {u V : ℝ} (hu : 0 ≤ u)
    (j : ℕ) {n : ℕ} (w : Fin n → Bool)
    (hnull : allNegativeLaw μ (tapePrefix n ⁻¹' {w}) ≤ ENNReal.ofReal (streamProb (1/2) w*V))
    (hscore : V ≤ u*(weights j:ℝ)*exp (∑ i, positiveBitScore (EntropyTailQuantile.bandEdge j/4) (w i))) :
    positiveBankTest μ weights u n w := by
  apply hnull.trans
  calc
    _ ≤ ENNReal.ofReal (u*((weights j:ℝ)*streamProb (1/2+EntropyTailQuantile.bandEdge j/4) w)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [positive_score_likelihood (by positivity [EntropyTailQuantile.bandEdge_pos j])
        (by linarith [bandEdge_le_half j])]
      have h := mul_le_mul_of_nonneg_left hscore (streamProb_pos (1/2) (by norm_num) (by norm_num) w).le
      nlinarith only [h]
    _ = ENNReal.ofReal u * ENNReal.ofReal ((weights j:ℝ)*streamProb (1/2+EntropyTailQuantile.bandEdge j/4) w) :=
      ENNReal.ofReal_mul hu
    _ ≤ _ := mul_le_mul_right (positiveBankLaw_lower weights j w) (ENNReal.ofReal u)

end ThresholdHC.EntropyTailUpper
