import ThresholdHC.UnknownLawConfidence.Word
import ThresholdHC.ArbitraryLawAdaptation.TailTestProbability

/-! One item: the three outcomes of `m` flips on one coin of known gap and sign.

A wrong declaration needs a one-sided deviation of the head fraction of at
least `r` in a specified direction, so it has probability at most
`exp(-2 m r^2) <= tau`. When `2r < d` even an unresolved outcome needs such a
deviation. Only the one-sided Hoeffding bound at one prefix length is used. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Real
namespace ThresholdHC.UnknownLawConfidence
open ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.Uniform713 ThresholdHC.EntropyTailUpper
open ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation

theorem tapeFraction_eq (j : ℕ) (ω : ℕ → Bool) :
    tapeFraction j ω = prefixMean observations (flipCount j) ω :=
  (prefixMean_eq_heads _ _).symm

theorem gapParameter_false_coe (d : Gap) :
    ((gapParameter false d : unitInterval) : ℝ) = 1 / 2 - (d : ℝ) := by
  simp [gapParameter, sub_eq_add_neg]

/-- An upward deviation of at least `r` has probability at most `tau`. -/
theorem deviation_up_le (j : ℕ) (p : unitInterval) :
    (tapeMeasure p).real {ω | radius j ≤ tapeFraction j ω - (p : ℝ)} ≤ tolerance j := by
  have h := tape_prefix_upper_tail p (flipCount_pos j) (radius_nonneg j)
  simp only [← tapeFraction_eq] at h
  exact h.trans (hoeffding_exp_le (flipCount_pos j) (tolerance_pos j))

/-- A downward deviation of at least `r` has probability at most `tau`. -/
theorem deviation_down_le (j : ℕ) (p : unitInterval) :
    (tapeMeasure p).real {ω | radius j ≤ (p : ℝ) - tapeFraction j ω} ≤ tolerance j := by
  have h := tape_prefix_lower_tail p (flipCount_pos j) (radius_nonneg j)
  simp only [← tapeFraction_eq] at h
  exact h.trans (hoeffding_exp_le (flipCount_pos j) (tolerance_pos j))

theorem pos_false_le (j : ℕ) (d : Gap) :
    (tapeMeasure (gapParameter false d)).real (posSet j) ≤ tolerance j := by
  refine (measureReal_mono ?_).trans (deviation_up_le j (gapParameter false d))
  intro ω hω
  change 1 / 2 + radius j < tapeFraction j ω at hω
  change radius j ≤ tapeFraction j ω - _
  rw [gapParameter_false_coe]
  have := d.property.1
  linarith

theorem neg_true_le (j : ℕ) (d : Gap) :
    (tapeMeasure (gapParameter true d)).real (negSet j) ≤ tolerance j := by
  refine (measureReal_mono ?_).trans (deviation_down_le j (gapParameter true d))
  intro ω hω
  change tapeFraction j ω < 1 / 2 - radius j at hω
  change radius j ≤ _ - tapeFraction j ω
  rw [gapParameter_true_coe]
  have := d.property.1
  linarith

theorem zero_true_le (j : ℕ) {d : Gap} (hd : 2 * radius j < (d : ℝ)) :
    (tapeMeasure (gapParameter true d)).real (zeroSet j) ≤ tolerance j := by
  refine (measureReal_mono ?_).trans (deviation_down_le j (gapParameter true d))
  intro ω hω
  have hp : ω ∉ posSet j := fun h => hω (Or.inl h)
  change ¬(1 / 2 + radius j < tapeFraction j ω) at hp
  change radius j ≤ _ - tapeFraction j ω
  rw [gapParameter_true_coe]
  linarith

theorem zero_false_le (j : ℕ) {d : Gap} (hd : 2 * radius j < (d : ℝ)) :
    (tapeMeasure (gapParameter false d)).real (zeroSet j) ≤ tolerance j := by
  refine (measureReal_mono ?_).trans (deviation_up_le j (gapParameter false d))
  intro ω hω
  have hn : ω ∉ negSet j := fun h => hω (Or.inr h)
  change ¬(tapeFraction j ω < 1 / 2 - radius j) at hn
  change radius j ≤ tapeFraction j ω - _
  rw [gapParameter_false_coe]
  linarith

end ThresholdHC.UnknownLawConfidence
