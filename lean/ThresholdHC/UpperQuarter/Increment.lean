import ThresholdHC.UpperQuarter.Grid
import ThresholdHC.UpperQuarter.EarlyStop
import ThresholdHC.UpperSign.Increment

/-! The disagreement of consecutive classifiers on the tape, level by level, with
the vote-change bound.

The squared increment at level `l` is at most one and at most the weight
`quarterWeight l d` plus the early-stopping error terms of both classifiers. From
`x = 19/20` on this is the level bound of `UpperDisagreement`; below it, from
the second level on, it is the vote-change bound of `EarlyStop`; the first
level has weight one. -/
noncomputable section
namespace ThresholdHC.UpperQuarter
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2 ThresholdHC.UpperSign

section QuarterIncrement
open Real Uniform713

/-- Past `19/20` the weight with the early-stopping terms is the level bound of
`UpperDisagreement`. -/
theorem levelBound_eq_quarter (L : ℕ) (d : ℝ) (h : 19 / 20 ≤ cap (L + 1) * d ^ 2) :
    UpperDisagreement.levelBound (L + 1) d =
      quarterWeight (L + 1) d + UpperDisagreement.stopError (L + 1) d +
        UpperDisagreement.stopError L d := by
  unfold UpperDisagreement.levelBound UpperDisagreement.capWeight quarterWeight
  rw [ite_eq_left (show (12 / 25 : ℝ) ≤ cap (L + 1) * d ^ 2 by linarith), ite_eq_left h,
    Nat.add_sub_cancel]

theorem quarter_increment_le (L : ℕ) (p : unitInterval) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (s : ℝ) (herr : ∀ L, (tapeMeasure p).real {ω | Tier2.Model.decision
      (fun k => dyadicMean observations k ω) L ≠ s} ≤ Tier2.Model.errorUnionBound L d)
    (hearly : ∀ L, (tapeMeasure p).real {ω | ∃ k < L, Tier2.Model.threshold1 (cap k) (cap L) <
      |dyadicMean observations k ω - 1/2|} ≤ earlyBound L d) :
    (∫ ω, (increment (fun k => Tier2.Model.decision (fun j => dyadicMean observations j ω) k) L) ^ 2
      ∂tapeMeasure p) ≤
      min 1 (quarterWeight L d + UpperDisagreement.stopError L d +
        UpperDisagreement.stopError (L - 1) d) := by
  have hm : ∀ k, Measurable (dyadicMean observations k) := (tape_mean_tails p).measurable
  have hs0 : ∀ L, 0 ≤ UpperDisagreement.stopError L d := fun L => UpperDisagreement.stopError_nonneg L d
  cases L with
  | zero =>
    simp only [increment]
    have h1 := Tier2.Model.decision_square_integral_le_one hm (μ := tapeMeasure p) 0
    have hw : quarterWeight 0 d = 1 := by
      unfold quarterWeight
      have : ¬ (19 / 20 ≤ cap 0 * d ^ 2) := by rw [cap_zero, one_mul]; nlinarith
      rw [ite_eq_right this, ite_eq_right (by norm_num)]
    apply le_min h1
    rw [hw]
    linarith [hs0 0, hs0 (0 - 1)]
  | succ L =>
    simp only [increment]
    have h1 := Tier2.Model.squared_decision_difference_le_one hm (μ := tapeMeasure p) (L + 1) L
    apply le_min h1
    simp only [Nat.add_sub_cancel]
    by_cases hx : 19 / 20 ≤ cap (L + 1) * d ^ 2
    · have h2 := (Tier2.Model.squared_decision_difference_le_errors hm (μ := tapeMeasure p) (L + 1) L s).trans
        (add_le_add (herr (L + 1)) (herr L))
      rw [UpperDisagreement.unionPair_eq L d (by linarith), levelBound_eq_quarter L d hx] at h2
      exact h2
    · have hw : quarterWeight (L + 1) d = 1 / 4 + ∑ k ∈ range L, driftBound L k d := by
        unfold quarterWeight
        rw [ite_eq_right hx, ite_eq_left (by omega), Nat.add_sub_cancel]
      rw [Tier2.Model.squared_decision_difference_integral hm (μ := tapeMeasure p) (L + 1) L]
      refine (disagree_tape_quarter L p (hearly L)).trans ?_
      rw [hw]
      unfold earlyBound
      linarith [hs0 (L + 1)]

end QuarterIncrement

end ThresholdHC.UpperQuarter
