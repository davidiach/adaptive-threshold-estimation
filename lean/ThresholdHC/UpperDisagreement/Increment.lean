import ThresholdHC.UpperDisagreement.ErrorSum
import ThresholdHC.UpperDisagreement.CapGrid

/-! The disagreement of consecutive classifiers, level by level.

Two consecutive classifiers disagree only if one of them errs, and the
cap-`2^l` classifier errs with probability at most its union bound: the cap
term `exp(-2*cap l*d^2)` plus the early-stopping terms `stopError l d`. At
level `l`, the two cap terms are `exp(-2*x)` and `exp(-x)` with
`x = cap l*d^2`. So the squared increment is at most one and at most
`levelBound l d = capWeight x + stopError l d + stopError (l-1) d`, where
`capWeight x` is one below `12/25`. -/
noncomputable section
namespace ThresholdHC.UpperDisagreement
open MeasureTheory Real Finset ThresholdHC.Uniform713 ThresholdHC.UpperWork

/-- The disagreement bound at level `l`. -/
def levelBound (l : ℕ) (d : ℝ) : ℝ :=
  capWeight (cap l * d ^ 2) + stopError l d + stopError (l - 1) d

theorem levelBound_nonneg (l : ℕ) (d : ℝ) : 0 ≤ levelBound l d :=
  add_nonneg (add_nonneg (capWeight_nonneg _) (stopError_nonneg _ _)) (stopError_nonneg _ _)

/-- Past the split, two consecutive union bounds add up to the level bound. -/
theorem unionPair_eq (L : ℕ) (d : ℝ) (h : 12 / 25 ≤ cap (L + 1) * d ^ 2) :
    Tier2.Model.errorUnionBound (L + 1) d + Tier2.Model.errorUnionBound L d =
      levelBound (L + 1) d := by
  rw [errorUnionBound_eq, errorUnionBound_eq]
  unfold levelBound capWeight
  rw [ite_eq_left h, Nat.add_sub_cancel]
  have he : Real.exp (-2 * cap L * d ^ 2) = Real.exp (-(cap (L + 1) * d ^ 2)) := by
    rw [cap_succ]
    ring_nf
  have he2 : Real.exp (-2 * cap (L + 1) * d ^ 2) = Real.exp (-2 * (cap (L + 1) * d ^ 2)) := by
    ring_nf
  rw [he, he2]
  ring

/-- Below the split the level bound is at least one. -/
theorem one_le_levelBound (L : ℕ) (d : ℝ) (h : ¬ 12 / 25 ≤ cap L * d ^ 2) :
    1 ≤ levelBound L d := by
  unfold levelBound capWeight
  rw [ite_eq_right h]
  linarith [stopError_nonneg L d, stopError_nonneg (L - 1) d]

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ → Ω → ℝ}

theorem increment_sq_le_envelope (s : ℝ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (hm : ∀ k, Measurable (m k))
    (herr : ∀ L, μ.real {ω | Tier2.Model.decision (fun k => m k ω) L ≠ s} ≤
      Tier2.Model.errorUnionBound L d) (L : ℕ) :
    (∫ ω, (increment (fun k => Tier2.Model.decision (fun j => m j ω) k) L) ^ 2 ∂μ) ≤
      min 1 (levelBound L d) := by
  cases L with
  | zero =>
    simp only [increment]
    have h1 := Tier2.Model.decision_square_integral_le_one hm (μ := μ) 0
    have hb : levelBound 0 d = 1 := by
      unfold levelBound capWeight stopError
      have hd2 : cap 0 * d ^ 2 < 12 / 25 := by rw [cap_zero, one_mul]; nlinarith
      rw [ite_eq_right (not_le.2 hd2)]
      simp
    rw [hb, min_self]
    exact h1
  | succ L =>
    simp only [increment]
    have h1 := Tier2.Model.squared_decision_difference_le_one hm (μ := μ) (L + 1) L
    apply le_min h1
    by_cases hx : 12 / 25 ≤ cap (L + 1) * d ^ 2
    · have h2 := (Tier2.Model.squared_decision_difference_le_errors hm (μ := μ) (L + 1) L s).trans
        (add_le_add (herr (L + 1)) (herr L))
      rwa [unionPair_eq L d hx] at h2
    · exact h1.trans (one_le_levelBound (L + 1) d hx)

theorem increment_sq_positive (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (ht : HasMeanTails μ m (1 / 2 + d)) :
    (∫ ω, (increment (fun k => Tier2.Model.decision (fun j => m j ω) k) L) ^ 2 ∂μ) ≤
      min 1 (levelBound L d) :=
  increment_sq_le_envelope 1 hd hdmax ht.measurable
    (fun L => Tier2.Model.error_positive_union L hd ht) L

theorem increment_sq_negative (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (ht : HasMeanTails μ m (1 / 2 - d)) :
    (∫ ω, (increment (fun k => Tier2.Model.decision (fun j => m j ω) k) L) ^ 2 ∂μ) ≤
      min 1 (levelBound L d) :=
  increment_sq_le_envelope 0 hd hdmax ht.measurable
    (fun L => Tier2.Model.error_negative_union L hd ht) L

end Probability

end ThresholdHC.UpperDisagreement
