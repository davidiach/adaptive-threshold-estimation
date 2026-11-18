import ThresholdHC.Proofs.Tier2.ClassifierModel

/-! A sharper per-level bound on the disagreement of consecutive classifiers.

The classifier at cap `2^L` errs with probability at most
`errorPrefactor/(cap L*d^2)^2`, where `errorPrefactor = (5/3)*exp(-2)`
(`Tier2.Model.error_positive_bound`). Two consecutive classifiers disagree
only if one of them errs, which gives `5*errorPrefactor/(cap (L+1)*d^2)^2`.
`Tier2.Model.error_pair_bound` rounds `5*errorPrefactor ≈ 1.1278` up to `3`;
this module keeps `113/100`. -/
noncomputable section
namespace ThresholdHC.UpperMoment
open MeasureTheory Real ThresholdHC.Uniform713

theorem exp_neg_two_le : Real.exp (-2) ≤ 339 / 2500 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg]
  exact (inv_le_iff_one_le_mul₀ (Real.exp_pos 2)).2 (by linarith)

theorem errorPair_le (L : ℕ) {d : ℝ} (hd : 0 < d) :
    Tier2.Model.errorPrefactor / (cap (L + 1) * d ^ 2) ^ 2 +
        Tier2.Model.errorPrefactor / (cap L * d ^ 2) ^ 2 ≤
      (113 / 100) / (cap (L + 1) * d ^ 2) ^ 2 := by
  have hN := (cap_pos L).ne'
  have hdne := hd.ne'
  have heq : Tier2.Model.errorPrefactor / (cap (L + 1) * d ^ 2) ^ 2 +
      Tier2.Model.errorPrefactor / (cap L * d ^ 2) ^ 2 =
      (5 * Tier2.Model.errorPrefactor) / (cap (L + 1) * d ^ 2) ^ 2 := by
    rw [cap_succ]
    field_simp
    ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  unfold Tier2.Model.errorPrefactor
  linarith [exp_neg_two_le]

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ → Ω → ℝ}

/-- The squared increment of the classifier decisions at level `L`. -/
theorem increment_secondMoment_envelope (s : ℝ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (hm : ∀ k, Measurable (m k))
    (herr : ∀ L, μ.real {ω | Tier2.Model.decision (fun k => m k ω) L ≠ s} ≤
      Tier2.Model.errorPrefactor / (cap L * d ^ 2) ^ 2) (L : ℕ) :
    (∫ ω, (increment (fun k => Tier2.Model.decision (fun j => m j ω) k) L) ^ 2 ∂μ) ≤
      min 1 ((113 / 100) / (cap L * d ^ 2) ^ 2) := by
  cases L with
  | zero =>
    simp only [increment, cap_zero, one_mul]
    apply le_min (Tier2.Model.decision_square_integral_le_one hm 0)
    apply (Tier2.Model.decision_square_integral_le_one hm 0).trans
    apply (le_div_iff₀ (sq_pos_of_pos (sq_pos_of_pos hd))).2
    have hds : d ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hds (sq_nonneg d)]
  | succ L =>
    simp only [increment]
    apply le_min (Tier2.Model.squared_decision_difference_le_one hm (L + 1) L)
    exact ((Tier2.Model.squared_decision_difference_le_errors hm (L + 1) L s).trans
      (add_le_add (herr (L + 1)) (herr L))).trans (errorPair_le L hd)

theorem increment_secondMoment_positive (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (ht : HasMeanTails μ m (1 / 2 + d)) :
    (∫ ω, (increment (fun k => Tier2.Model.decision (fun j => m j ω) k) L) ^ 2 ∂μ) ≤
      min 1 ((113 / 100) / (cap L * d ^ 2) ^ 2) :=
  increment_secondMoment_envelope 1 hd hdmax ht.measurable
    (fun L => Tier2.Model.error_positive_bound L hd ht) L

theorem increment_secondMoment_negative (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 2)
    (ht : HasMeanTails μ m (1 / 2 - d)) :
    (∫ ω, (increment (fun k => Tier2.Model.decision (fun j => m j ω) k) L) ^ 2 ∂μ) ≤
      min 1 ((113 / 100) / (cap L * d ^ 2) ^ 2) :=
  increment_secondMoment_envelope 0 hd hdmax ht.measurable
    (fun L => Tier2.Model.error_negative_bound L hd ht) L

end Probability

end ThresholdHC.UpperMoment
