import ThresholdHC.EntropyTailUpper.PredictableWald

/-! Finite-cap expected work from geometric survival tails. -/

noncomputable section
open MeasureTheory Real Set
open scoped BigOperators

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC.Tier2

theorem integral_survives (p : unitInterval) {τ : (ℕ → Bool) → ℕ} (hτ : Measurable τ) (n : ℕ) :
    (∫ ω, survives τ n ω ∂tapeMeasure p) = (tapeMeasure p).real {ω | n < τ ω} := by
  have he : survives τ n = {ω | n < τ ω}.indicator (fun _ => (1:ℝ)) := by
    funext ω
    simp only [survives, Set.indicator, mem_ofPred_eq]
  rw [he]
  exact integral_indicator_one (measurableSet_lt measurable_const hτ)

theorem bounded_count_tail_sum (p : unitInterval) (τ : (ℕ → Bool) → ℕ) (M : ℕ)
    (hM : ∀ ω, τ ω ≤ M) (hτ : Measurable τ) :
    (∫ ω, (τ ω : ℝ) ∂tapeMeasure p) =
      ∑ n ∈ Finset.range M, (tapeMeasure p).real {ω | n < τ ω} := by
  simp_rw [stopped_count_eq τ M hM]
  have hi (n : ℕ) : Integrable (survives τ n) (tapeMeasure p) := by
    apply Integrable.of_bound
      ((measurable_const.ite (measurableSet_lt measurable_const hτ) measurable_const)).aestronglyMeasurable 1
    exact ae_of_all _ (fun ω => by change ‖(if n < τ ω then (1:ℝ) else 0)‖ ≤ 1; split_ifs <;> norm_num)
  rw [integral_finsetSum _ (fun n _ => hi n)]
  simp_rw [integral_survives p hτ]

theorem finite_geometric_sum_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    (∑ n ∈ Finset.range M, r^n) ≤ (1-r)⁻¹ := by
  rw [← tsum_geometric_of_lt_one hr0 hr1]
  exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum (Finset.range M)
    (fun n _ => pow_nonneg hr0 n)

theorem geometric_work_bound (p : unitInterval) (τ : (ℕ → Bool) → ℕ) (M N : ℕ)
    (hM : ∀ ω, τ ω ≤ M) (hτ : Measurable τ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ n, N ≤ n → (tapeMeasure p).real {ω | n < τ ω} ≤ r^n) :
    (∫ ω, (τ ω : ℝ) ∂tapeMeasure p) ≤ N+(1-r)⁻¹ := by
  classical
  rw [bounded_count_tail_sum p τ M hM hτ]
  have hb (n : ℕ) : (tapeMeasure p).real {ω | n < τ ω} ≤ (if n < N then (1:ℝ) else 0)+r^n := by
    split_ifs with hn
    · exact measureReal_le_one.trans (le_add_of_nonneg_right (pow_nonneg hr0 n))
    · simpa using htail n (le_of_not_gt hn)
  calc
    _ ≤ ∑ n ∈ Finset.range M, ((if n < N then (1:ℝ) else 0)+r^n) :=
      Finset.sum_le_sum (fun n _ => hb n)
    _ = (∑ n ∈ Finset.range M, if n < N then (1:ℝ) else 0)+∑ n ∈ Finset.range M, r^n :=
      Finset.sum_add_distrib
    _ ≤ N+(1-r)⁻¹ := add_le_add (by
      have he : (∑ n ∈ Finset.range M, if n < N then (1:ℝ) else 0) = (min M N:ℕ) := by
        rw [← Finset.sum_filter]
        have hs : (Finset.range M).filter (fun n => n < N) = Finset.range (min M N) := by
          ext n
          simp
        rw [hs]
        simp
      rw [he]
      exact_mod_cast min_le_right M N) (finite_geometric_sum_le hr0 hr1 M)

theorem inv_one_sub_exp_neg_le {x : ℝ} (hx : 0 < x) :
    (1-exp (-x))⁻¹ ≤ 1+x⁻¹ := by
  have he : exp (-x) < 1 := exp_lt_one_iff.mpr (neg_neg_of_pos hx)
  have h0 : 0 < 1-exp (-x) := by linarith
  have hexp := add_one_le_exp x
  have hid : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
  have hmul := mul_le_mul_of_nonneg_right hexp (exp_pos (-x)).le
  rw [hid] at hmul
  rw [inv_eq_one_div]
  apply (div_le_iff₀ h0).mpr
  have hi : x*x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  have h := mul_le_mul_of_nonneg_right hmul (inv_pos.mpr hx).le
  nlinarith

end ThresholdHC.EntropyTailUpper
