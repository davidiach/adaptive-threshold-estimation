import ThresholdHC.Proofs.Tier2.ClassifierProbability

/-! Hoeffding bounds at every positive prefix length, rather than only at the
dyadic checkpoints of the ordinary classifier. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC.Tier2 ThresholdHC.Uniform713

theorem tape_prefix_subgaussian (p : unitInterval) {n : ℕ} (hn : 0 < n) :
    HasSubgaussianMGF (fun ω => prefixMean observations n ω - (p:ℝ)) (1/(4*n)) (tapeMeasure p) := by
  apply prefixMean_subgaussian measurable_observations _ (observations_mean p) (observations_independent p) hn
  intro i
  exact ae_of_all _ (fun ω => by unfold observations bit; split_ifs <;> norm_num)

theorem tape_prefix_upper_tail (p : unitInterval) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    (tapeMeasure p).real {ω | t ≤ prefixMean observations n ω - (p:ℝ)} ≤ exp (-2*n*t^2) := by
  have he : -t^2/(2*((1/(4*n):ℝ≥0):ℝ)) = -2*n*t^2 := by
    norm_num
    have : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring
  simpa only [he] using (tape_prefix_subgaussian p hn).measure_ge_le ht

theorem tape_prefix_lower_tail (p : unitInterval) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    (tapeMeasure p).real {ω | t ≤ (p:ℝ) - prefixMean observations n ω} ≤ exp (-2*n*t^2) := by
  have he : -t^2/(2*((1/(4*n):ℝ≥0):ℝ)) = -2*n*t^2 := by
    norm_num
    have : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring
  simpa only [Pi.neg_apply, neg_sub, he] using (tape_prefix_subgaussian p hn).neg.measure_ge_le ht

end ThresholdHC.EntropyTailUpper
