import ThresholdHC.FiniteLawCertificates.Oracles
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.FiniteLawCertificates ThresholdHC.DeterministicCertificates
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
private def gaps := (![(1/2:ℚ)] : Fin 1 → ℚ)
private def weights := (![(1/1:ℚ)] : Fin 1 → ℚ)
private def labels := (![0] : Fin 1 → ℕ)
private theorem gaps_valid : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := by norm_num [gaps, Fin.forall_fin_succ]
private theorem weights_valid : ∀ i, 0 ≤ weights i := by norm_num [weights, Fin.forall_fin_succ]
private theorem weights_sum : ∑ i, weights i = 1 := by norm_num [weights, Fin.sum_univ_succ]
private noncomputable def law := atomicMeasure (points gaps gaps_valid) weights
theorem certified_value : IsProbabilityMeasure law ∧
    Contains ⟨(1/1:ℚ), (1/1:ℚ)⟩ (nullPrefixIntegral law 0 0) ∧
    ((1/1:ℚ):ℝ)-((1/1:ℚ):ℝ) ≤ ((1/1208925819614629174706176:ℚ):ℝ) := by
  refine ⟨atomicMeasure_probability _ _ weights_valid weights_sum, ?_, ?_⟩
  · rw [law, nullPrefix_eq gaps weights gaps_valid weights_valid]
    norm_num [Contains, nullPrefixValue, gaps, weights, Fin.sum_univ_succ]
  · norm_num
#print axioms certified_value
