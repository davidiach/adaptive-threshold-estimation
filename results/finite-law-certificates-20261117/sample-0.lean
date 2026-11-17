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
private def selected := (![(0/1:ℚ)] : Fin 1 → ℚ)
private theorem selected_valid : ∀ i, 0 ≤ selected i ∧ selected i ≤ 1 := by
  norm_num [selected, Fin.forall_fin_succ]
private theorem labels_injective : Function.Injective labels := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [labels] at *
private theorem bands_cover : ∀ i, ∃ j, inBand (gaps i) (labels j) = true := by
  norm_num [gaps, labels, inBand, Fin.forall_fin_succ, Fin.exists_fin_succ]
theorem certified_value : IsProbabilityMeasure law ∧
    atomicMeasure (points gaps gaps_valid) (fun i => weights i*selected i) ≤ law ∧
    Contains ⟨(1/16:ℚ), (1/16:ℚ)⟩ (min (ENNReal.ofReal ((1/4:ℚ):ℝ))
      (ThresholdHC.EntropyTail.selectionObjective law ((1/4:ℚ):ℝ) ((1024/1:ℚ):ℝ)
        (atomicMeasure (points gaps gaps_valid) (fun i => weights i*selected i)))).toReal ∧
    (ThresholdHC.EntropyTail.selection law ((1/4:ℚ):ℝ) ((1024/1:ℚ):ℝ)).toReal ≤ ((1/16:ℚ):ℝ) := by
  have hc : accepted (objectiveExpr gaps weights selected labels (1/4:ℚ) (1024/1:ℚ)) ⟨(1/16:ℚ), (1/16:ℚ)⟩
      (.binary ⟨(1/16:ℚ), (1/16:ℚ)⟩ (.leaf ⟨(1/4:ℚ), (1/4:ℚ)⟩) (.binary ⟨(1/16:ℚ), (1/16:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩) (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩))))) (.binary ⟨(1/16:ℚ), (1/16:ℚ)⟩ (.unary ⟨(1/16:ℚ), (1/16:ℚ)⟩ (.binary ⟨(1/16:ℚ), (1/16:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.unary ⟨(1/16:ℚ), (1/16:ℚ)⟩ (.leaf ⟨(1/256:ℚ), (1/256:ℚ)⟩)))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩)))) = true := by
    norm_num [gaps, weights, selected, labels, accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ, objectiveExpr, costs, inBand, imin, imax, tailWorkExpr, tailWeights]
  exact ⟨atomicMeasure_probability _ _ weights_valid weights_sum,
    selected_le _ weights selected weights_valid selected_valid,
    objective_accepted_sound gaps weights selected labels (1/4:ℚ) (1024/1:ℚ) gaps_valid weights_valid
      selected_valid (by norm_num) (by norm_num) labels_injective bands_cover hc,
    selection_upper gaps weights selected labels (1/4:ℚ) (1024/1:ℚ) gaps_valid weights_valid
      selected_valid (by norm_num) (by norm_num) labels_injective bands_cover hc⟩
#print axioms certified_value
