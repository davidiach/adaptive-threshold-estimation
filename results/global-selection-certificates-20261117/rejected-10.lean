import ThresholdHC.GlobalSelectionCertificates.Trace
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.FiniteLawCertificates ThresholdHC.DeterministicCertificates
open ThresholdHC.GlobalSelectionCertificates
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
private def gaps := (![(1/3:ℚ), (3/8:ℚ)] : Fin 2 → ℚ)
private def weights := (![(1/2:ℚ), (1/2:ℚ)] : Fin 2 → ℚ)
private def labels := (![0] : Fin 1 → ℕ)
private def bands := (![0, 0] : Fin 2 → ℕ)
private def candidates : List (Fin 2 → Bool) := [(![false, false] : Fin 2 → Bool), (![false, true] : Fin 2 → Bool), (![true, true] : Fin 2 → Bool)]
private def witness := (![true, false] : Fin 2 → Bool)
private theorem gaps_valid : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := by norm_num [gaps, Fin.forall_fin_succ]
private theorem weights_positive : ∀ i, 0 < weights i := by norm_num [weights, Fin.forall_fin_succ]
private theorem weights_valid : ∀ i, 0 ≤ weights i := fun i => (weights_positive i).le
private theorem weights_sum : ∑ i, weights i = 1 := by norm_num [weights, Fin.sum_univ_succ]
private theorem labels_injective : Function.Injective labels := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [labels] at *
private theorem bands_cover : ∀ i, ∃ j, inBand (gaps i) (labels j) = true := by
  norm_num [gaps, labels, inBand, Fin.forall_fin_succ, Fin.exists_fin_succ]
private theorem bands_valid : ∀ i, inBand (gaps i) (bands i) = true := by
  norm_num [gaps, bands, inBand, Fin.forall_fin_succ]
private noncomputable def law := atomicMeasure (points gaps gaps_valid) weights
private noncomputable def K := (ThresholdHC.EntropyTail.selection law ((1/4:ℚ):ℝ) ((1/1:ℚ):ℝ)).toReal
private noncomputable def J (s : Fin 2 → Bool) := (objectiveExpr gaps weights (fractions s) labels (1/4:ℚ) (1/1:ℚ)).eval
private theorem attained : ∃ s, suffixCheck gaps bands s = true ∧ K = J s :=
  suffix_attains gaps weights labels bands (1/4:ℚ) (1/1:ℚ) gaps_valid weights_positive weights_sum
    labels_injective bands_cover bands_valid (by norm_num) (by norm_num) (by norm_num)
private theorem complete_menu : ∀ s, suffixCheck gaps bands s = true → s ∈ candidates := by
  intro s hs
  have he : s = ![s 0, s 1] := by funext i; fin_cases i <;> rfl
  rw [he] at hs ⊢
  cases h0 : s 0 <;> cases h1 : s 1 <;> simp only [h0, h1] at hs ⊢ <;>
    norm_num [suffixCheck, gaps, bands, Fin.forall_fin_succ] at hs <;> norm_num [candidates]
private theorem menu_valid : candidates.Nodup ∧ (∀ s ∈ candidates, suffixCheck gaps bands s = true) ∧
    candidates.length = 3 := by
  norm_num [candidates, suffixCheck, gaps, bands, Fin.forall_fin_succ] <;> decide
private theorem witness_suffix : suffixCheck gaps bands witness = true := by
  norm_num [witness, suffixCheck, gaps, bands, Fin.forall_fin_succ]
private theorem feasible : K ≤ J witness :=
  selection_le_expr gaps weights (fractions witness) labels (1/4:ℚ) (1/1:ℚ) gaps_valid weights_valid
    (fractions_valid witness) (by norm_num) (by norm_num) labels_injective bands_cover
private theorem witness_bounds : Contains ⟨(0/1:ℚ), (1/4:ℚ)⟩ (J (![true, false] : Fin 2 → Bool)) := by
  apply accepted_sound (e := objectiveExpr gaps weights (fractions (![true, false] : Fin 2 → Bool)) labels (1/4:ℚ) (1/1:ℚ))
  change accepted _ _ (.binary ⟨(0/1:ℚ), (1/4:ℚ)⟩ (.leaf ⟨(1/4:ℚ), (1/4:ℚ)⟩) (.binary ⟨(6702984397/4294967296:ℚ), (3351492199/2147483648:ℚ)⟩ (.unary ⟨(4555500749/4294967296:ℚ), (2277750375/2147483648:ℚ)⟩ (.unary ⟨(9/8:ℚ), (9/8:ℚ)⟩ (.binary ⟨(9/2:ℚ), (9/2:ℚ)⟩ (.leaf ⟨(9/2:ℚ), (9/2:ℚ)⟩) (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.logarithm ⟨(0/1:ℚ), (0/1:ℚ)⟩ ⟨0, 16⟩ ⟨0, 16⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩))))) (.binary ⟨(1/2:ℚ), (1/2:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.binary ⟨(1/1:ℚ), (1/1:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.unary ⟨(3/1:ℚ), (3/1:ℚ)⟩ (.leaf ⟨(9/1:ℚ), (9/1:ℚ)⟩)))) (.binary ⟨(1/2:ℚ), (1/2:ℚ)⟩ (.unary ⟨(1/2:ℚ), (1/2:ℚ)⟩ (.binary ⟨(1/1:ℚ), (1/1:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.unary ⟨(5726623061/2147483648:ℚ), (11453246123/4294967296:ℚ)⟩ (.leaf ⟨(64/9:ℚ), (64/9:ℚ)⟩)))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩))))) = true
  norm_num [gaps, weights, labels, fractions, accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ, objectiveExpr, costs, inBand, imin, imax]
private theorem candidate_0 : Contains ⟨(1/4:ℚ), (1/4:ℚ)⟩ (J (![false, false] : Fin 2 → Bool)) := by
  apply accepted_sound (e := objectiveExpr gaps weights (fractions (![false, false] : Fin 2 → Bool)) labels (1/4:ℚ) (1/1:ℚ))
  change accepted _ _ (.binary ⟨(1/4:ℚ), (1/4:ℚ)⟩ (.leaf ⟨(1/4:ℚ), (1/4:ℚ)⟩) (.binary ⟨(1/1:ℚ), (1/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩) (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩))))) (.binary ⟨(1/1:ℚ), (1/1:ℚ)⟩ (.unary ⟨(1/2:ℚ), (1/2:ℚ)⟩ (.binary ⟨(1/1:ℚ), (1/1:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.unary ⟨(3/1:ℚ), (3/1:ℚ)⟩ (.leaf ⟨(9/1:ℚ), (9/1:ℚ)⟩)))) (.binary ⟨(1/2:ℚ), (1/2:ℚ)⟩ (.unary ⟨(1/2:ℚ), (1/2:ℚ)⟩ (.binary ⟨(1/1:ℚ), (1/1:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.unary ⟨(5726623061/2147483648:ℚ), (11453246123/4294967296:ℚ)⟩ (.leaf ⟨(64/9:ℚ), (64/9:ℚ)⟩)))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩))))) = true
  norm_num [gaps, weights, labels, fractions, accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ, objectiveExpr, costs, inBand, imin, imax]
private theorem candidate_1 : Contains ⟨(1/4:ℚ), (1/4:ℚ)⟩ (J (![false, true] : Fin 2 → Bool)) := by
  apply accepted_sound (e := objectiveExpr gaps weights (fractions (![false, true] : Fin 2 → Bool)) labels (1/4:ℚ) (1/1:ℚ))
  change accepted _ _ (.binary ⟨(1/4:ℚ), (1/4:ℚ)⟩ (.leaf ⟨(1/4:ℚ), (1/4:ℚ)⟩) (.binary ⟨(12393635295/8589934592:ℚ), (387301103/268435456:ℚ)⟩ (.unary ⟨(8098667999/8589934592:ℚ), (253083375/268435456:ℚ)⟩ (.unary ⟨(8/9:ℚ), (8/9:ℚ)⟩ (.binary ⟨(32/9:ℚ), (32/9:ℚ)⟩ (.leaf ⟨(32/9:ℚ), (32/9:ℚ)⟩) (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.logarithm ⟨(0/1:ℚ), (0/1:ℚ)⟩ ⟨0, 16⟩ ⟨0, 16⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩))))) (.binary ⟨(1/2:ℚ), (1/2:ℚ)⟩ (.unary ⟨(1/2:ℚ), (1/2:ℚ)⟩ (.binary ⟨(1/1:ℚ), (1/1:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.unary ⟨(3/1:ℚ), (3/1:ℚ)⟩ (.leaf ⟨(9/1:ℚ), (9/1:ℚ)⟩)))) (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.binary ⟨(1/1:ℚ), (1/1:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.unary ⟨(5726623061/2147483648:ℚ), (11453246123/4294967296:ℚ)⟩ (.leaf ⟨(64/9:ℚ), (64/9:ℚ)⟩)))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩))))) = true
  norm_num [gaps, weights, labels, fractions, accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ, objectiveExpr, costs, inBand, imin, imax]
private theorem candidate_2 : Contains ⟨(1/4:ℚ), (1/4:ℚ)⟩ (J (![true, true] : Fin 2 → Bool)) := by
  apply accepted_sound (e := objectiveExpr gaps weights (fractions (![true, true] : Fin 2 → Bool)) labels (1/4:ℚ) (1/1:ℚ))
  change accepted _ _ (.binary ⟨(1/4:ℚ), (1/4:ℚ)⟩ (.leaf ⟨(1/4:ℚ), (1/4:ℚ)⟩) (.binary ⟨(761881849/536870912:ℚ), (6095054793/4294967296:ℚ)⟩ (.unary ⟨(761881849/536870912:ℚ), (6095054793/4294967296:ℚ)⟩ (.unary ⟨(145/72:ℚ), (145/72:ℚ)⟩ (.binary ⟨(145/18:ℚ), (145/18:ℚ)⟩ (.leaf ⟨(145/18:ℚ), (145/18:ℚ)⟩) (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.logarithm ⟨(0/1:ℚ), (0/1:ℚ)⟩ ⟨0, 16⟩ ⟨0, 16⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩))))) (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.binary ⟨(1/1:ℚ), (1/1:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.unary ⟨(3/1:ℚ), (3/1:ℚ)⟩ (.leaf ⟨(9/1:ℚ), (9/1:ℚ)⟩)))) (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.binary ⟨(1/1:ℚ), (1/1:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.unary ⟨(5726623061/2147483648:ℚ), (11453246123/4294967296:ℚ)⟩ (.leaf ⟨(64/9:ℚ), (64/9:ℚ)⟩)))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩))))) = true
  norm_num [gaps, weights, labels, fractions, accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ, objectiveExpr, costs, inBand, imin, imax]
private theorem lower_bounds : ∀ s ∈ candidates, ((1/4:ℚ):ℝ) ≤ J s := by
  intro s hs
  simp only [candidates, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · have h := (candidate_0).1
    dsimp [Contains] at h
    linarith
  · have h := (candidate_1).1
    dsimp [Contains] at h
    linarith
  · have h := (candidate_2).1
    dsimp [Contains] at h
    linarith
private theorem enclosure : ((1/4:ℚ):ℝ) ≤ K ∧ K ≤ J witness ∧ J witness ≤ ((1/4:ℚ):ℝ) := by
  apply global_enclosure (fun s => suffixCheck gaps bands s = true) J K candidates witness
    (1/4:ℚ) (1/4:ℚ) attained complete_menu lower_bounds feasible
  have h := witness_bounds.2
  change J witness ≤ ((1/4:ℚ):ℝ) at h
  have hu : ((1/4:ℚ):ℝ) ≤ ((1/4:ℚ):ℝ) := by norm_num
  exact h.trans hu
private theorem optimal : J witness = K := by
  apply global_optimality (fun s => suffixCheck gaps bands s = true) J K candidates witness attained complete_menu _ feasible
  intro s hs
  simp only [candidates, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · have hl := candidate_0.1
    have hu := witness_bounds.2
    dsimp [Contains] at hl hu
    change J witness ≤ _ at hu
    linarith
  · have hl := candidate_1.1
    have hu := witness_bounds.2
    dsimp [Contains] at hl hu
    change J witness ≤ _ at hu
    linarith
  · have hl := candidate_2.1
    have hu := witness_bounds.2
    dsimp [Contains] at hl hu
    change J witness ≤ _ at hu
    linarith
theorem certified_value : IsProbabilityMeasure law ∧
    Contains ⟨(1/4:ℚ), (1/4:ℚ)⟩ K ∧
    atomicMeasure (points gaps gaps_valid) (fun i => weights i*fractions witness i) ≤ law ∧
    suffixCheck gaps bands witness = true ∧
    K ≤ J witness ∧ J witness ≤ ((1/4:ℚ):ℝ) ∧
    candidates.Nodup ∧ (∀ s ∈ candidates, suffixCheck gaps bands s = true) ∧
    (∀ s, suffixCheck gaps bands s = true → s ∈ candidates) ∧
    candidates.length = 3 ∧ (J witness = K) := by
  exact ⟨atomicMeasure_probability _ _ weights_valid weights_sum,
    ⟨enclosure.1, enclosure.2.1.trans enclosure.2.2⟩,
    selected_le _ weights (fractions witness) weights_valid (fractions_valid witness),
    witness_suffix, enclosure.2.1, enclosure.2.2, menu_valid.1, menu_valid.2.1, complete_menu,
    menu_valid.2.2, optimal⟩
#print axioms certified_value
