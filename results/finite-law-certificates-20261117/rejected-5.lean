import ThresholdHC.FiniteLawCertificates.Oracles
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.FiniteLawCertificates ThresholdHC.DeterministicCertificates
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
private def gaps := (![(1/16:ℚ), (1/8:ℚ), (1/2:ℚ)] : Fin 3 → ℚ)
private def weights := (![(1/8:ℚ), (1/8:ℚ), (3/4:ℚ)] : Fin 3 → ℚ)
private def labels := (![0, 2, 3] : Fin 3 → ℕ)
private theorem gaps_valid : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := by norm_num [gaps, Fin.forall_fin_succ]
private theorem weights_valid : ∀ i, 0 ≤ weights i := by norm_num [weights, Fin.forall_fin_succ]
private theorem weights_sum : ∑ i, weights i = 1 := by norm_num [weights, Fin.sum_univ_succ]
private noncomputable def law := atomicMeasure (points gaps gaps_valid) weights
private def selected := (![(0/1:ℚ), (0/1:ℚ), (1/1:ℚ)] : Fin 3 → ℚ)
private theorem selected_valid : ∀ i, 0 ≤ selected i ∧ selected i ≤ 1 := by
  norm_num [selected, Fin.forall_fin_succ]
private theorem selected_weights_valid (i) : 0 ≤ weights i*selected i :=
  mul_nonneg (weights_valid i) (selected_valid i).1
private noncomputable def core := ThresholdHC.EntropyTailQuantile.quantileCore law ((1/4:ℚ):ℝ)
private noncomputable def tail := (law-core).restrict {x : ThresholdHC.Tier6.Gap | 1 ≤ ((64/1:ℚ):ℝ)*(x:ℝ)^2}
private noncomputable def unresolved := (law-core).restrict {x : ThresholdHC.Tier6.Gap | ((64/1:ℚ):ℝ)*(x:ℝ)^2 < 1}
private theorem core_eq : core = atomicMeasure (points gaps gaps_valid) (fun i => weights i*selected i) := by
  apply quantileCore_atomic (points gaps gaps_valid) weights selected weights_valid weights_sum
    (ρ := ((1/4:ℚ):ℝ)) (t := ((1/8:ℚ):ℝ)) (by norm_num) (by norm_num)
    (1/1:ℚ) (by norm_num)
  all_goals norm_num [gaps, weights, selected, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
private theorem tail_eq : tail = atomicMeasure (points gaps gaps_valid)
    (tailWeights gaps weights selected (64/1:ℚ)) := by
  rw [tail, core_eq]
  exact tailMeasure_eq gaps weights selected (64/1:ℚ) gaps_valid weights_valid selected_valid
private theorem unresolved_eq : unresolved = atomicMeasure (points gaps gaps_valid)
    (unresolvedWeights gaps weights selected (64/1:ℚ)) := by
  rw [unresolved, core_eq]
  exact unresolvedMeasure_eq gaps weights selected (64/1:ℚ) gaps_valid weights_valid selected_valid
private theorem resolved_eq : core+tail = atomicMeasure (points gaps gaps_valid)
    (resolvedWeights gaps weights selected (64/1:ℚ)) := by
  rw [tail, core_eq]
  exact resolvedMeasure_eq gaps weights selected (64/1:ℚ) gaps_valid weights_valid selected_valid
theorem certified_value : IsProbabilityMeasure law ∧
    ThresholdHC.EntropyTailQuantile.quantileThreshold law ((1/4:ℚ):ℝ) = ((1/8:ℚ):ℝ) ∧
    core = atomicMeasure (points gaps gaps_valid) (fun i => weights i*selected i) ∧
    (∀ j, ThresholdHC.EntropyTail.bandCost core (labels j) = ENNReal.ofReal ((![(3/1:ℚ), (0/1:ℚ), (0/1:ℚ)] : Fin 3 → ℚ) j:ℝ)) ∧
    unresolved.real Set.univ = ((1/8:ℚ):ℝ) ∧
    (∫ x : ThresholdHC.Tier6.Gap, (x:ℝ)⁻¹ ∂tail) = ((0/1:ℚ):ℝ) ∧
    (∫ x : ThresholdHC.Tier6.Gap, min 1 (1/(((1024/1:ℚ):ℝ)*(x:ℝ)^2)^2) ∂(core+tail)) =
      ((131/262144:ℚ):ℝ) ∧
    Contains ⟨(0/1:ℚ), (128/1:ℚ)⟩ (tailWorkIntegral tail ((1024/1:ℚ):ℝ)) := by
  refine ⟨atomicMeasure_probability _ _ weights_valid weights_sum, ?_, core_eq, ?_, ?_, ?_, ?_, ?_⟩
  · let : IsProbabilityMeasure law := atomicMeasure_probability (points gaps gaps_valid) weights weights_valid weights_sum
    apply quantileThreshold_eq_of_mass law (ρ := ((1/4:ℚ):ℝ)) (by norm_num) (by norm_num)
    all_goals rw [law, atomicMeasure_real _ _ weights_valid]
    all_goals norm_num [gaps, weights, selected, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
  · intro j
    rw [core_eq, bandCost_atomic _ _ selected_weights_valid]
    norm_num [labels, ThresholdHC.EntropyTail.band, gaps, weights, selected, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
    fin_cases j <;> norm_num [labels, gaps, weights, selected, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
  · rw [unresolved_eq, atomicMeasure_real _ _ (by norm_num [unresolvedWeights, gaps, weights, selected, points, Fin.sum_univ_succ, Fin.forall_fin_succ])]
    norm_num [unresolvedWeights, gaps, weights, selected, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
  · rw [tail_eq, inverseIntegral_eq gaps _ gaps_valid
      (tailWeights_nonneg gaps weights selected (64/1:ℚ) weights_valid selected_valid)]
    norm_num [inverseValue, tailWeights, gaps, weights, selected, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
  · rw [resolved_eq, errorIntegral_eq gaps _ (1024/1:ℚ) gaps_valid (by
      intro i
      exact add_nonneg (selected_weights_valid i)
        (tailWeights_nonneg gaps weights selected (64/1:ℚ) weights_valid selected_valid i))]
    norm_num [errorValue, resolvedWeights, tailWeights, gaps, weights, selected, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
  · rw [tail_eq]
    apply tailWork_accepted_sound gaps _ (1024/1:ℚ) gaps_valid
      (tailWeights_nonneg gaps weights selected (64/1:ℚ) weights_valid selected_valid) (c := (.binary ⟨(0/1:ℚ), (128/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.binary ⟨(1024/1:ℚ), (1024/1:ℚ)⟩ (.leaf ⟨(1024/1:ℚ), (1024/1:ℚ)⟩) (.unary ⟨(794923264/76545:ℚ), (7154385536/688905:ℚ)⟩ (.binary ⟨(182657/76545:ℚ), (3287861/1377810:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.binary ⟨(106112/76545:ℚ), (1910051/1377810:ℚ)⟩ (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩) (.logarithm ⟨(106112/76545:ℚ), (1910051/1377810:ℚ)⟩ ⟨2, 12⟩ ⟨2, 12⟩ (.leaf ⟨(4/1:ℚ), (4/1:ℚ)⟩))))))) (.binary ⟨(128/1:ℚ), (128/1:ℚ)⟩ (.unary ⟨(128/1:ℚ), (128/1:ℚ)⟩ (.binary ⟨(1024/1:ℚ), (1024/1:ℚ)⟩ (.leaf ⟨(1024/1:ℚ), (1024/1:ℚ)⟩) (.unary ⟨(314180672/76545:ℚ), (2827664128/688905:ℚ)⟩ (.binary ⟨(288769/76545:ℚ), (2598956/688905:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.binary ⟨(212224/76545:ℚ), (1910051/688905:ℚ)⟩ (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩) (.logarithm ⟨(212224/76545:ℚ), (1910051/688905:ℚ)⟩ ⟨4, 12⟩ ⟨4, 12⟩ (.leaf ⟨(16/1:ℚ), (16/1:ℚ)⟩))))))) (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.binary ⟨(34067524/76545:ℚ), (306612476/688905:ℚ)⟩ (.leaf ⟨(1024/1:ℚ), (1024/1:ℚ)⟩) (.unary ⟨(34067524/76545:ℚ), (306612476/688905:ℚ)⟩ (.binary ⟨(500993/76545:ℚ), (4509007/688905:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.binary ⟨(424448/76545:ℚ), (3820102/688905:ℚ)⟩ (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩) (.logarithm ⟨(424448/76545:ℚ), (3820102/688905:ℚ)⟩ ⟨8, 12⟩ ⟨8, 12⟩ (.leaf ⟨(256/1:ℚ), (256/1:ℚ)⟩))))))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩)))))
    norm_num [gaps, weights, selected, points, Fin.sum_univ_succ, Fin.forall_fin_succ, accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ, objectiveExpr, costs, inBand, imin, imax, tailWorkExpr, tailWeights]
#print axioms certified_value
