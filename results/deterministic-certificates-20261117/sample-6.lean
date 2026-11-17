import ThresholdHC.DeterministicCertificates.Entropy
open ThresholdHC.DeterministicCertificates
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
theorem certified_value : Contains ⟨(0/1:ℚ), (0/1:ℚ)⟩ (ThresholdHC.EntropyTailQuantile.costEntropy (fun i => ((![(0/1:ℚ), (0/1:ℚ)] : Fin 2 → ℚ) i : ℝ))) := by
  apply entropy_accepted_sound (![(0/1:ℚ), (0/1:ℚ)] : Fin 2 → ℚ) (by norm_num [Fin.forall_fin_succ]) (c := (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩) (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩) (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩)))))
  norm_num [accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ]
#print axioms certified_value
