import ThresholdHC.DeterministicCertificates.Entropy
open ThresholdHC.DeterministicCertificates
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
theorem certified_value : Contains ⟨(0/1:ℚ), (0/1:ℚ)⟩ (ThresholdHC.EntropyTailQuantile.costEntropy (fun i => ((![(1/1:ℚ), (2/1:ℚ)] : Fin 2 → ℚ) i : ℝ))) := by
  apply entropy_accepted_sound (![(1/1:ℚ), (2/1:ℚ)] : Fin 2 → ℚ) (by norm_num [Fin.forall_fin_succ]) (c := (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.leaf ⟨(3/1:ℚ), (3/1:ℚ)⟩) (.binary ⟨(326261056/170859375:ℚ), (2936369582/1537734375:ℚ)⟩ (.unary ⟨(1313942464/1196015625:ℚ), (23651240341/21528281250:ℚ)⟩ (.logarithm ⟨(1313942464/1196015625:ℚ), (23651240341/21528281250:ℚ)⟩ ⟨1, 12⟩ ⟨1, 12⟩ (.leaf ⟨(3/1:ℚ), (3/1:ℚ)⟩))) (.binary ⟨(1330432/1640625:ℚ), (23947783/29531250:ℚ)⟩ (.unary ⟨(1330432/1640625:ℚ), (23947783/29531250:ℚ)⟩ (.logarithm ⟨(665216/1640625:ℚ), (23947783/59062500:ℚ)⟩ ⟨0, 12⟩ ⟨0, 12⟩ (.leaf ⟨(3/2:ℚ), (3/2:ℚ)⟩))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩)))))
  norm_num [accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ]
#print axioms certified_value
