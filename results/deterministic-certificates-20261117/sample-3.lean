import ThresholdHC.DeterministicCertificates.Entropy
open ThresholdHC.DeterministicCertificates
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
theorem certified_value : Contains ⟨(-1910051/918540:ℚ), (-53056/25515:ℚ)⟩ (Real.log ((1/8:ℚ):ℝ)) := by
  apply accepted_sound (e := .log (.rational (1/8:ℚ))) (c := (.logarithm ⟨(-1910051/918540:ℚ), (-53056/25515:ℚ)⟩ ⟨-3, 12⟩ ⟨-3, 12⟩ (.leaf ⟨(1/8:ℚ), (1/8:ℚ)⟩)))
  norm_num [accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ]
#print axioms certified_value
