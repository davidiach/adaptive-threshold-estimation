import ThresholdHC.DeterministicCertificates.Entropy
open ThresholdHC.DeterministicCertificates
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
theorem certified_value : Contains ⟨(3/1:ℚ), (3/1:ℚ)⟩ (Real.sqrt ((2/1:ℚ):ℝ)) := by
  apply accepted_sound (e := .sqrt (.rational (2/1:ℚ))) (c := (.unary ⟨(3/1:ℚ), (3/1:ℚ)⟩ (.leaf ⟨(2/1:ℚ), (2/1:ℚ)⟩)))
  norm_num [accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ]
#print axioms certified_value
theorem certified_precision :
    ((3/1:ℚ):ℝ) - ((3/1:ℚ):ℝ) ≤ ((1/65536:ℚ):ℝ) *
      min 1 (Real.sqrt ((2/1:ℚ):ℝ)) := by
  apply sqrtPrecisionCheck_sound (output := ⟨(3/1:ℚ), (3/1:ℚ)⟩)
  · norm_num [sqrtPrecisionCheck]
  · norm_num
#print axioms certified_precision
