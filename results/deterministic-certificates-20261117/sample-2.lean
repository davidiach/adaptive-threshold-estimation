import ThresholdHC.DeterministicCertificates.Entropy
open ThresholdHC.DeterministicCertificates
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
theorem certified_value : Contains ⟨(3/4:ℚ), (3/4:ℚ)⟩ (Real.sqrt ((9/16:ℚ):ℝ)) := by
  apply accepted_sound (e := .sqrt (.rational (9/16:ℚ))) (c := (.unary ⟨(3/4:ℚ), (3/4:ℚ)⟩ (.leaf ⟨(9/16:ℚ), (9/16:ℚ)⟩)))
  norm_num [accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ]
#print axioms certified_value
theorem certified_precision :
    ((3/4:ℚ):ℝ) - ((3/4:ℚ):ℝ) ≤ ((1/1208925819614629174706176:ℚ):ℝ) *
      min 1 (Real.sqrt ((9/16:ℚ):ℝ)) := by
  apply sqrtPrecisionCheck_sound (output := ⟨(3/4:ℚ), (3/4:ℚ)⟩)
  · norm_num [sqrtPrecisionCheck]
  · norm_num
#print axioms certified_precision
