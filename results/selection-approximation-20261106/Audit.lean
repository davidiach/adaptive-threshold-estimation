import ThresholdHC.SelectionApproximation.Model
import ThresholdHC.SelectionApproximation.Entropy
import ThresholdHC.SelectionApproximation.Compression
example : ThresholdHC.SelectionApproximation.EntropyPerturbationStatement := ThresholdHC.SelectionApproximation.entropy_perturbation
example : ThresholdHC.SelectionApproximation.CompressionInvariantStatement := ThresholdHC.SelectionApproximation.compression_invariant

open ThresholdHC.SelectionApproximation
example : ValidBins 1 (fun x : ℝ => x) := validBins_identity
example : Close (1+1/(2:ℝ)) 1 (3/2) := by
  apply dyadic_cell_close (scale := 1) (M := 2) (j := 0) <;> norm_num

#print axioms ThresholdHC.SelectionApproximation.Close
#print axioms ThresholdHC.SelectionApproximation.CompressionInvariantStatement
#print axioms ThresholdHC.SelectionApproximation.EntropyPerturbationStatement
#print axioms ThresholdHC.SelectionApproximation.ValidBins
#print axioms ThresholdHC.SelectionApproximation.baseSummary
#print axioms ThresholdHC.SelectionApproximation.close_abs_sub
#print axioms ThresholdHC.SelectionApproximation.close_add_same
#print axioms ThresholdHC.SelectionApproximation.close_refl
#print axioms ThresholdHC.SelectionApproximation.close_trans
#print axioms ThresholdHC.SelectionApproximation.close_zero
#print axioms ThresholdHC.SelectionApproximation.compression_invariant
#print axioms ThresholdHC.SelectionApproximation.costEntropy_eq_potential_sub
#print axioms ThresholdHC.SelectionApproximation.dyadic_cell_close
#print axioms ThresholdHC.SelectionApproximation.entropy_perturbation
#print axioms ThresholdHC.SelectionApproximation.entropy_relative
#print axioms ThresholdHC.SelectionApproximation.entropy_zero_of_close
#print axioms ThresholdHC.SelectionApproximation.interval_close
#print axioms ThresholdHC.SelectionApproximation.potential
#print axioms ThresholdHC.SelectionApproximation.potential_hasDerivAt
#print axioms ThresholdHC.SelectionApproximation.potential_lipschitz
#print axioms ThresholdHC.SelectionApproximation.summaryKey
#print axioms ThresholdHC.SelectionApproximation.surrogate_bounds
#print axioms ThresholdHC.SelectionApproximation.trace_nonneg
#print axioms ThresholdHC.SelectionApproximation.trimSolve
#print axioms ThresholdHC.SelectionApproximation.trimSolve_subset
#print axioms ThresholdHC.SelectionApproximation.validBins_identity
#print axioms ThresholdHC.SelectionApproximation.validBins_of_intervals
