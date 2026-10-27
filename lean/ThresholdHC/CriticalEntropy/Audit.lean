import ThresholdHC.CriticalEntropy.Packing
import ThresholdHC.CriticalEntropy.CommonPoint
import ThresholdHC.CriticalEntropy.Specification

open ThresholdHC.CriticalEntropy

example : EntropyPackingStatement := entropy_of_gap_count

example : CommonPointStatement := fun _ _ => common_point_of_finite_mixtures

#print axioms sum_event_mass_le_overlap
#print axioms event_packing
#print axioms overlap_bound
#print axioms entropy_of_packing
#print axioms entropy_of_gap_count
#print axioms finite_common_point
#print axioms common_point_of_finite_mixtures
#print axioms EntropyPackingStatement
#print axioms CommonPointStatement
