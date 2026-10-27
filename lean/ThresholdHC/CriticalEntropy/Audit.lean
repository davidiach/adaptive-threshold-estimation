import ThresholdHC.CriticalEntropy.Packing
import ThresholdHC.CriticalEntropy.CommonPoint
import ThresholdHC.CriticalEntropy.Specification
import ThresholdHC.CriticalEntropy.EventInformation

open ThresholdHC.CriticalEntropy

example : EntropyPackingStatement := entropy_of_gap_count

example : CommonPointStatement := fun _ _ => common_point_of_finite_mixtures

example : PrefixInformationStatement := fun _ _ => prefix_observable_kl_le

example : PrefixEventTransferStatement := fun _ => fair_prefix_event_mass_lower

#print axioms sum_event_mass_le_overlap
#print axioms event_packing
#print axioms overlap_bound
#print axioms entropy_of_packing
#print axioms entropy_of_gap_count
#print axioms finite_common_point
#print axioms common_point_of_finite_mixtures
#print axioms EntropyPackingStatement
#print axioms CommonPointStatement
#print axioms streamProb_pos
#print axioms stream_kl_identity
#print axioms finiteMeasure_positive
#print axioms finiteMeasure_density
#print axioms seeded_prefix_kl
#print axioms binary_kl_le_chisq
#print axioms seeded_prefix_kl_le_chisq
#print axioms seeded_tape_prefix_map
#print axioms prefix_observable_kl_le
#print axioms binary_kl_lower_log
#print axioms event_binary_kl_le
#print axioms event_mass_lower_of_kl
#print axioms prefix_event_mass_lower
#print axioms fair_prefix_event_mass_lower
#print axioms PrefixInformationStatement
#print axioms PrefixEventTransferStatement
