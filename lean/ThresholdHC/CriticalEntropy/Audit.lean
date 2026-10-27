import ThresholdHC.CriticalEntropy.Packing
import ThresholdHC.CriticalEntropy.CommonPoint
import ThresholdHC.CriticalEntropy.Specification
import ThresholdHC.CriticalEntropy.EventInformation
import ThresholdHC.CriticalEntropy.FiniteGap

open ThresholdHC.CriticalEntropy

example : EntropyPackingStatement := entropy_of_gap_count

example : CommonPointStatement := fun _ _ => common_point_of_finite_mixtures

example : PrefixInformationStatement := fun _ _ => prefix_observable_kl_le

example : PrefixEventTransferStatement := fun _ => fair_prefix_event_mass_lower

example : FiniteGapSignEntropyStatement := fun _ => finite_gap_sign_entropy

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
#print axioms SignTest
#print axioms signTestWork
#print axioms expectedSignTestWork
#print axioms signTestWindow
#print axioms measurable_signTestWork
#print axioms measurable_signTestWindow
#print axioms signTest_prefix_probability
#print axioms signTest_terminates
#print axioms signTest_late_probability
#print axioms signTest_window_probability
#print axioms binary_kl_separation
#print axioms early_event_probability
#print axioms EntropyGap
#print axioms signParameter
#print axioms signParameter_interior
#print axioms early_prefix_information
#print axioms signTest_early_minus
#print axioms entropyLowerTime
#print axioms entropyUpperTime
#print axioms entropyLowerTime_bounds
#print axioms entropyUpperTime_bounds
#print axioms signTest_quarter_late
#print axioms signTest_negative_window
#print axioms restrictPrefix
#print axioms signTestWindowPrefix
#print axioms measurable_signTestWindowPrefix
#print axioms signTestWindowPrefix_preimage
#print axioms signTestWindowPrefix_probability
#print axioms signTestWindow_positive_imp_lt
#print axioms signTest_fair_window
#print axioms signTest_window_scale
#print axioms geometric_separation_of_adjacent
#print axioms half_low_cost
#print axioms geometric_interval_card
#print axioms inverse_gap_scales_separated
#print axioms signTest_window_overlap
#print axioms finite_gap_sign_entropy
#print axioms FiniteGapSignEntropyStatement
