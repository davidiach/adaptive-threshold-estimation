import ThresholdHC.CriticalEntropy.Packing
import ThresholdHC.CriticalEntropy.CommonPoint
import ThresholdHC.CriticalEntropy.Specification
import ThresholdHC.CriticalEntropy.EventInformation
import ThresholdHC.CriticalEntropy.FiniteGap
import ThresholdHC.CriticalEntropy.StoppedTape
import ThresholdHC.CriticalEntropy.RestartPair
import ThresholdHC.CriticalEntropy.RepeatedRestart

open ThresholdHC.CriticalEntropy

example : EntropyPackingStatement := entropy_of_gap_count

example : CommonPointStatement := fun _ _ => common_point_of_finite_mixtures

example : PrefixInformationStatement := fun _ _ => prefix_observable_kl_le

example : PrefixEventTransferStatement := fun _ => fair_prefix_event_mass_lower

example : FiniteGapSignEntropyStatement := fun _ => finite_gap_sign_entropy

example : StoppedSuffixStatement := fun _ _ => stopped_marked_suffix_map

example : SequentialRestartStatement := fun _ _ _ _ _ _ _ _ ν η _ _ p A B h =>
  ⟨sequential_output_map ν η p A B h, sequential_expected_work ν η p A B h⟩

example : RepeatedRestartStatement := fun _ _ _ _ ν _ p A h n =>
  ⟨repeated_output_map ν p A h n, repeated_expected_work ν p A h n⟩

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
#print axioms tapeDrop
#print axioms measurable_tapeDrop
#print axioms StoppedProcedure
#print axioms stoppedSuffix
#print axioms measurable_stoppedSuffix
#print axioms stoppedProcedureWork
#print axioms expectedStoppedProcedureWork
#print axioms measurable_stoppedProcedureWork
#print axioms stoppedWithWork
#print axioms tapeDrop_map
#print axioms prefix_drop_independent
#print axioms tape_split_map
#print axioms seeded_tape_split_map
#print axioms measure_eq_tsum_stopping
#print axioms seeded_prefix_drop_probability
#print axioms stopped_event_tail_probability
#print axioms stopped_output_suffix_probability
#print axioms stopped_output_suffix_map
#print axioms stopped_procedure_terminates
#print axioms stopped_marked_suffix_map
#print axioms StoppedSuffixStatement
#print axioms completePrefix
#print axioms measurable_completePrefix
#print axioms tapePrefix_completePrefix
#print axioms prefix_eq_restrict
#print axioms prefix_eq_drop
#print axioms stopped_prefix_ext
#print axioms restartInput
#print axioms measurable_restartInput
#print axioms sequentialStop
#print axioms sequentialOutput
#print axioms measurable_sequentialStop
#print axioms measurable_sequentialOutput
#print axioms sequential_prefix_ext
#print axioms sequentialProcedure
#print axioms prod_swap_middle
#print axioms seeded_stopped_suffix_map
#print axioms two_run_marked_map
#print axioms two_run_expected_work
#print axioms sequential_expected_work
#print axioms sequential_output_map
#print axioms SequentialRestartStatement
#print axioms reseedProcedure
#print axioms postprocessProcedure
#print axioms emptyProcedure
#print axioms measurable_finCons
#print axioms repeatedProcedure
#print axioms fin_seed_split_map
#print axioms reseed_expected_work
#print axioms repeated_expected_work
#print axioms reseed_output_map
#print axioms fin_product_cons_map
#print axioms repeated_output_map
#print axioms RepeatedRestartStatement
