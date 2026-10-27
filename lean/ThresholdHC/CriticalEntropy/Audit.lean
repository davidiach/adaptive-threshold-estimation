import ThresholdHC.CriticalEntropy.Packing
import ThresholdHC.CriticalEntropy.CommonPoint
import ThresholdHC.CriticalEntropy.Specification
import ThresholdHC.CriticalEntropy.EventInformation
import ThresholdHC.CriticalEntropy.FiniteGap
import ThresholdHC.CriticalEntropy.StoppedTape
import ThresholdHC.CriticalEntropy.RestartPair
import ThresholdHC.CriticalEntropy.RepeatedRestart
import ThresholdHC.CriticalEntropy.EstimationEntropy
import ThresholdHC.CriticalEntropy.PopulationMixture
import ThresholdHC.CriticalEntropy.GoodGaps
import ThresholdHC.CriticalEntropy.CriticalScale
import ThresholdHC.CriticalEntropy.BaseCost

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

example : RepeatedSignTestStatement := by
  intro R _ ν _ p A hf h n hn a M t ha hM
  exact ⟨repeated_sign_work ν p A hf n t,
    (fun hm => repeated_sign_plus_error ν p A hf h n hn a M t ha hM hm),
    (fun hm => repeated_sign_minus_error ν p A hf h n hn a M t ha hM hm)⟩

example : FiniteGapEstimationEntropyStatement := fun _ => finite_gap_estimation_entropy

example : PopulationMomentStatement := by
  intro D R _ _ μ _ ν _ p₀ p₁ q h₀ h₁ hq A
  exact ⟨population_second_moment_formula μ ν p₀ p₁ q h₀ h₁ hq A,
    population_work_formula μ ν p₀ p₁ q h₀ h₁ hq A,
    population_mean_formula μ ν p₀ p₁ q h₀ h₁ hq A⟩

example : PopulationFinitenessStatement := by
  intro D R _ _ μ _ ν _ p₀ p₁ h₀ h₁ c hc A hm₀ hm₁ hw₀ hw₁
  obtain ⟨ha,hi₀,hi₁⟩ := population_conditional_finiteness μ ν p₀ p₁ h₀ h₁ c hc A hm₀ hm₁ hw₀ hw₁
  exact ⟨ha,hi₀,hi₁,population_finiteness_transfer μ ν p₀ p₁ h₀ h₁ c hc A hm₀ hm₁ hw₀ hw₁⟩

example : PopulationVarianceFloorStatement := fun _ _ => population_evariance_floor

example : PopulationMomentFromVarianceStatement := fun _ _ => population_moment_bound_of_evariance

example : PopulationGoodGapsStatement := fun _ => population_good_gaps

example : CriticalLawStatement := by
  refine ⟨inferInstance, inferInstance, criticalGapLaw_supported, ?_, criticalParameter_coe_of_mem⟩
  intro x hx hx'
  simpa using criticalGapLaw_Ioc 0 x (by norm_num) hx hx'

example : CriticalScaleProductStatement := fun _ => critical_scale_product

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
#print axioms stopped_before_prefix_ext
#print axioms stoppedToSignTest
#print axioms repeatedSignDecision
#print axioms measurable_repeatedSignDecision
#print axioms repeatedSignTest
#print axioms iid_sum_memLp
#print axioms iid_sum_integral
#print axioms iid_sum_variance
#print axioms iid_sum_deviation
#print axioms iid_sum_lower_error
#print axioms iid_sum_upper_error
#print axioms repeated_sign_work
#print axioms repeated_sign_plus_error
#print axioms repeated_sign_minus_error
#print axioms finite_gap_estimation_entropy
#print axioms critical_restart_count_bounds
#print axioms RepeatedSignTestStatement
#print axioms FiniteGapEstimationEntropyStatement
#print axioms uniformUnitMeasure
#print axioms uniformUnitMeasure_probability
#print axioms uniformCoinFlip
#print axioms measurable_uniformCoinFlip
#print axioms uniformTapeMeasure
#print axioms uniformTapeMeasure_probability
#print axioms uniformCoinTape
#print axioms measurable_uniformCoinTape
#print axioms uniformProcedureState
#print axioms measurable_uniformProcedureState
#print axioms conditionalSecondMoment
#print axioms conditionalMean
#print axioms mixtureParameter
#print axioms measurable_mixtureParameter
#print axioms populationInput
#print axioms measurable_populationInput
#print axioms populationMeasure
#print axioms populationSecondMoment
#print axioms populationExpectedWork
#print axioms populationMean
#print axioms uniformCoinFlip_true
#print axioms uniformCoinFlip_map
#print axioms uniformCoinTape_map
#print axioms seeded_uniformCoinTape_map
#print axioms conditionalSecondMoment_uniform
#print axioms conditionalMean_uniform
#print axioms conditionalWork_uniform
#print axioms measurable_conditionalSecondMoment
#print axioms measurable_conditionalMean
#print axioms measurable_conditionalWork
#print axioms conditionalSecondMoment_finite_iff
#print axioms conditionalMean_output_law
#print axioms conditionalSecondMoment_output_law
#print axioms seeded_lintegral_uniform
#print axioms measurable_seeded_lintegral
#print axioms measurable_seeded_integral
#print axioms conditionalMean_integrable_of_moment
#print axioms mixtureParameter_map
#print axioms lintegral_bernoulli_parameter
#print axioms mixtureParameter_lintegral
#print axioms population_lintegral
#print axioms population_lintegral_const
#print axioms population_finite_components
#print axioms population_ae_finite_components
#print axioms mixtureParameter_integral
#print axioms population_integral
#print axioms population_finite_all
#print axioms population_conditional_finiteness
#print axioms population_second_moment_formula
#print axioms population_work_formula
#print axioms population_mean_formula
#print axioms population_finiteness_transfer
#print axioms PopulationMomentStatement
#print axioms PopulationFinitenessStatement
#print axioms population_memLp_of_moment
#print axioms population_second_moment_toReal
#print axioms variance_lower_of_mixture
#print axioms population_second_moment_const
#print axioms population_mean_const
#print axioms population_variance_mixture_lower
#print axioms population_variance_floor
#print axioms conditionalMean_sq_le_moment
#print axioms population_moment_bound_of_variance
#print axioms population_moment_finite_of_evariance
#print axioms population_evariance_floor
#print axioms population_moment_bound_of_evariance
#print axioms CappedPrior
#print axioms halfPrior
#print axioms CappedPopulationGuarantee
#print axioms PopulationGoodGap
#print axioms conditional_moment_pair_integrable
#print axioms population_second_moment_real_formula
#print axioms measurable_halfPrior
#print axioms halfPrior_le_half
#print axioms halfPrior_integral
#print axioms cappedPrior_const
#print axioms cappedPrior_half
#print axioms halfPrior_weighted_integral
#print axioms population_halfPrior_moment
#print axioms population_halfPrior_mean
#print axioms exists_subset_real_measure
#print axioms bad_set_mass_lt_of_integral_lower
#print axioms bad_set_mass_lt_of_integral_upper
#print axioms population_good_gaps
#print axioms PopulationVarianceFloorStatement
#print axioms PopulationMomentFromVarianceStatement
#print axioms PopulationGoodGapsStatement

#print axioms criticalGapLaw
#print axioms criticalUpper
#print axioms criticalAnnulus
#print axioms criticalParameter
#print axioms criticalGapLaw_noAtoms
#print axioms linear_density_interval
#print axioms criticalGapLaw_Ioc
#print axioms criticalGapLaw_supported
#print axioms criticalGapLaw_probability
#print axioms criticalGapLaw_real_Ioc
#print axioms criticalUpper_pos
#print axioms criticalUpper_le_quarter
#print axioms criticalUpper_succ
#print axioms criticalAnnulus_mass
#print axioms criticalAnnulus_adjacent
#print axioms criticalUpper_antitone
#print axioms criticalAnnulus_disjoint
#print axioms measurable_criticalParameter
#print axioms criticalParameter_eq_sign
#print axioms criticalParameter_coe_of_mem
#print axioms exists_good_point_low_work
#print axioms criticalAnnulus_work_factor
#print axioms critical_annulus_work_sum
#print axioms critical_annulus_good_points
#print axioms population_negative_work_integral
#print axioms critical_scale_entropy
#print axioms critical_scale_product
#print axioms CriticalLawStatement
#print axioms CriticalScaleProductStatement

example : ActivationNormalizationStatement := fun _ => activation_product_bounds

example : CriticalRawBaseCostStatement := critical_raw_base_cost

example : CriticalBaseCostStatement := critical_base_cost

#print axioms activeSeeds
#print axioms measurableSet_activeSeeds
#print axioms stop_zero_iff_inactive
#print axioms inactive_output
#print axioms inactive_work
#print axioms active_work_lower
#print axioms activation_work_restrict
#print axioms activation_conditional_work
#print axioms activation_probability_le_work
#print axioms activation_conditional_work_lower
#print axioms normalized_event_mean
#print axioms normalized_event_moment
#print axioms populationSeedEvent
#print axioms measurableSet_populationSeedEvent
#print axioms populationSeedEvent_measure
#print axioms populationMeasure_restrict_seed
#print axioms populationMeasure_smul_seed
#print axioms populationMeasure_condition_seed
#print axioms population_inactive_mean
#print axioms activeProcedure
#print axioms population_activation_mean
#print axioms population_activation_work
#print axioms activation_positive_of_bias
#print axioms population_activation_moment
#print axioms active_population_guarantee
#print axioms capped_guarantee_moment_floor
#print axioms population_null_work_ge_activation
#print axioms activation_product_bounds
#print axioms critical_product_scale
#print axioms entropy_scale_count
#print axioms critical_annulus_mass_of_small_product
#print axioms entropy_logs_le_exp
#print axioms criticalLogFactor
#print axioms critical_scalar_base_cost
#print axioms critical_raw_base_cost
#print axioms critical_base_cost
#print axioms ActivationNormalizationStatement
#print axioms CriticalRawBaseCostStatement
#print axioms CriticalBaseCostStatement
