import ThresholdHC.Proofs.Algebra
import ThresholdHC.Proofs.Calibration
import ThresholdHC.Proofs.Classifier
import ThresholdHC.Proofs.Constants
import ThresholdHC.Proofs.FixedGap
import ThresholdHC.Proofs.Hellinger
import ThresholdHC.Proofs.KL
import ThresholdHC.Proofs.Modulus
import ThresholdHC.Proofs.Tier2.ClassifierProb
import ThresholdHC.Proofs.Tier2.Information
import ThresholdHC.Proofs.Tier2.RareEvent
import ThresholdHC.ResearchRouteA.Sanity
import ThresholdHC.Tier3.Examples
import ThresholdHC.Tier3.ExamplesModel
import ThresholdHC.Tier3.Full
import ThresholdHC.Tier3.IntegralLogSum
import ThresholdHC.Tier3.Optimizer
import ThresholdHC.Tier3.OptimizerModel
import ThresholdHC.Tier3.Randomized
import ThresholdHC.Tier3.RandomizedBase
import ThresholdHC.Tier3.RandomizedModel
import ThresholdHC.Tier3.Specification
import ThresholdHC.Tier3.Stopping
import ThresholdHC.Tier3.StoppingBase
import ThresholdHC.Tier3.StoppingModel
import ThresholdHC.Tier3.TranscriptRatio
import ThresholdHC.Tier4.BoundReduction
import ThresholdHC.Tier4.Entropy
import ThresholdHC.Tier4.FiniteBase
import ThresholdHC.Tier4.FiniteDensity
import ThresholdHC.Tier4.Full
import ThresholdHC.Tier4.Model
import ThresholdHC.Tier4.Specification
import ThresholdHC.Tier4.StoppedFull
import ThresholdHC.Tier4.StoppedReconstruction
import ThresholdHC.Uniform713
import ThresholdHC.Uniform713.Arithmetic
import ThresholdHC.Uniform713.Classifier
import ThresholdHC.Uniform713.ClassifierModel
import ThresholdHC.Uniform713.Common
import ThresholdHC.Uniform713.Concentration
import ThresholdHC.Uniform713.Conditional
import ThresholdHC.Uniform713.Convergence
import ThresholdHC.Uniform713.CoupledWork
import ThresholdHC.Uniform713.Estimator
import ThresholdHC.Uniform713.Examples
import ThresholdHC.Uniform713.FullBound
import ThresholdHC.Uniform713.Integration
import ThresholdHC.Uniform713.Series
import ThresholdHC.Uniform713.Specification
import ThresholdHC.Uniform713.WorkArithmetic
theorem MinimaxReplay.tier3_randomized_law_total : ThresholdHC.Tier3.RandomizedTotalStatement := ThresholdHC.Tier3.randomized_law_total
theorem MinimaxReplay.tier3_randomized_information_bound : ThresholdHC.Tier3.RandomizedInformationStatement := ThresholdHC.Tier3.randomized_information_bound
theorem MinimaxReplay.tier3_randomized_marginal_kl_bound : ThresholdHC.Tier3.RandomizedMarginalKLStatement := ThresholdHC.Tier3.randomized_marginal_kl_bound
theorem MinimaxReplay.tier3_randomized_testing_bound : ThresholdHC.Tier3.RandomizedTestingStatement := ThresholdHC.Tier3.randomized_testing_bound
theorem MinimaxReplay.tier3_finite_work_stops : ThresholdHC.Tier3.FiniteWorkStopsStatement := ThresholdHC.Tier3.finite_work_stops
theorem MinimaxReplay.tier3_unbounded_stopping : ThresholdHC.Tier3.UnboundedStoppingStatement := ThresholdHC.Tier3.unbounded_stopping
theorem MinimaxReplay.tier3_unbounded_testing : ThresholdHC.Tier3.UnboundedTestingStatement := ThresholdHC.Tier3.unbounded_testing
theorem MinimaxReplay.tier3_arbitrary_law_cutoff : ThresholdHC.Tier3.ArbitraryLawCutoffStatement := ThresholdHC.Tier3.arbitrary_law_cutoff
theorem MinimaxReplay.tier3_arbitrary_law_optimizer : ThresholdHC.Tier3.ArbitraryLawOptimizerStatement := ThresholdHC.Tier3.arbitrary_law_optimizer
theorem MinimaxReplay.tier3_unbounded_example : ThresholdHC.Tier3.UnboundedExampleStatement := ThresholdHC.Tier3.unbounded_example
theorem MinimaxReplay.tier3_tier3_landmark : ThresholdHC.Tier3.Tier3LandmarkStatement := ThresholdHC.Tier3.tier3_landmark
theorem MinimaxReplay.tier4_finite_prefix_kl_identity : ThresholdHC.Tier4.FinitePrefixKLStatement := ThresholdHC.Tier4.finite_prefix_kl_identity
theorem MinimaxReplay.tier4_infinite_kl_eq_iSup : ThresholdHC.Tier4.InfiniteKLSupremumStatement := ThresholdHC.Tier4.infinite_kl_eq_iSup
theorem MinimaxReplay.tier4_infinite_kl_bound : ThresholdHC.Tier4.InfiniteKLBoundStatement := ThresholdHC.Tier4.infinite_kl_bound
theorem MinimaxReplay.tier4_infinite_kl_finite : ThresholdHC.Tier4.InfiniteKLFiniteStatement := ThresholdHC.Tier4.infinite_kl_finite
theorem MinimaxReplay.tier4_observable_kl_bound : ThresholdHC.Tier4.ObservableKLBoundStatement := ThresholdHC.Tier4.observable_kl_bound
theorem MinimaxReplay.tier4_tier4_landmark : ThresholdHC.Tier4.Tier4LandmarkStatement := ThresholdHC.Tier4.tier4_landmark
example : ThresholdHC.Uniform713.FullBound713Statement := ThresholdHC.Uniform713.full_bound_713
theorem MinimaxReplay.scored_posterior_identity : ThresholdHC.Targets.posterior_identity := ThresholdHC.Proofs.posterior_identity
theorem MinimaxReplay.scored_posterior_diff_le : ThresholdHC.Targets.posterior_diff_le := ThresholdHC.Proofs.posterior_diff_le
theorem MinimaxReplay.scored_posterior_mem : ThresholdHC.Targets.posterior_mem := ThresholdHC.Proofs.posterior_mem
theorem MinimaxReplay.scored_pred_variance_ge : ThresholdHC.Targets.pred_variance_ge := ThresholdHC.Proofs.pred_variance_ge
theorem MinimaxReplay.scored_ratio_bound : ThresholdHC.Targets.ratio_bound := ThresholdHC.Proofs.ratio_bound
theorem MinimaxReplay.scored_kl_taylor_bound : ThresholdHC.Targets.kl_taylor_bound := ThresholdHC.Proofs.kl_taylor_bound
theorem MinimaxReplay.scored_lemmaA_forward : ThresholdHC.Targets.lemmaA_forward := ThresholdHC.Proofs.lemmaA_forward
theorem MinimaxReplay.scored_lemmaA_reverse : ThresholdHC.Targets.lemmaA_reverse := ThresholdHC.Proofs.lemmaA_reverse
theorem MinimaxReplay.scored_lemmaA_sharp_at_one : ThresholdHC.Targets.lemmaA_sharp_at_one := ThresholdHC.Proofs.lemmaA_sharp_at_one
theorem MinimaxReplay.scored_hardpair_step_kl : ThresholdHC.Targets.hardpair_step_kl := ThresholdHC.Proofs.hardpair_step_kl
theorem MinimaxReplay.scored_sym_kl_hellinger_pointwise : ThresholdHC.Targets.sym_kl_hellinger_pointwise := ThresholdHC.Proofs.sym_kl_hellinger_pointwise
theorem MinimaxReplay.scored_kl_ge_two_hell_finite : ThresholdHC.Targets.kl_ge_two_hell_finite := ThresholdHC.Proofs.kl_ge_two_hell_finite
theorem MinimaxReplay.scored_sym_kl_ge_eight_hell_finite : ThresholdHC.Targets.sym_kl_ge_eight_hell_finite := ThresholdHC.Proofs.sym_kl_ge_eight_hell_finite
theorem MinimaxReplay.scored_two_point_variance_finite : ThresholdHC.Targets.two_point_variance_finite := ThresholdHC.Proofs.two_point_variance_finite
theorem MinimaxReplay.scored_fixed_gap_unbiased : ThresholdHC.Targets.fixed_gap_unbiased := ThresholdHC.Proofs.fixed_gap_unbiased
theorem MinimaxReplay.scored_fixed_gap_variance : ThresholdHC.Targets.fixed_gap_variance := ThresholdHC.Proofs.fixed_gap_variance
theorem MinimaxReplay.scored_fixed_gap_equality : ThresholdHC.Targets.fixed_gap_equality := ThresholdHC.Proofs.fixed_gap_equality
theorem MinimaxReplay.scored_negbin_total : ThresholdHC.Targets.negbin_total := ThresholdHC.Proofs.negbin_total
theorem MinimaxReplay.scored_negbin_mean : ThresholdHC.Targets.negbin_mean := ThresholdHC.Proofs.negbin_mean
theorem MinimaxReplay.scored_haldane_inverse_moment : ThresholdHC.Targets.haldane_inverse_moment := ThresholdHC.Proofs.haldane_inverse_moment
theorem MinimaxReplay.scored_scaling_up_pointwise : ThresholdHC.Targets.scaling_up_pointwise := ThresholdHC.Proofs.scaling_up_pointwise
theorem MinimaxReplay.scored_scaling_down_pointwise : ThresholdHC.Targets.scaling_down_pointwise := ThresholdHC.Proofs.scaling_down_pointwise
theorem MinimaxReplay.scored_modulus_scaling_up : ThresholdHC.Targets.modulus_scaling_up := ThresholdHC.Proofs.modulus_scaling_up
theorem MinimaxReplay.scored_power_modulus_critical : ThresholdHC.Targets.power_modulus_critical := ThresholdHC.Proofs.power_modulus_critical
theorem MinimaxReplay.scored_power_modulus : ThresholdHC.Targets.power_modulus := ThresholdHC.Proofs.power_modulus
theorem MinimaxReplay.scored_constant_second_moment : ThresholdHC.Targets.constant_second_moment := ThresholdHC.Proofs.constant_second_moment
theorem MinimaxReplay.scored_constant_work : ThresholdHC.Targets.constant_work := ThresholdHC.Proofs.constant_work
theorem MinimaxReplay.scored_kl_delta_identity : ThresholdHC.Targets.kl_delta_identity := ThresholdHC.Proofs.kl_delta_identity
theorem MinimaxReplay.scored_kl_delta_lower : ThresholdHC.Targets.kl_delta_lower := ThresholdHC.Proofs.kl_delta_lower
theorem MinimaxReplay.scored_error_tail_bound : ThresholdHC.Targets.error_tail_bound := ThresholdHC.Proofs.error_tail_bound
theorem MinimaxReplay.scored_classifier_scale_step : ThresholdHC.Targets.classifier_scale_step := ThresholdHC.Proofs.classifier_scale_step
theorem MinimaxReplay.scored_dyadic_sum_v1 : ThresholdHC.Targets.dyadic_sum_v1 := ThresholdHC.Proofs.dyadic_sum_v1
theorem MinimaxReplay.scored_dyadic_sum_v2 : ThresholdHC.Targets.dyadic_sum_v2 := ThresholdHC.Proofs.dyadic_sum_v2
theorem MinimaxReplay.scored_kl_data_processing_finite : ThresholdHC.Targets.kl_data_processing_finite := ThresholdHC.Proofs.kl_data_processing_finite
theorem MinimaxReplay.scored_pinsker_finite : ThresholdHC.Targets.pinsker_finite := ThresholdHC.Proofs.pinsker_finite
theorem MinimaxReplay.scored_two_point_rms_lower : ThresholdHC.Targets.two_point_rms_lower := ThresholdHC.Proofs.two_point_rms_lower
theorem MinimaxReplay.scored_transcript_law_total : ThresholdHC.Targets.transcript_law_total := ThresholdHC.Proofs.transcript_law_total
theorem MinimaxReplay.scored_stopped_transcript_kl : ThresholdHC.Targets.stopped_transcript_kl := ThresholdHC.Proofs.stopped_transcript_kl
theorem MinimaxReplay.scored_stopped_transcript_testing : ThresholdHC.Targets.stopped_transcript_testing := ThresholdHC.Proofs.stopped_transcript_testing
theorem MinimaxReplay.scored_bounded_ratio_log : ThresholdHC.Targets.bounded_ratio_log := ThresholdHC.Proofs.bounded_ratio_log
theorem MinimaxReplay.scored_lemma6_error : ThresholdHC.Targets.lemma6_error := ThresholdHC.Proofs.lemma6_error
theorem MinimaxReplay.scored_lemma6_work : ThresholdHC.Targets.lemma6_work := ThresholdHC.Proofs.lemma6_work
theorem MinimaxReplay.scored_lemma7_telescoping : ThresholdHC.Targets.lemma7_telescoping := ThresholdHC.Proofs.lemma7_telescoping
theorem MinimaxReplay.scored_lemma7_second_moment : ThresholdHC.Targets.lemma7_second_moment := ThresholdHC.Proofs.lemma7_second_moment
theorem MinimaxReplay.scored_lemma7_work : ThresholdHC.Targets.lemma7_work := ThresholdHC.Proofs.lemma7_work
theorem MinimaxReplay.scored_psi_optimizer_atomic : ThresholdHC.Targets.psi_optimizer_atomic := ThresholdHC.Proofs.psi_optimizer_atomic
example : ThresholdHC.ResearchRouteA.SeparateMomentBoundsStatement := ThresholdHC.ResearchRouteA.separate_moment_bounds
example : ThresholdHC.ResearchRouteA.UniformFamilyBoundsStatement := ThresholdHC.ResearchRouteA.uniform_family_bounds
#print axioms MinimaxReplay.scored_bounded_ratio_log
#print axioms MinimaxReplay.scored_classifier_scale_step
#print axioms MinimaxReplay.scored_constant_second_moment
#print axioms MinimaxReplay.scored_constant_work
#print axioms MinimaxReplay.scored_dyadic_sum_v1
#print axioms MinimaxReplay.scored_dyadic_sum_v2
#print axioms MinimaxReplay.scored_error_tail_bound
#print axioms MinimaxReplay.scored_fixed_gap_equality
#print axioms MinimaxReplay.scored_fixed_gap_unbiased
#print axioms MinimaxReplay.scored_fixed_gap_variance
#print axioms MinimaxReplay.scored_haldane_inverse_moment
#print axioms MinimaxReplay.scored_hardpair_step_kl
#print axioms MinimaxReplay.scored_kl_data_processing_finite
#print axioms MinimaxReplay.scored_kl_delta_identity
#print axioms MinimaxReplay.scored_kl_delta_lower
#print axioms MinimaxReplay.scored_kl_ge_two_hell_finite
#print axioms MinimaxReplay.scored_kl_taylor_bound
#print axioms MinimaxReplay.scored_lemma6_error
#print axioms MinimaxReplay.scored_lemma6_work
#print axioms MinimaxReplay.scored_lemma7_second_moment
#print axioms MinimaxReplay.scored_lemma7_telescoping
#print axioms MinimaxReplay.scored_lemma7_work
#print axioms MinimaxReplay.scored_lemmaA_forward
#print axioms MinimaxReplay.scored_lemmaA_reverse
#print axioms MinimaxReplay.scored_lemmaA_sharp_at_one
#print axioms MinimaxReplay.scored_modulus_scaling_up
#print axioms MinimaxReplay.scored_negbin_mean
#print axioms MinimaxReplay.scored_negbin_total
#print axioms MinimaxReplay.scored_pinsker_finite
#print axioms MinimaxReplay.scored_posterior_diff_le
#print axioms MinimaxReplay.scored_posterior_identity
#print axioms MinimaxReplay.scored_posterior_mem
#print axioms MinimaxReplay.scored_power_modulus
#print axioms MinimaxReplay.scored_power_modulus_critical
#print axioms MinimaxReplay.scored_pred_variance_ge
#print axioms MinimaxReplay.scored_psi_optimizer_atomic
#print axioms MinimaxReplay.scored_ratio_bound
#print axioms MinimaxReplay.scored_scaling_down_pointwise
#print axioms MinimaxReplay.scored_scaling_up_pointwise
#print axioms MinimaxReplay.scored_stopped_transcript_kl
#print axioms MinimaxReplay.scored_stopped_transcript_testing
#print axioms MinimaxReplay.scored_sym_kl_ge_eight_hell_finite
#print axioms MinimaxReplay.scored_sym_kl_hellinger_pointwise
#print axioms MinimaxReplay.scored_transcript_law_total
#print axioms MinimaxReplay.scored_two_point_rms_lower
#print axioms MinimaxReplay.scored_two_point_variance_finite
#print axioms MinimaxReplay.tier3_arbitrary_law_cutoff
#print axioms MinimaxReplay.tier3_arbitrary_law_optimizer
#print axioms MinimaxReplay.tier3_finite_work_stops
#print axioms MinimaxReplay.tier3_randomized_information_bound
#print axioms MinimaxReplay.tier3_randomized_law_total
#print axioms MinimaxReplay.tier3_randomized_marginal_kl_bound
#print axioms MinimaxReplay.tier3_randomized_testing_bound
#print axioms MinimaxReplay.tier3_tier3_landmark
#print axioms MinimaxReplay.tier3_unbounded_example
#print axioms MinimaxReplay.tier3_unbounded_stopping
#print axioms MinimaxReplay.tier3_unbounded_testing
#print axioms MinimaxReplay.tier4_finite_prefix_kl_identity
#print axioms MinimaxReplay.tier4_infinite_kl_bound
#print axioms MinimaxReplay.tier4_infinite_kl_eq_iSup
#print axioms MinimaxReplay.tier4_infinite_kl_finite
#print axioms MinimaxReplay.tier4_observable_kl_bound
#print axioms MinimaxReplay.tier4_tier4_landmark
#print axioms ThresholdHC.ResearchRouteA.deterministic_gap_model
#print axioms ThresholdHC.ResearchRouteA.deterministic_gap_separate_bounds
#print axioms ThresholdHC.ResearchRouteA.independent_constant_observations
#print axioms ThresholdHC.ResearchRouteA.separate_moment_bounds
#print axioms ThresholdHC.ResearchRouteA.uniform_family_bounds
#print axioms ThresholdHC.Tier3.ArbitraryLawCutoffStatement
#print axioms ThresholdHC.Tier3.ArbitraryLawOptimizerStatement
#print axioms ThresholdHC.Tier3.FeasibleAllocation
#print axioms ThresholdHC.Tier3.FiniteWorkStopsStatement
#print axioms ThresholdHC.Tier3.MeasurablePolicy
#print axioms ThresholdHC.Tier3.MeasurableTest
#print axioms ThresholdHC.Tier3.PolicyCode
#print axioms ThresholdHC.Tier3.Prefix
#print axioms ThresholdHC.Tier3.ProcessTape
#print axioms ThresholdHC.Tier3.RandomizedInformationStatement
#print axioms ThresholdHC.Tier3.RandomizedMarginalKLStatement
#print axioms ThresholdHC.Tier3.RandomizedTestingStatement
#print axioms ThresholdHC.Tier3.RandomizedTotalStatement
#print axioms ThresholdHC.Tier3.RealizesPrefixes
#print axioms ThresholdHC.Tier3.Tier3LandmarkStatement
#print axioms ThresholdHC.Tier3.UnboundedExampleStatement
#print axioms ThresholdHC.Tier3.UnboundedStoppingStatement
#print axioms ThresholdHC.Tier3.UnboundedTestingStatement
#print axioms ThresholdHC.Tier3.acceptance_eq_code
#print axioms ThresholdHC.Tier3.acceptedBy
#print axioms ThresholdHC.Tier3.acceptedBy_processPrefix_iff
#print axioms ThresholdHC.Tier3.allocation
#print axioms ThresholdHC.Tier3.allocationMass
#print axioms ThresholdHC.Tier3.allocationMass_continuous
#print axioms ThresholdHC.Tier3.allocationMass_half
#print axioms ThresholdHC.Tier3.allocationMass_zero
#print axioms ThresholdHC.Tier3.allocation_eq_one
#print axioms ThresholdHC.Tier3.allocation_feasible
#print axioms ThresholdHC.Tier3.allocation_le_one
#print axioms ThresholdHC.Tier3.allocation_mono
#print axioms ThresholdHC.Tier3.allocation_nonneg
#print axioms ThresholdHC.Tier3.allocation_payoff_regions
#print axioms ThresholdHC.Tier3.allocation_payoff_saturated
#print axioms ThresholdHC.Tier3.allocation_strict_below_one
#print axioms ThresholdHC.Tier3.allocation_zero
#print axioms ThresholdHC.Tier3.arbitrary_law_cutoff
#print axioms ThresholdHC.Tier3.arbitrary_law_optimizer
#print axioms ThresholdHC.Tier3.codeAcceptance
#print axioms ThresholdHC.Tier3.codeLaw
#print axioms ThresholdHC.Tier3.conditionalInformation
#print axioms ThresholdHC.Tier3.continuousAt_testing_kl
#print axioms ThresholdHC.Tier3.cutoff_exists
#print axioms ThresholdHC.Tier3.cutoff_unique
#print axioms ThresholdHC.Tier3.examplePolicy
#print axioms ThresholdHC.Tier3.examplePolicy_prefix
#print axioms ThresholdHC.Tier3.examplePrefix
#print axioms ThresholdHC.Tier3.examplePrefix_hist_length
#print axioms ThresholdHC.Tier3.examplePrefix_snoc
#print axioms ThresholdHC.Tier3.examplePrefix_work
#print axioms ThresholdHC.Tier3.exampleProcessLaw
#print axioms ThresholdHC.Tier3.exampleProcessLaw_probability
#print axioms ThresholdHC.Tier3.exampleSeedLaw
#print axioms ThresholdHC.Tier3.exampleSeedLaw_probability
#print axioms ThresholdHC.Tier3.exampleTape
#print axioms ThresholdHC.Tier3.example_finite_expected_work
#print axioms ThresholdHC.Tier3.example_path_expect
#print axioms ThresholdHC.Tier3.example_policy_measurable
#print axioms ThresholdHC.Tier3.example_realizes
#print axioms ThresholdHC.Tier3.example_seed_work_integrable
#print axioms ThresholdHC.Tier3.example_totalWork
#print axioms ThresholdHC.Tier3.example_transcript_expect
#print axioms ThresholdHC.Tier3.example_unbounded_work
#print axioms ThresholdHC.Tier3.finiteHistory
#print axioms ThresholdHC.Tier3.finiteHistory_processPrefix
#print axioms ThresholdHC.Tier3.finite_work_stops
#print axioms ThresholdHC.Tier3.fullHist_snoc_example
#print axioms ThresholdHC.Tier3.histBefore_processPrefix_last
#print axioms ThresholdHC.Tier3.integrable_acceptance
#print axioms ThresholdHC.Tier3.integrable_acceptance_function
#print axioms ThresholdHC.Tier3.integrable_allocation
#print axioms ThresholdHC.Tier3.integrable_conditional_kl
#print axioms ThresholdHC.Tier3.integrable_conditional_work
#print axioms ThresholdHC.Tier3.integrable_feasible
#print axioms ThresholdHC.Tier3.integrable_finite_comp
#print axioms ThresholdHC.Tier3.integrable_indicator_inv
#print axioms ThresholdHC.Tier3.integrable_indicator_inv_sq
#print axioms ThresholdHC.Tier3.integrable_kl_term
#print axioms ThresholdHC.Tier3.integrable_policy_function
#print axioms ThresholdHC.Tier3.integrable_prefix_work
#print axioms ThresholdHC.Tier3.integrable_test_function
#print axioms ThresholdHC.Tier3.integrable_transcriptLaw
#print axioms ThresholdHC.Tier3.integral_log_sum
#print axioms ThresholdHC.Tier3.integral_support
#print axioms ThresholdHC.Tier3.integral_total_work_eq_iSup
#print axioms ThresholdHC.Tier3.measurableSet_acceptedBy
#print axioms ThresholdHC.Tier3.measurableSet_prefixAcceptance
#print axioms ThresholdHC.Tier3.measurable_allocation
#print axioms ThresholdHC.Tier3.measurable_policy
#print axioms ThresholdHC.Tier3.measurable_policyCode
#print axioms ThresholdHC.Tier3.measurable_prefix_function
#print axioms ThresholdHC.Tier3.measurable_processPrefix
#print axioms ThresholdHC.Tier3.measurable_testCode
#print axioms ThresholdHC.Tier3.measurable_totalProcessWork
#print axioms ThresholdHC.Tier3.objective_integrable
#print axioms ThresholdHC.Tier3.optimizer_above_cutoff
#print axioms ThresholdHC.Tier3.optimizer_below_cutoff
#print axioms ThresholdHC.Tier3.optimizer_formula
#print axioms ThresholdHC.Tier3.optimizer_saturation
#print axioms ThresholdHC.Tier3.pathProb_zero_of_invalid
#print axioms ThresholdHC.Tier3.policyCode
#print axioms ThresholdHC.Tier3.prefixAcceptanceSet
#print axioms ThresholdHC.Tier3.prefixAcceptance_mono
#print axioms ThresholdHC.Tier3.prefixAcceptance_subset_terminal
#print axioms ThresholdHC.Tier3.prefixAcceptance_tendsto
#print axioms ThresholdHC.Tier3.prefix_work_le_total
#print axioms ThresholdHC.Tier3.processHistory
#print axioms ThresholdHC.Tier3.processPrefix
#print axioms ThresholdHC.Tier3.processPrefix_snoc
#print axioms ThresholdHC.Tier3.process_work_mono
#print axioms ThresholdHC.Tier3.randomizedAcceptance
#print axioms ThresholdHC.Tier3.randomizedLaw
#print axioms ThresholdHC.Tier3.randomizedWork
#print axioms ThresholdHC.Tier3.randomized_information_bound
#print axioms ThresholdHC.Tier3.randomized_law_total
#print axioms ThresholdHC.Tier3.randomized_marginal_kl_bound
#print axioms ThresholdHC.Tier3.randomized_marginal_kl_le
#print axioms ThresholdHC.Tier3.randomized_test_data_processing
#print axioms ThresholdHC.Tier3.randomized_testing_bound
#print axioms ThresholdHC.Tier3.randomized_work_prior_comparison
#print axioms ThresholdHC.Tier3.rareObjective
#print axioms ThresholdHC.Tier3.realized_prefix_acceptance
#print axioms ThresholdHC.Tier3.realized_prefix_work_eq
#print axioms ThresholdHC.Tier3.realized_valid_step
#print axioms ThresholdHC.Tier3.sum_support
#print axioms ThresholdHC.Tier3.terminalAccept
#print axioms ThresholdHC.Tier3.terminalAccept_eq_iUnion
#print axioms ThresholdHC.Tier3.terminalFiniteTest
#print axioms ThresholdHC.Tier3.terminalFiniteTest_measurable
#print axioms ThresholdHC.Tier3.testCode
#print axioms ThresholdHC.Tier3.tier3_landmark
#print axioms ThresholdHC.Tier3.totalProcessWork
#print axioms ThresholdHC.Tier3.transcriptLaw_eq_codeLaw
#print axioms ThresholdHC.Tier3.transcriptLaw_le_of_prior_ratio
#print axioms ThresholdHC.Tier3.transcriptLaw_minus_le_plus
#print axioms ThresholdHC.Tier3.transcriptLaw_plus_le_minus
#print axioms ThresholdHC.Tier3.transcriptLaw_zero_of_invalid
#print axioms ThresholdHC.Tier3.unbounded_example
#print axioms ThresholdHC.Tier3.unbounded_stopping
#print axioms ThresholdHC.Tier3.unbounded_testing
#print axioms ThresholdHC.Tier3.workOf_le_length
#print axioms ThresholdHC.Tier3.workOf_nonneg
#print axioms ThresholdHC.Tier4.FinitePrefixKLStatement
#print axioms ThresholdHC.Tier4.InfiniteKLBoundStatement
#print axioms ThresholdHC.Tier4.InfiniteKLFiniteStatement
#print axioms ThresholdHC.Tier4.InfiniteKLSupremumStatement
#print axioms ThresholdHC.Tier4.ObservableKLBoundStatement
#print axioms ThresholdHC.Tier4.Tier4LandmarkStatement
#print axioms ThresholdHC.Tier4.absolutelyContinuous_of_restrict_exhaustion
#print axioms ThresholdHC.Tier4.finiteCodeRatio
#print axioms ThresholdHC.Tier4.finite_function_abs_bound
#print axioms ThresholdHC.Tier4.finite_prefix_kl_identity
#print axioms ThresholdHC.Tier4.infiniteKLBound_of_supremum
#print axioms ThresholdHC.Tier4.infiniteKLFinite_of_bound
#print axioms ThresholdHC.Tier4.infiniteTranscriptLaw
#print axioms ThresholdHC.Tier4.infiniteTranscriptLaw_map_prefix
#print axioms ThresholdHC.Tier4.infinite_kl_bound
#print axioms ThresholdHC.Tier4.infinite_kl_bound_extended
#print axioms ThresholdHC.Tier4.infinite_kl_eq_iSup
#print axioms ThresholdHC.Tier4.infinite_kl_finite
#print axioms ThresholdHC.Tier4.integral_prefixTranscriptLaw
#print axioms ThresholdHC.Tier4.jointPolicyCode
#print axioms ThresholdHC.Tier4.klDiv_eq_iSup_map_of_reconstruction
#print axioms ThresholdHC.Tier4.klDiv_eq_iSup_restrict
#print axioms ThresholdHC.Tier4.klDiv_finite_density
#print axioms ThresholdHC.Tier4.klDiv_le_of_restrict_exhaustion
#print axioms ThresholdHC.Tier4.klDiv_of_finite_likelihood
#print axioms ThresholdHC.Tier4.klDiv_restrict_eq_lintegral
#print axioms ThresholdHC.Tier4.klDiv_restrict_le
#print axioms ThresholdHC.Tier4.klDiv_restrict_le_map_of_reconstruct
#print axioms ThresholdHC.Tier4.measurableSet_reconstructed
#print axioms ThresholdHC.Tier4.measurableSet_stoppedFull
#print axioms ThresholdHC.Tier4.measurableSet_stoppedPrefix
#print axioms ThresholdHC.Tier4.measurable_infinite_observation
#print axioms ThresholdHC.Tier4.measurable_jointPolicyCode
#print axioms ThresholdHC.Tier4.measurable_jointPrefix
#print axioms ThresholdHC.Tier4.measurable_joint_prefix
#print axioms ThresholdHC.Tier4.measurable_padJoint
#print axioms ThresholdHC.Tier4.measurable_padPrefix
#print axioms ThresholdHC.Tier4.measurable_processTape
#print axioms ThresholdHC.Tier4.measure_eq_withDensity_of_setIntegral
#print axioms ThresholdHC.Tier4.observableKLBound_of_bound
#print axioms ThresholdHC.Tier4.observable_kl_bound
#print axioms ThresholdHC.Tier4.padJoint
#print axioms ThresholdHC.Tier4.padPrefix
#print axioms ThresholdHC.Tier4.padPrefix_eq_of_tail_none
#print axioms ThresholdHC.Tier4.prefixTranscriptLaw
#print axioms ThresholdHC.Tier4.processHistory_succ_of_none
#print axioms ThresholdHC.Tier4.realized_eventual_reconstruction
#print axioms ThresholdHC.Tier4.realized_stopped_cover
#print axioms ThresholdHC.Tier4.realized_stopped_reconstruction
#print axioms ThresholdHC.Tier4.restrict_eq_map_reconstruct
#print axioms ThresholdHC.Tier4.rnDeriv_restrict_both
#print axioms ThresholdHC.Tier4.stoppedFullSet
#print axioms ThresholdHC.Tier4.stoppedFullSet_mono
#print axioms ThresholdHC.Tier4.stoppedFullSet_prefix
#print axioms ThresholdHC.Tier4.stoppedPrefixSet
#print axioms ThresholdHC.Tier4.stopped_valid_reconstruction
#print axioms ThresholdHC.Tier4.stopped_valid_tail
#print axioms ThresholdHC.Tier4.tapeSymbolMeasurableSpace
#print axioms ThresholdHC.Tier4.tier4_landmark
#print axioms ThresholdHC.Uniform713.Arithmetic.error_prefactor_lt
#print axioms ThresholdHC.Uniform713.Arithmetic.fourth_root_three_lt
#print axioms ThresholdHC.Uniform713.Arithmetic.geometric_second_moment_factor_lt
#print axioms ThresholdHC.Uniform713.Arithmetic.product_of_moment_bounds
#print axioms ThresholdHC.Uniform713.Arithmetic.second_moment_scalar_lt
#print axioms ThresholdHC.Uniform713.Arithmetic.survival_coefficients
#print axioms ThresholdHC.Uniform713.Arithmetic.work_scalar_lt
#print axioms ThresholdHC.Uniform713.abs_mean_error_le
#print axioms ThresholdHC.Uniform713.bounded_centered_subgaussian
#print axioms ThresholdHC.Uniform713.cap_mono
#print axioms ThresholdHC.Uniform713.cap_pos
#print axioms ThresholdHC.Uniform713.cap_succ
#print axioms ThresholdHC.Uniform713.cap_zero
#print axioms ThresholdHC.Uniform713.classifier_increment_sq_le_one
#print axioms ThresholdHC.Uniform713.conditional_bounds
#print axioms ThresholdHC.Uniform713.coupledLevelWork_eq_levelWork
#print axioms ThresholdHC.Uniform713.coupled_work_eq
#print axioms ThresholdHC.Uniform713.decision_square_integral_le_one
#print axioms ThresholdHC.Uniform713.decision_zero_or_one
#print axioms ThresholdHC.Uniform713.deterministic_positive_model
#print axioms ThresholdHC.Uniform713.dyadic_survival_identity
#print axioms ThresholdHC.Uniform713.early_error_term
#print axioms ThresholdHC.Uniform713.errorUnionBound_le
#print axioms ThresholdHC.Uniform713.error_le_one
#print axioms ThresholdHC.Uniform713.error_negative_bound
#print axioms ThresholdHC.Uniform713.error_negative_union
#print axioms ThresholdHC.Uniform713.error_pair_bound
#print axioms ThresholdHC.Uniform713.error_positive_bound
#print axioms ThresholdHC.Uniform713.error_positive_union
#print axioms ThresholdHC.Uniform713.estimator_memLp
#print axioms ThresholdHC.Uniform713.estimator_second_moment
#print axioms ThresholdHC.Uniform713.estimator_unbiased
#print axioms ThresholdHC.Uniform713.exp_cap_error
#print axioms ThresholdHC.Uniform713.expected_work_le_cap
#print axioms ThresholdHC.Uniform713.expected_work_negative_bound
#print axioms ThresholdHC.Uniform713.expected_work_positive_bound
#print axioms ThresholdHC.Uniform713.expected_work_survival_bound
#print axioms ThresholdHC.Uniform713.expected_work_survival_identity
#print axioms ThresholdHC.Uniform713.finite_dyadic_indicator_sum
#print axioms ThresholdHC.Uniform713.finite_dyadic_scaled_indicator_sum
#print axioms ThresholdHC.Uniform713.finite_dyadic_sum_v1
#print axioms ThresholdHC.Uniform713.finite_dyadic_sum_v2
#print axioms ThresholdHC.Uniform713.finite_work_survival_bound
#print axioms ThresholdHC.Uniform713.firstDecision_zero_or_one
#print axioms ThresholdHC.Uniform713.firstStop_eq_iff
#print axioms ThresholdHC.Uniform713.firstStop_le
#print axioms ThresholdHC.Uniform713.firstStop_le_of_cross
#print axioms ThresholdHC.Uniform713.firstStop_min
#print axioms ThresholdHC.Uniform713.firstStop_mono
#print axioms ThresholdHC.Uniform713.firstStop_spec
#print axioms ThresholdHC.Uniform713.full_bound_713
#print axioms ThresholdHC.Uniform713.hasMeanTails_of_independent_bounded
#print axioms ThresholdHC.Uniform713.hasSum_levelProb
#print axioms ThresholdHC.Uniform713.increment_secondMoment_envelope
#print axioms ThresholdHC.Uniform713.increment_secondMoment_negative
#print axioms ThresholdHC.Uniform713.increment_secondMoment_positive
#print axioms ThresholdHC.Uniform713.integrable_binary
#print axioms ThresholdHC.Uniform713.integrable_classifier_increment
#print axioms ThresholdHC.Uniform713.integrable_classifier_increment_sq
#print axioms ThresholdHC.Uniform713.integrable_decision
#print axioms ThresholdHC.Uniform713.integrable_increment
#print axioms ThresholdHC.Uniform713.integrable_levelMeasure_iff
#print axioms ThresholdHC.Uniform713.integrable_sampled
#print axioms ThresholdHC.Uniform713.integrable_work
#print axioms ThresholdHC.Uniform713.integral_binary_error
#print axioms ThresholdHC.Uniform713.integral_estimator
#print axioms ThresholdHC.Uniform713.integral_levelMeasure
#print axioms ThresholdHC.Uniform713.integral_sampled
#print axioms ThresholdHC.Uniform713.integrate_conditional_bound
#print axioms ThresholdHC.Uniform713.integrate_conditional_inverse_gap
#print axioms ThresholdHC.Uniform713.integrate_conditional_inverse_gap_strict
#print axioms ThresholdHC.Uniform713.integrate_conditional_strict_bound
#print axioms ThresholdHC.Uniform713.levelMeasure_probability
#print axioms ThresholdHC.Uniform713.levelMeasure_real_singleton
#print axioms ThresholdHC.Uniform713.levelMeasure_singleton
#print axioms ThresholdHC.Uniform713.levelProb_pos
#print axioms ThresholdHC.Uniform713.levelWork_succ_eq_max
#print axioms ThresholdHC.Uniform713.levelWork_zero
#print axioms ThresholdHC.Uniform713.measurable_classifier_increment
#print axioms ThresholdHC.Uniform713.measurable_decision
#print axioms ThresholdHC.Uniform713.measurable_estimator
#print axioms ThresholdHC.Uniform713.measurable_firstStop
#print axioms ThresholdHC.Uniform713.measurable_increment
#print axioms ThresholdHC.Uniform713.measurable_prefixMean
#print axioms ThresholdHC.Uniform713.measurable_sampled
#print axioms ThresholdHC.Uniform713.measurable_stopLevel
#print axioms ThresholdHC.Uniform713.measurable_work
#print axioms ThresholdHC.Uniform713.prefixMean_subgaussian
#print axioms ThresholdHC.Uniform713.rLevel_lt_one
#print axioms ThresholdHC.Uniform713.rLevel_pos
#print axioms ThresholdHC.Uniform713.samplingKernel_apply
#print axioms ThresholdHC.Uniform713.samplingKernel_markov
#print axioms ThresholdHC.Uniform713.samplingMeasure_indep
#print axioms ThresholdHC.Uniform713.samplingMeasure_probability
#print axioms ThresholdHC.Uniform713.secondMomentSeries_bound
#print axioms ThresholdHC.Uniform713.squared_decision_difference_integral
#print axioms ThresholdHC.Uniform713.squared_decision_difference_le_errors
#print axioms ThresholdHC.Uniform713.squared_decision_difference_le_one
#print axioms ThresholdHC.Uniform713.stopLevel_le
#print axioms ThresholdHC.Uniform713.stopLevel_mono
#print axioms ThresholdHC.Uniform713.sum_cap_range
#print axioms ThresholdHC.Uniform713.sum_increment
#print axioms ThresholdHC.Uniform713.sum_secondMomentEnvelope_lt
#print axioms ThresholdHC.Uniform713.sum_weightedWorkEnvelope_lt
#print axioms ThresholdHC.Uniform713.summable_mean_increments
#print axioms ThresholdHC.Uniform713.summable_secondMomentEnvelope
#print axioms ThresholdHC.Uniform713.summable_weightedWorkEnvelope
#print axioms ThresholdHC.Uniform713.survival_indicator_scale_step
#print axioms ThresholdHC.Uniform713.survival_probability_negative
#print axioms ThresholdHC.Uniform713.survival_probability_positive
#print axioms ThresholdHC.Uniform713.tendsto_dyadic_error_zero
#print axioms ThresholdHC.Uniform713.tendsto_errorEnvelope_zero
#print axioms ThresholdHC.Uniform713.tendsto_error_probability
#print axioms ThresholdHC.Uniform713.tendsto_mean_of_binary_error
#print axioms ThresholdHC.Uniform713.tendsto_of_error_envelope
#print axioms ThresholdHC.Uniform713.threshold_mono_cap
#print axioms ThresholdHC.Uniform713.threshold_nonneg
#print axioms ThresholdHC.Uniform713.threshold_sq
#print axioms ThresholdHC.Uniform713.tsum_secondMomentEnvelope_lt
#print axioms ThresholdHC.Uniform713.tsum_weightedWorkEnvelope_lt
#print axioms ThresholdHC.Uniform713.uniformWork_eq_coupled
#print axioms ThresholdHC.Uniform713.variance_work_lt_713
#print axioms ThresholdHC.Uniform713.workSeries_bound
#print axioms ThresholdHC.Uniform713.work_bound_of_survival
#print axioms ThresholdHC.Uniform713.work_le_cap
#print axioms ThresholdHC.Uniform713.work_mono
#print axioms ThresholdHC.Uniform713.work_pos
#print axioms ThresholdHC.Uniform713.work_survival_identity
#print axioms ThresholdHC.Uniform713.wrong_negative_stop
#print axioms ThresholdHC.Uniform713.wrong_positive_stop
