"""Check critical base cost, statistical transfer and minimax lower bound.

This audit covers the critical lower theorem. The original distribution-blind
upper and matching critical upper have separate audits in
tools/verify_blind_upper_components.py and tools/verify_critical_upper_components.py.

This extension does not change existing frozen targets or scores. It reuses the
frozen Tier 6 source and transitive-axiom guards. Specifications were introduced
with these proofs, not retrospectively described as a pre-proof freeze.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, IMPORT, project_dependencies, sha, strip_comments,
    validate_reports, imports as source_imports,
)

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
SOURCE = LEAN / "ThresholdHC/CriticalEntropy"
MODULES = ("Packing", "CommonPoint", "BernoulliPrefix", "EventInformation", "SignTest",
           "EarlyDecision", "StoppingWindow", "GeometricOverlap", "FiniteGap",
           "StoppedModel", "StoppedTape", "SequentialModel", "RestartPair",
           "RepeatedModel", "RepeatedRestart", "RepeatedSignModel", "SampleMean",
           "SignReduction", "EstimationEntropy", "PopulationModel", "UniformCoin",
           "PopulationMixture", "PopulationVariance", "GoodGapModel", "ConditionalMoments",
           "HalfPrior", "GapSelection", "GoodGaps", "CriticalModel", "CriticalLaw",
           "CriticalAnnuli", "CriticalScale", "ActivationModel", "Activation", "ActivationCost",
           "ScaleAsymptotics", "BaseCost",
           "ObservationModel", "FiniteObservation", "CappedObservation", "FiniteSufficiency",
           "LikelihoodBounds", "HellingerModel", "Hellinger", "ObservationInformation",
           "PopulationGeometryModel", "PopulationCompactness", "FiniteGeometryModel", "FiniteGeometry",
           "ObservationGeometryModel", "LikelihoodAffine", "ObservationAffine", "HellingerGeometry", "CriticalGeometry",
           "FiniteRiskModel", "FiniteRiskAnalytic", "StatisticProcedure", "SymmetricReduction",
           "FiniteSaddle", "ExponentialRisk", "FiniteCentering", "FiniteRMS",
           "FiniteSupport", "ObservationRisk", "CriticalRisk",
           "PolicyNormalization", "SelectedPolicy", "CapInvariance", "SeedAdaptation", "PolicyMixture", "CriticalCommonPair",
           "FiniteAffinity", "MidpointWork", "LocalSimulation", "FinitePopulation", "PopulationTapeLaw", "PopulationLocalWork", "PopulationTransfer", "CriticalPopulationFinite",
           "SeedAffinity", "CreationPopulation", "PopulationWorkLaw", "CriticalCreation", "ObservablePopulation", "SeededPopulationTransfer", "CriticalExperiment", "EventualAffinity", "CriticalTermination", "CriticalTerminalAffinity", "AffinityTesting", "CriticalRareModel", "CriticalAlgorithmLower", "CriticalRate", "CriticalMinimax", "Specification")
NAMESPACE = "ThresholdHC.CriticalEntropy."
ROOTS = {
    NAMESPACE + name for name in (
        "sum_event_mass_le_overlap", "event_packing", "overlap_bound",
        "entropy_of_packing", "entropy_of_gap_count", "finite_common_point",
        "common_point_of_finite_mixtures", "EntropyPackingStatement", "CommonPointStatement",
        "streamProb_pos", "stream_kl_identity", "finiteMeasure_positive", "finiteMeasure_density",
        "seeded_prefix_kl", "binary_kl_le_chisq", "seeded_prefix_kl_le_chisq",
        "seeded_tape_prefix_map", "prefix_observable_kl_le", "binary_kl_lower_log",
        "event_binary_kl_le", "event_mass_lower_of_kl", "prefix_event_mass_lower",
        "fair_prefix_event_mass_lower", "PrefixInformationStatement", "PrefixEventTransferStatement",
        "SignTest", "signTestWork", "expectedSignTestWork", "signTestWindow",
        "measurable_signTestWork", "measurable_signTestWindow", "signTest_prefix_probability",
        "signTest_terminates", "signTest_late_probability", "signTest_window_probability",
        "binary_kl_separation", "early_event_probability", "EntropyGap", "signParameter",
        "signParameter_interior", "early_prefix_information", "signTest_early_minus",
        "entropyLowerTime", "entropyUpperTime", "entropyLowerTime_bounds", "entropyUpperTime_bounds",
        "signTest_quarter_late", "signTest_negative_window", "restrictPrefix", "signTestWindowPrefix",
        "measurable_signTestWindowPrefix", "signTestWindowPrefix_preimage", "signTestWindowPrefix_probability",
        "signTestWindow_positive_imp_lt", "signTest_fair_window", "signTest_window_scale",
        "geometric_separation_of_adjacent", "half_low_cost", "geometric_interval_card",
        "inverse_gap_scales_separated", "signTest_window_overlap", "finite_gap_sign_entropy",
        "FiniteGapSignEntropyStatement",
        "tapeDrop", "measurable_tapeDrop", "StoppedProcedure", "stoppedSuffix",
        "measurable_stoppedSuffix", "stoppedProcedureWork", "expectedStoppedProcedureWork",
        "measurable_stoppedProcedureWork", "stoppedWithWork", "tapeDrop_map",
        "prefix_drop_independent", "tape_split_map", "seeded_tape_split_map",
        "measure_eq_tsum_stopping", "seeded_prefix_drop_probability",
        "stopped_event_tail_probability", "stopped_output_suffix_probability",
        "stopped_output_suffix_map", "stopped_procedure_terminates", "stopped_marked_suffix_map",
        "StoppedSuffixStatement",
        "completePrefix", "measurable_completePrefix", "tapePrefix_completePrefix",
        "prefix_eq_restrict", "prefix_eq_drop", "stopped_prefix_ext", "restartInput",
        "measurable_restartInput", "sequentialStop", "sequentialOutput",
        "measurable_sequentialStop", "measurable_sequentialOutput", "sequential_prefix_ext",
        "sequentialProcedure", "prod_swap_middle", "seeded_stopped_suffix_map",
        "two_run_marked_map", "two_run_expected_work", "sequential_expected_work",
        "sequential_output_map", "SequentialRestartStatement",
        "reseedProcedure", "postprocessProcedure", "emptyProcedure", "measurable_finCons",
        "repeatedProcedure", "fin_seed_split_map", "reseed_expected_work",
        "repeated_expected_work", "reseed_output_map", "fin_product_cons_map",
        "repeated_output_map", "RepeatedRestartStatement",
        "stopped_before_prefix_ext", "stoppedToSignTest", "repeatedSignDecision",
        "measurable_repeatedSignDecision", "repeatedSignTest", "iid_sum_memLp",
        "iid_sum_integral", "iid_sum_variance", "iid_sum_deviation", "iid_sum_lower_error",
        "iid_sum_upper_error", "repeated_sign_work", "repeated_sign_plus_error",
        "repeated_sign_minus_error", "finite_gap_estimation_entropy", "critical_restart_count_bounds",
        "RepeatedSignTestStatement", "FiniteGapEstimationEntropyStatement",
        "uniformUnitMeasure", "uniformUnitMeasure_probability", "uniformCoinFlip",
        "measurable_uniformCoinFlip", "uniformTapeMeasure", "uniformTapeMeasure_probability",
        "uniformCoinTape", "measurable_uniformCoinTape", "uniformProcedureState",
        "measurable_uniformProcedureState", "conditionalSecondMoment", "conditionalMean",
        "mixtureParameter", "measurable_mixtureParameter", "populationInput",
        "measurable_populationInput", "populationMeasure", "populationSecondMoment",
        "populationExpectedWork", "populationMean", "uniformCoinFlip_true", "uniformCoinFlip_map",
        "uniformCoinTape_map", "seeded_uniformCoinTape_map", "conditionalSecondMoment_uniform",
        "conditionalMean_uniform", "conditionalWork_uniform", "measurable_conditionalSecondMoment",
        "measurable_conditionalMean", "measurable_conditionalWork", "conditionalSecondMoment_finite_iff",
        "conditionalMean_output_law", "conditionalSecondMoment_output_law", "seeded_lintegral_uniform",
        "measurable_seeded_lintegral", "measurable_seeded_integral", "conditionalMean_integrable_of_moment",
        "mixtureParameter_map", "lintegral_bernoulli_parameter", "mixtureParameter_lintegral",
        "population_lintegral", "population_lintegral_const", "population_finite_components",
        "population_ae_finite_components", "mixtureParameter_integral", "population_integral",
        "population_finite_all", "population_conditional_finiteness", "population_second_moment_formula",
        "population_work_formula", "population_mean_formula", "population_finiteness_transfer",
        "PopulationMomentStatement", "PopulationFinitenessStatement",
        "population_memLp_of_moment", "population_second_moment_toReal", "variance_lower_of_mixture",
        "population_second_moment_const", "population_mean_const", "population_variance_mixture_lower",
        "population_variance_floor", "conditionalMean_sq_le_moment", "population_moment_bound_of_variance",
        "population_moment_finite_of_evariance", "population_evariance_floor",
        "population_moment_bound_of_evariance", "CappedPrior", "halfPrior", "CappedPopulationGuarantee",
        "PopulationGoodGap", "conditional_moment_pair_integrable", "population_second_moment_real_formula",
        "measurable_halfPrior", "halfPrior_le_half", "halfPrior_integral", "cappedPrior_const",
        "cappedPrior_half", "halfPrior_weighted_integral", "population_halfPrior_moment", "population_halfPrior_mean",
        "exists_subset_real_measure", "bad_set_mass_lt_of_integral_lower", "bad_set_mass_lt_of_integral_upper",
        "population_good_gaps", "PopulationVarianceFloorStatement", "PopulationMomentFromVarianceStatement",
        "PopulationGoodGapsStatement",
        "criticalGapLaw", "criticalUpper", "criticalAnnulus",
        "criticalParameter", "criticalGapLaw_noAtoms", "linear_density_interval",
        "criticalGapLaw_Ioc", "criticalGapLaw_supported", "criticalGapLaw_probability",
        "criticalGapLaw_real_Ioc", "criticalUpper_pos", "criticalUpper_le_quarter",
        "criticalUpper_succ", "criticalAnnulus_mass", "criticalAnnulus_adjacent",
        "criticalUpper_antitone", "criticalAnnulus_disjoint", "measurable_criticalParameter",
        "criticalParameter_eq_sign", "criticalParameter_coe_of_mem", "exists_good_point_low_work",
        "criticalAnnulus_work_factor", "critical_annulus_work_sum", "critical_annulus_good_points",
        "population_negative_work_integral", "critical_scale_entropy", "critical_scale_product",
        "CriticalLawStatement", "CriticalScaleProductStatement",
        "activeSeeds", "measurableSet_activeSeeds", "stop_zero_iff_inactive",
        "inactive_output", "inactive_work", "active_work_lower",
        "activation_work_restrict", "activation_conditional_work", "activation_probability_le_work",
        "activation_conditional_work_lower", "normalized_event_mean", "normalized_event_moment",
        "populationSeedEvent", "measurableSet_populationSeedEvent", "populationSeedEvent_measure",
        "populationMeasure_restrict_seed", "populationMeasure_smul_seed", "populationMeasure_condition_seed",
        "population_inactive_mean", "activeProcedure", "population_activation_mean",
        "population_activation_work", "activation_positive_of_bias", "population_activation_moment",
        "active_population_guarantee", "capped_guarantee_moment_floor", "population_null_work_ge_activation",
        "activation_product_bounds", "critical_product_scale", "entropy_scale_count",
        "critical_annulus_mass_of_small_product", "entropy_logs_le_exp", "criticalLogFactor",
        "critical_scalar_base_cost", "critical_raw_base_cost", "critical_base_cost",
        "ActivationNormalizationStatement", "CriticalRawBaseCostStatement", "CriticalBaseCostStatement",
        "wordHeads", "stoppedSeedCell", "wordLikelihood",
        "populationWordLikelihood", "CappedWord", "cappedWord_fintype",
        "cappedWord_measurableSpace", "cappedWord_measurableSingleton", "cappedTranscript",
        "cappedTranscriptLaw", "stoppedReference", "stoppedStatistic",
        "cappedStatisticLaw", "transcriptReconstruction", "streamProb_heads",
        "measurableSet_stoppedSeedCell", "stopped_word_probability", "population_event_probability",
        "measurable_wordLikelihood", "population_stopped_word_probability", "population_stopped_heads_probability",
        "measurable_cappedTranscript", "cappedTranscript_of_stop", "cappedTranscript_mem_cell",
        "cappedTranscriptLaw_cell", "stoppedReference_cell", "measure_ext_prod_finite",
        "stoppedReference_finite", "cappedTranscriptLaw_density", "cappedTranscriptLaw_probability",
        "map_factored_density", "factored_density_restrict", "factored_density_fiber_mass",
        "factored_density_cond", "cappedStatisticLaw_density", "wordLikelihood_le_one",
        "wordLikelihood_pos", "prior_weights_sum", "populationWordLikelihood_le_one",
        "populationWordLikelihood_pos", "critical_parameters_interior", "hellingerAffinity",
        "finiteAffinity", "affinity_density_scaling", "hellingerAffinity_withDensity",
        "affinity_mass_scaling", "hellingerAffinity_finite_density", "cappedStatisticLaw_probability",
        "cappedStatisticLaw_zero_iff_reference", "hellingerAffinity_factored_statistic", "capped_observation_reconstruction",
        "capped_observation_affinity", "capped_observation_finite_affinity", "capped_transcript_work",
        "capped_observation_work", "critical_observation_reconstruction", "critical_observation_finite_affinity",
        "critical_observation_work", "CriticalObservationReconstructionStatement", "CriticalObservationAffinityStatement",
        "CriticalObservationWorkStatement",
        "PopulationDual", "populationDualSet", "populationDualDensity",
        "populationDualPrior", "populationMomentMap", "boundedPriorMomentSet",
        "populationTarget", "populationPairSet", "populationDualSet_compact",
        "populationDualSet_nonempty", "populationDualSet_convex", "populationDualDensity_test",
        "populationDualDensity_setIntegral", "populationDualDensity_bounds", "populationDualPrior_measurable",
        "populationDualPrior_le_half", "populationDualPrior_ae", "populationDualPrior_mass",
        "populationDualPrior_admissible", "populationDualSet_covers_priors", "populationDualPrior_test",
        "populationMomentMap_apply", "populationMomentMap_continuous", "populationMomentImage_compact_convex",
        "boundedPriorMomentSet_eq_image", "boundedPriorMomentSet_compact_convex", "populationPairSet_compact_convex",
        "populationPairSet_nonempty", "realFiniteAffinity", "sqrt_product_scale",
        "sqrt_product_mix", "realFiniteAffinity_continuous", "realFiniteAffinity_concave",
        "realFiniteAffinity_le_one", "realFiniteDistance_convex", "finiteAffinity_toReal",
        "cappedObservationVector", "cappedObservationImage", "wordLikelihood_real_bounds",
        "wordLikelihood_real_memLp", "populationWordLikelihood_real", "populationWordLikelihood_affine_moment",
        "cappedStatisticLaw_real_mass", "cappedStatisticLaw_affine_moment", "cappedObservationVector_affine_coordinates",
        "cappedObservationVector_congr_ae", "capped_observation_affine_representation", "capped_observation_image_compact_convex",
        "capped_observation_image_nonempty", "capped_observation_image_positive", "capped_observation_uniform_positive",
        "capped_statistic_probabilities", "capped_observation_affinity_real", "capped_observation_hellinger_geometry",
        "capped_observation_affinity_le_one", "critical_population_representation", "critical_observation_geometry",
        "populationPairSet_realization", "critical_pair_hellinger_geometry", "CriticalPopulationRepresentationStatement",
        "CriticalObservationGeometryStatement", "CriticalPairGeometryStatement",
        "finitePartition", "finitePartitionLinear", "finiteRepeatedObjective",
        "finitePartition_pos", "realFiniteAffinity_pos", "affinity_le_tilted_partition",
        "finite_log_partition_lower", "finite_log_partition_attained", "finitePartition_shift",
        "finitePartition_convex", "finiteLogPartition_convex", "positiveVectors_convex",
        "finiteLogPartition_population_concave", "finitePartition_continuous", "finiteLogPartition_continuousOn",
        "finitePerspective_convex", "convex_concave_uniform_strict", "exists_positive_scale_lt",
        "finiteRepeatedObjective_pointwise", "finiteRepeatedObjective_convex", "cappedStatisticProcedure",
        "cappedStatisticProcedure_work", "cappedStatisticProcedure_output_law", "cappedStatisticProcedure_memLp",
        "population_capped_work_le", "iid_score_memLp", "iid_score_integral",
        "iid_score_variance", "symmetric_one_run_reduction", "finiteRepeatedObjective_population_geometry",
        "finiteRepeatedObjective_score_continuous", "finite_repeated_uniform_saddle", "square_le_shifted_exponentials",
        "second_moment_of_exponential_bounds", "realFiniteAffinity_self", "finiteRepeatedObjective_diagonal",
        "finite_saddle_centering", "finite_function_memLp", "finite_function_integrable",
        "finite_integral_exp", "finite_iid_exponential", "radius_second_moment_le",
        "finite_iid_risk_of_log_bounds", "finite_convex_rms_comparison", "finiteSupportRetraction",
        "finiteSupportRetraction_val", "finite_support_sum", "finite_support_map_mass",
        "finite_support_affinity", "evariance_map_measurable", "finite_convex_one_run",
        "capped_observation_one_run", "critical_capped_estimator", "critical_capped_affinity_obstruction",
        "critical_capped_policy_pair", "CriticalCappedEstimatorStatement", "CriticalCappedAffinityObstructionStatement",
        "CriticalCappedPolicyPairStatement",
        "affinity_power_controls_distance", "critical_repeat_choice", "compact_power_pair_bound",
        "populationPairSet_covers_priors", "capped_observation_affinity_real_congr", "capped_observation_affinity_real_symm",
        "criticalLogFactor_pos", "critical_capped_constraint_feasible", "measurable_selected",
        "selectedProcedure", "selectedProcedure_capped", "selected_seed_lintegral",
        "selected_expected_work", "population_selected_lintegral", "selected_population_work",
        "capped_statistic_lintegral", "selected_statistic_lintegral", "selected_statistic_mass",
        "selected_statistic_real_mass", "real_affinity_common_density_mixture", "selected_affinity_real",
        "population_seed_map", "population_reseed_lintegral", "population_reseed_work",
        "reseed_statistic_lintegral", "statisticCapEmbedding", "statisticCapEmbedding_injective",
        "stoppedStatistic_enlarge_cap", "cappedStatisticLaw_enlarge_cap", "realFiniteAffinity_map_injective",
        "capped_affinity_enlarge_cap", "reseed_statistic_law", "reseed_affinity_real",
        "finiteWeightMeasure", "finiteWeightMeasure_singleton", "finiteWeightMeasure_probability",
        "finiteWeightMeasure_real_singleton", "selected_population_work_real", "CappedPolicy",
        "cappedPolicyOfProcedure", "policyAffinity", "policyNullWork",
        "cappedPolicyOfProcedure_affinity", "cappedPolicyOfProcedure_nullWork", "capped_policy_mixture",
        "critical_common_capped_pair", "CriticalCappedConstraintStatement", "CriticalCommonCappedPairStatement",
        "hellingerAffinity_finite", "lintegral_sqrt_product_le", "hellingerAffinity_map_finite",
        "hellingerAffinity_probability_le_one", "finiteWeightMeasure_finite", "finiteWeightMeasure_affinity",
        "hellingerAffinity_withDensity_nonnegative", "hellingerAffinity_revealed_finite", "cappedOutput",
        "measurable_cappedOutput", "cappedOutput_cappedTranscript", "cappedOutput_map",
        "cappedOutput_affinity", "midpointPrior", "measurable_midpointPrior",
        "unitInterval_integrable", "midpointPrior_integral", "cappedPrior_midpoint",
        "unitInterval_memLp", "populationWordLikelihood_real_midpoint", "null_work_le_twice_population_work",
        "localSimulation", "localSimulation_count_le", "localSimulation_prefix_ext",
        "measurable_localSimulation", "localSimulationProcedure", "localSimulationProcedure_capped",
        "populationSimulation", "localSimulation_eq_population", "populationSimulation_total_work",
        "localSimulation_total_work", "finitePopulationWeight", "finite_population_factor",
        "finite_population_total", "populationCoinMass", "coinLike_le_one",
        "continuous_coinLike", "population_coin_integrand_bounds", "population_coin_integrable",
        "populationCoinMass_midpoint", "product_defect_le_sum", "sqrt_product_common_factor",
        "sqrt_product_le_midpoint", "finite_midpoint_hybrid_decomposition", "finite_weighted_midpoint_hybrid_decomposition",
        "finite_population_hybrid_decomposition", "tape_head_drop_preserving", "array_head_drop_preserving",
        "histBefore_cons_zero", "histBefore_cons_succ", "pathProb_cons",
        "pathProb_initial_stop", "sum_cons_word", "measurable_populationSimulation_word",
        "bernoulli_singleton_ofReal", "populationSimulation_lintegral", "populationSimulation_word_law",
        "measurable_uniformTapeArray", "parameterTapeLaw", "parameterTapeLaw_probability",
        "parameterTapeLaw_array_map", "fixed_parameter_uniform_array_lintegral", "parameterTapeLaw_population_lintegral",
        "measurable_pathProb_parameters", "pathProb_parameters_bounds", "integrable_pathProb_parameters",
        "parameterTapeLaw_population_word_law", "parameter_pathProb_factor", "populationParameterLaw",
        "populationParameterLaw_probability", "populationParameterLaw_integral", "population_tape_word_law",
        "populationInput_preserving", "populationInput_output_law", "populationInput_work",
        "populationInput_capped_law", "array_replace_preserving", "measurable_populationSimulation_count",
        "localSimulation_word_law", "localSimulation_work", "population_localSimulation_total_work",
        "population_localSimulation_word_law", "localSimulation_affinity_le", "finitePopulationExpectedWork",
        "population_localSimulation_total_work_real", "finite_population_transfer", "finitePopulationWeight_gap_congr",
        "criticalClippedGap", "measurable_criticalClippedGap", "criticalClippedGap_bounds",
        "criticalClippedGap_ae", "critical_common_finite_population_pair", "PopulationTapeLawStatement",
        "PopulationLocalWorkStatement", "CriticalFinitePopulationPairStatement",
        "finite_kernel_density",
        "finite_kernel_hellinger_identity",
        "finite_kernel_hellinger_bound",
        "finite_kernel_marginal",
        "creationPopulationWeight",
        "creationPopulationWeight_eq_finite",
        "measurable_creationPopulationWeight",
        "creationPopulationWeight_total",
        "finitePopulation_work_law",
        "finitePopulation_work_real",
        "criticalClipped_parameters",
        "critical_common_creation_prefix_pair",
        "observable_population_prefix_kernel",
        "observable_population_hellinger_bound",
        "criticalExperimentLaw",
        "criticalExperimentLaw_probability",
        "criticalPrefixLaw",
        "criticalExpectedWork",
        "criticalExperimentLaw_realizes",
        "critical_common_experiment_prefix_pair",
        "map_singleton_real_tendsto",
        "hellingerAffinity_finite_real",
        "hellingerAffinity_tendsto_eventual_maps",
        "hellingerAffinity_lower_of_eventual_maps",
        "critical_tape_measurable",
        "critical_prefix_work_le_total",
        "critical_experiment_stops",
        "critical_eventual_tape_reconstruction",
        "criticalObservationLaw",
        "criticalPrefixLaw_probability",
        "critical_terminal_affinity_bound",
        "thresholdDecision",
        "measurable_thresholdDecision",
        "risk_event_markov",
        "bool_affinity_le_half_of_errors",
        "two_point_risk_lower_of_decision_affinity",
        "CriticalRarePrior",
        "CriticalUniformBudget",
        "criticalMaximalRMSRisk",
        "criticalMinimaxRisk",
        "critical_common_terminal_pair",
        "critical_rms_pair_lower",
        "critical_algorithm_lower_at_separation",
        "critical_rate_separation",
        "critical_algorithm_lower_bound",
        "critical_minimax_lower_bound",
        "criticalZeroEstimator",
        "criticalZeroEstimator_work",
        "critical_budget_class_nonempty",
        "criticalZeroEstimator_risk",
        "critical_minimax_le_rarity",
        "SeedKernelDensityStatement",
        "CriticalExperimentPrefixPairStatement",
        "CriticalEndpointStoppingStatement",
        "CriticalEventualReconstructionStatement",
        "CriticalTerminalPairStatement",
        "CriticalAlgorithmLowerStatement",
        "CriticalMinimaxLowerStatement",
        "CriticalBudgetNonemptyStatement",
        "CriticalTrivialUpperStatement",
    )
}
# Every specification statement must be type-checked by an Audit.lean example.
EXACT_TARGETS = {root.removeprefix(NAMESPACE) for root in ROOTS if root.endswith("Statement")}
# Checkpoints certified together by the exact targets and the axiom audit.
FLAGS = (
    "base_cost_theorem_verified",
    "capped_observation_reduction_verified",
    "population_observation_geometry_verified",
    "capped_policy_risk_and_pair_verified",
    "common_capped_pair_verified",
    "finite_horizon_population_transfer_verified",
    "unrestricted_population_transfer_verified",
    "endpoint_termination_limit_verified",
    "critical_minimax_lower_bound_verified",
    "finite_gap_sign_testing_theorem_verified",
    "stopped_suffix_independence_verified",
    "sequential_restart_law_and_work_verified",
    "finite_repetition_iid_and_work_verified",
    "repeated_sign_error_and_work_verified",
    "finite_gap_estimation_entropy_verified",
    "population_moment_disintegration_verified",
    "population_conditional_finiteness_verified",
    "population_extended_variance_floor_verified",
    "population_moment_from_variance_verified",
    "population_good_gap_selection_verified",
    "critical_gap_law_verified",
    "critical_scale_null_cost_product_verified",
    "activation_normalization_verified",
    "critical_raw_base_cost_verified",
)


def exact_targets(audit: str) -> set[str]:
    """Return the statements that Audit.lean type-checks, requiring each exactly once."""
    checked = re.findall(r"^example\s*:\s*([A-Za-z_][\w']*)\s*:=", audit, re.M)
    if len(checked) != len(set(checked)) or set(checked) != EXACT_TARGETS:
        raise ValueError("Audit.lean must type-check every specification statement once")
    return set(checked)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--sequential", action="store_true")
    args = parser.parse_args()
    output = args.output_dir or ROOT / ".runtime/critical-components" / datetime.now(
        timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    sources = sorted(SOURCE.glob("*.lean"))
    expected_sources = {name + ".lean" for name in (*MODULES, "Audit")}
    if {p.name for p in sources} != expected_sources:
        raise ValueError("Unexpected or missing component module")
    declared = []
    texts = {}
    for path in sources:
        source = strip_comments(path.read_text(encoding="utf-8"))
        texts[path.stem] = source
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        imports = source_imports(source)
        allowed_imports = {
            "Mathlib", "Mathlib.MeasureTheory.Integral.Prod",
            "Mathlib.InformationTheory.KullbackLeibler.DataProcessing",
            "Mathlib.Analysis.SpecialFunctions.BinaryEntropy",
            "ThresholdHC.Proofs.Tier2.ClassifierProbability",
            "ThresholdHC.Proofs.Tier2.TranscriptLikelihood",
            "ThresholdHC.Tier4.FiniteDensity", "ThresholdHC.Tier6.TestingFinite",
            "ThresholdHC.Tier5.FiniteEnvironment",
            "ThresholdHC.Tier3.StoppingBase",
            "ThresholdHC.Tier5.FiniteJoint",
            "ThresholdHC.Tier5.FiniteCreation",
            "ThresholdHC.Tier5.StoppingBase",
            "ThresholdHC.Tier6.AlgorithmCore",
            "ThresholdHC.Tier6.Process",
        } | {NAMESPACE + name for name in MODULES}
        if any(module not in allowed_imports for module in imports):
            raise ValueError("Unregistered component import in " + path.name)
        declared.extend(NAMESPACE + name for name in DECLARATION.findall(source))
    if len(declared) != len(ROOTS) or set(declared) != ROOTS:
        raise ValueError("Public declaration coverage mismatch")
    seen = set()
    for name in MODULES:
        for dependency in source_imports(texts[name]):
            if dependency.startswith(NAMESPACE) and dependency not in seen:
                raise ValueError("Component dependency order is invalid: " + dependency)
        seen.add(NAMESPACE + name)
    targets = exact_targets(texts["Audit"])
    protected = project_dependencies(sources) | {
        Path(__file__).resolve(), ROOT / "tools/verify_blind_upper_components.py",
        ROOT / "tools/verify_tier6.py", LEAN / "lean-toolchain", LEAN / "lake-manifest.json",
        LEAN / "lakefile.toml",
    }
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    status = {
        "valid": False,
        "scope": "Critical quadratic single-coin variance and raw-moment base-cost bounds for all rarities, derived from actual observable population experiments; activation, scale selection, restarts, sign entropy, finite stopped-observation reconstruction, canonical affinity and work preservation, actual population compactness and affine/convex observation geometry, finite convex RMS comparison, actual observable one-run estimator and policy-specific separated pair, normalized Hellinger/work constraints, actual heterogeneous revealed mixtures, and one common separated pair for every capped observable policy, its transfer to arbitrary measurable seeds and unrestricted creation using exact population simulation laws and work charging, endpoint termination and observable affinity limits, and the critical minimax lower bound for the full rare-prior class",
        "full_critical_minimax_theorem_verified": False,
        **{flag: False for flag in FLAGS},
        "specifications_frozen_before_proofs": False,
        "source_sha256": hashes,
        "commands": [],
    }
    status_path = output / "status.json"
    status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    modules = [NAMESPACE + name for name in MODULES]
    commands = [["lake", "build", m] for m in modules] if args.sequential else [["lake", "build", *modules]]
    commands.append(["lake", "env", "lean", "ThresholdHC/CriticalEntropy/Audit.lean"])
    for index, command in enumerate(commands):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True,
                                encoding="utf-8")
        text = result.stdout + result.stderr
        (output / f"{index + 1:02d}.log").write_text(text, encoding="utf-8")
        status["commands"].append({"command": command, "exit_code": result.returncode})
        status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
        if result.returncode:
            print(text)
            return result.returncode
    status["axioms"] = validate_reports(text, result.returncode, ROOTS)
    if any(sha(ROOT / rel) != digest for rel, digest in hashes.items()):
        raise ValueError("Sources changed during audit")
    verified = {flag: True for flag in FLAGS}
    status.update(valid=True, exact_component_targets=len(targets),
                  audited_declarations=len(ROOTS), **verified)
    status_path.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"valid": True, "exact_component_targets": len(targets),
                      "audited_declarations": len(ROOTS), "evidence": str(output),
                      **verified, "full_critical_minimax_theorem_verified": False}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
