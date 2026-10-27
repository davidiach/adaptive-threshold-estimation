import ThresholdHC.Tier5.BoundReduction
import ThresholdHC.Tier5.CreationBase
import ThresholdHC.Tier5.CreationExample
import ThresholdHC.Tier5.CreationFresh
import ThresholdHC.Tier5.CreationModel
import ThresholdHC.Tier5.CreationPadding
import ThresholdHC.Tier5.CreationProduct
import ThresholdHC.Tier5.Entropy
import ThresholdHC.Tier5.EntropyPrefix
import ThresholdHC.Tier5.FiniteCreation
import ThresholdHC.Tier5.FiniteEnvironment
import ThresholdHC.Tier5.FiniteJoint
import ThresholdHC.Tier5.Full
import ThresholdHC.Tier5.Model
import ThresholdHC.Tier5.PriorRatio
import ThresholdHC.Tier5.Specification
import ThresholdHC.Tier5.StoppingBase
import ThresholdHC.Tier5.StoppingEntropy
import ThresholdHC.Tier5.StoppingFull
namespace PopulationStepTier5Audit
theorem audit_creation_law_total : ThresholdHC.Tier5.CreationTotalStatement := ThresholdHC.Tier5.creation_law_total
theorem audit_creation_law_consistent : ThresholdHC.Tier5.CreationConsistencyStatement := ThresholdHC.Tier5.creation_law_consistent
theorem audit_creation_finite_kl_bound : ThresholdHC.Tier5.CreationFiniteKLStatement := ThresholdHC.Tier5.creation_finite_kl_bound
theorem audit_creation_stops : ThresholdHC.Tier5.CreationStopsStatement := ThresholdHC.Tier5.creation_stops
theorem audit_creation_kl_eq_iSup : ThresholdHC.Tier5.CreationKLSupremumStatement := ThresholdHC.Tier5.creation_kl_eq_iSup
theorem audit_creation_infinite_kl_bound : ThresholdHC.Tier5.CreationInfiniteKLStatement := ThresholdHC.Tier5.creation_infinite_kl_bound
theorem audit_creation_observable_kl_bound : ThresholdHC.Tier5.CreationObservableKLStatement := ThresholdHC.Tier5.creation_observable_kl_bound
theorem audit_unbounded_creation_example : ThresholdHC.Tier5.UnboundedCreationExampleStatement := ThresholdHC.Tier5.unbounded_creation_example
theorem audit_tier5_landmark : ThresholdHC.Tier5.Tier5LandmarkStatement := ThresholdHC.Tier5.tier5_landmark
end PopulationStepTier5Audit
#print axioms PopulationStepTier5Audit.audit_creation_finite_kl_bound
#print axioms PopulationStepTier5Audit.audit_creation_infinite_kl_bound
#print axioms PopulationStepTier5Audit.audit_creation_kl_eq_iSup
#print axioms PopulationStepTier5Audit.audit_creation_law_consistent
#print axioms PopulationStepTier5Audit.audit_creation_law_total
#print axioms PopulationStepTier5Audit.audit_creation_observable_kl_bound
#print axioms PopulationStepTier5Audit.audit_creation_stops
#print axioms PopulationStepTier5Audit.audit_tier5_landmark
#print axioms PopulationStepTier5Audit.audit_unbounded_creation_example
#print axioms ThresholdHC.Tier5.CreationConsistencyStatement
#print axioms ThresholdHC.Tier5.CreationFiniteKLStatement
#print axioms ThresholdHC.Tier5.CreationInfiniteKLStatement
#print axioms ThresholdHC.Tier5.CreationKLSupremumStatement
#print axioms ThresholdHC.Tier5.CreationObservableKLStatement
#print axioms ThresholdHC.Tier5.CreationStopsStatement
#print axioms ThresholdHC.Tier5.CreationTotalStatement
#print axioms ThresholdHC.Tier5.FiniteKernelRealization
#print axioms ThresholdHC.Tier5.MeasurableCreationPolicy
#print axioms ThresholdHC.Tier5.MeasurableEnvironment
#print axioms ThresholdHC.Tier5.RealizesCreationPrefixes
#print axioms ThresholdHC.Tier5.Tier5LandmarkStatement
#print axioms ThresholdHC.Tier5.UnboundedCreationExampleStatement
#print axioms ThresholdHC.Tier5.abs_log_ratio_le
#print axioms ThresholdHC.Tier5.bernoulli_real_singleton
#print axioms ThresholdHC.Tier5.capPolicy
#print axioms ThresholdHC.Tier5.capPolicy_isSome_at
#print axioms ThresholdHC.Tier5.capPolicy_succ_agree
#print axioms ThresholdHC.Tier5.cappedLaw_succ_eq
#print axioms ThresholdHC.Tier5.coinCap
#print axioms ThresholdHC.Tier5.coinCap_le_succ
#print axioms ThresholdHC.Tier5.coinCap_mono
#print axioms ThresholdHC.Tier5.coinLike_eq_one_of_not_queried
#print axioms ThresholdHC.Tier5.creationActionMeasurableSpace
#print axioms ThresholdHC.Tier5.creationInfiniteKL_of_prefix
#print axioms ThresholdHC.Tier5.creationKLSupremum_of_finiteKL
#print axioms ThresholdHC.Tier5.creationLaw
#print axioms ThresholdHC.Tier5.creationLaw_eq_capped
#print axioms ThresholdHC.Tier5.creationLaw_sum_extensions
#print axioms ThresholdHC.Tier5.creationLaw_total
#print axioms ThresholdHC.Tier5.creationLaw_zero_of_invalid
#print axioms ThresholdHC.Tier5.creationObservableKL_of_bound
#print axioms ThresholdHC.Tier5.creationPolicyCode
#print axioms ThresholdHC.Tier5.creation_finite_kl_bound
#print axioms ThresholdHC.Tier5.creation_infinite_kl_bound
#print axioms ThresholdHC.Tier5.creation_infinite_kl_bound_extended
#print axioms ThresholdHC.Tier5.creation_kl_eq_iSup
#print axioms ThresholdHC.Tier5.creation_law_consistent
#print axioms ThresholdHC.Tier5.creation_law_total
#print axioms ThresholdHC.Tier5.creation_observable_kl_bound
#print axioms ThresholdHC.Tier5.creation_stops
#print axioms ThresholdHC.Tier5.finite_kernel_kl_bound
#print axioms ThresholdHC.Tier5.finite_kernel_kl_identity
#print axioms ThresholdHC.Tier5.finite_transcript_le_of_prior_ratio_horizon
#print axioms ThresholdHC.Tier5.finite_transcript_minus_le_plus_horizon
#print axioms ThresholdHC.Tier5.finite_transcript_plus_le_minus_horizon
#print axioms ThresholdHC.Tier5.freshBitLaw
#print axioms ThresholdHC.Tier5.freshBitLaw_integral_prefix
#print axioms ThresholdHC.Tier5.freshBitLaw_map_prefix
#print axioms ThresholdHC.Tier5.freshBitLaw_probability
#print axioms ThresholdHC.Tier5.freshPolicy
#print axioms ThresholdHC.Tier5.freshProcessLaw
#print axioms ThresholdHC.Tier5.freshProcessLaw_probability
#print axioms ThresholdHC.Tier5.freshTape
#print axioms ThresholdHC.Tier5.freshTape_coordinate_measurable
#print axioms ThresholdHC.Tier5.freshTruncatedPrefix
#print axioms ThresholdHC.Tier5.freshTruncatedPrefix_hist_length
#print axioms ThresholdHC.Tier5.freshTruncatedPrefix_snoc
#print axioms ThresholdHC.Tier5.fresh_coinCap_le
#print axioms ThresholdHC.Tier5.fresh_finite_expected_work
#print axioms ThresholdHC.Tier5.fresh_path_expect
#print axioms ThresholdHC.Tier5.fresh_prefix_work_eq
#print axioms ThresholdHC.Tier5.fresh_realizes
#print axioms ThresholdHC.Tier5.fresh_totalWork
#print axioms ThresholdHC.Tier5.fresh_transcript_expect
#print axioms ThresholdHC.Tier5.fresh_unbounded_work
#print axioms ThresholdHC.Tier5.histBefore_length_le
#print axioms ThresholdHC.Tier5.integrable_kernel_kl
#print axioms ThresholdHC.Tier5.integrable_kernel_work
#print axioms ThresholdHC.Tier5.integrable_of_abs_bound
#print axioms ThresholdHC.Tier5.joint_tape_kl_eq_iSup_prefix_of_ac
#print axioms ThresholdHC.Tier5.klDiv_eq_iSup_map_of_generates
#print axioms ThresholdHC.Tier5.klDiv_map_eq_lintegral_condExp
#print axioms ThresholdHC.Tier5.klDiv_of_bounded_likelihood
#print axioms ThresholdHC.Tier5.measurable_capPolicy
#print axioms ThresholdHC.Tier5.measurable_coinCap
#print axioms ThresholdHC.Tier5.measurable_creationLaw
#print axioms ThresholdHC.Tier5.measurable_creationPolicyCode
#print axioms ThresholdHC.Tier5.measurable_creation_policy
#print axioms ThresholdHC.Tier5.measurable_freshTape
#print axioms ThresholdHC.Tier5.measurable_stoppingFlagPolicy
#print axioms ThresholdHC.Tier5.measurable_variable_finite_eval
#print axioms ThresholdHC.Tier5.measurable_variable_pathProb
#print axioms ThresholdHC.Tier5.measurable_variable_transcriptLaw
#print axioms ThresholdHC.Tier5.prefixSigma
#print axioms ThresholdHC.Tier5.prefixSigma_iSup
#print axioms ThresholdHC.Tier5.prefixSigma_mono
#print axioms ThresholdHC.Tier5.queriedCoins
#print axioms ThresholdHC.Tier5.queriedCoins_card_le
#print axioms ThresholdHC.Tier5.ratio_le_of_comparison
#print axioms ThresholdHC.Tier5.realized_creation_prefix_kernel
#print axioms ThresholdHC.Tier5.realized_creation_prefix_work
#print axioms ThresholdHC.Tier5.realized_creation_stopped_cover
#print axioms ThresholdHC.Tier5.realized_creation_stopped_reconstruction
#print axioms ThresholdHC.Tier5.realized_creation_valid_step
#print axioms ThresholdHC.Tier5.selected_lt_coinCap
#print axioms ThresholdHC.Tier5.stoppingFlagPolicy
#print axioms ThresholdHC.Tier5.tier5_landmark
#print axioms ThresholdHC.Tier5.transcriptLaw_unused_last
#print axioms ThresholdHC.Tier5.unbounded_creation_example
