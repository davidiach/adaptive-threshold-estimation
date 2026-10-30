import ThresholdHC.StoppingProgram.Perspective
import ThresholdHC.StoppingProgram.Model
import ThresholdHC.StoppingProgram.FlowBasics
import ThresholdHC.StoppingProgram.FlowBounds
import ThresholdHC.StoppingProgram.PascalFlow
import ThresholdHC.StoppingProgram.FullCapFlow
import ThresholdHC.StoppingProgram.RareCompactness
import ThresholdHC.StoppingProgram.PrefixCoefficients
import ThresholdHC.StoppingProgram.FlowConservation
import ThresholdHC.StoppingProgram.PolicyWeights
import ThresholdHC.StoppingProgram.DecisionMixture
import ThresholdHC.StoppingProgram.DecisionIndependence
import ThresholdHC.StoppingProgram.PolicyMixture
import ThresholdHC.StoppingProgram.FlowMixture
import ThresholdHC.StoppingProgram.TableCall
import ThresholdHC.StoppingProgram.TapeMoments
import ThresholdHC.StoppingProgram.WordFlow
import ThresholdHC.StoppingProgram.WordStopping
import ThresholdHC.StoppingProgram.TableExpansion
import ThresholdHC.StoppingProgram.TableStatistics
import ThresholdHC.StoppingProgram.FlowTableRates
import ThresholdHC.StoppingProgram.MixtureStatistics
import ThresholdHC.StoppingProgram.PositiveTables
import ThresholdHC.StoppingProgram.RealizedOutputs
import ThresholdHC.StoppingProgram.ShiftEstimator
import ThresholdHC.StoppingProgram.PoissonMoments
import ThresholdHC.StoppingProgram.FlowPoisson
import ThresholdHC.StoppingProgram.CertificateRealization
import ThresholdHC.StoppingProgram.FlowOperations
import ThresholdHC.StoppingProgram.ProgramGeometry
import ThresholdHC.StoppingProgram.MomentImage
import ThresholdHC.StoppingProgram.CompactMaximum
import ThresholdHC.StoppingProgram.RobustConstraints
import ThresholdHC.StoppingProgram.ClosedProgram
import ThresholdHC.StoppingProgram.InformationBound
import ThresholdHC.StoppingProgram.ConeLagrange
import ThresholdHC.StoppingProgram.WeakDuality
import ThresholdHC.StoppingProgram.PositiveValue
import ThresholdHC.StoppingProgram.OutputChoices
import ThresholdHC.StoppingProgram.NullPruning
import ThresholdHC.StoppingProgram.SublevelBounds
import ThresholdHC.StoppingProgram.PrimalCompactness
import ThresholdHC.StoppingProgram.PrimalAttainment
import ThresholdHC.StoppingProgram.Specification
import ThresholdHC.StoppingProgram.ProgramUpper

open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ProgramUpperStatement := program_upper
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (N : ℕ),
    0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < N →
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N := program_upper
example : ∀ {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (C : Certificate N),
    Feasible μ ρ B C → 0 < N →
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      RareBudget μ A ρ B ∧ ∀ q : SignLaw, RarePrior μ ρ q →
        squaredRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) ≤
          ENNReal.ofReal (C.bias^2+C.variance) := certificate_realization

#print axioms ThresholdHC.StoppingProgram.Admissible
#print axioms ThresholdHC.StoppingProgram.AttainedDualStatement
#print axioms ThresholdHC.StoppingProgram.Certificate
#print axioms ThresholdHC.StoppingProgram.CountState
#print axioms ThresholdHC.StoppingProgram.Feasible
#print axioms ThresholdHC.StoppingProgram.FiniteCertificateStatement
#print axioms ThresholdHC.StoppingProgram.Flow
#print axioms ThresholdHC.StoppingProgram.FlowCone
#print axioms ThresholdHC.StoppingProgram.FlowCone.add
#print axioms ThresholdHC.StoppingProgram.FlowCone.scale
#print axioms ThresholdHC.StoppingProgram.FlowCone.withOutputs
#print axioms ThresholdHC.StoppingProgram.FourPriors
#print axioms ThresholdHC.StoppingProgram.NullPruned
#print axioms ThresholdHC.StoppingProgram.PositiveTable
#print axioms ThresholdHC.StoppingProgram.ProgramPoint
#print axioms ThresholdHC.StoppingProgram.ProgramUpperStatement
#print axioms ThresholdHC.StoppingProgram.abs_le_square_bound
#print axioms ThresholdHC.StoppingProgram.addFlow
#print axioms ThresholdHC.StoppingProgram.arrayAt
#print axioms ThresholdHC.StoppingProgram.arrayAt_add_flow
#print axioms ThresholdHC.StoppingProgram.arrayAt_continuous
#print axioms ThresholdHC.StoppingProgram.arrayAt_le_of
#print axioms ThresholdHC.StoppingProgram.arrayAt_nonneg
#print axioms ThresholdHC.StoppingProgram.arrayAt_scale_flow
#print axioms ThresholdHC.StoppingProgram.arrayAt_sq
#print axioms ThresholdHC.StoppingProgram.arrayAt_state
#print axioms ThresholdHC.StoppingProgram.arrayAt_zero
#print axioms ThresholdHC.StoppingProgram.arrival_independent_current
#print axioms ThresholdHC.StoppingProgram.boundedFirst_eq_iff
#print axioms ThresholdHC.StoppingProgram.certificateCap
#print axioms ThresholdHC.StoppingProgram.certificatePoint
#print axioms ThresholdHC.StoppingProgram.certificatePoint_mem_domain
#print axioms ThresholdHC.StoppingProgram.certificateSquared
#print axioms ThresholdHC.StoppingProgram.certificate_lagrange
#print axioms ThresholdHC.StoppingProgram.certificate_realization
#print axioms ThresholdHC.StoppingProgram.choose_pascal_high
#print axioms ThresholdHC.StoppingProgram.choose_pascal_low
#print axioms ThresholdHC.StoppingProgram.compactMaximum
#print axioms ThresholdHC.StoppingProgram.compactMaximum_attained
#print axioms ThresholdHC.StoppingProgram.compactMaximum_convex
#print axioms ThresholdHC.StoppingProgram.compactMaximum_le_iff
#print axioms ThresholdHC.StoppingProgram.constantCertificate
#print axioms ThresholdHC.StoppingProgram.constantCertificate_feasible
#print axioms ThresholdHC.StoppingProgram.constantPrior
#print axioms ThresholdHC.StoppingProgram.constantPrior_mean
#print axioms ThresholdHC.StoppingProgram.constantPrior_null_state
#print axioms ThresholdHC.StoppingProgram.coordinateMean
#print axioms ThresholdHC.StoppingProgram.coordinateMean_combo_left
#print axioms ThresholdHC.StoppingProgram.coordinateMean_combo_right
#print axioms ThresholdHC.StoppingProgram.countCoefficient
#print axioms ThresholdHC.StoppingProgram.countCoefficient_affine
#print axioms ThresholdHC.StoppingProgram.countCoefficient_dominated
#print axioms ThresholdHC.StoppingProgram.countCoefficient_nonneg
#print axioms ThresholdHC.StoppingProgram.countCoefficient_root
#print axioms ThresholdHC.StoppingProgram.countContrastPolynomial
#print axioms ThresholdHC.StoppingProgram.countContrastPolynomial_eval
#print axioms ThresholdHC.StoppingProgram.countDecision
#print axioms ThresholdHC.StoppingProgram.countDecision_binary
#print axioms ThresholdHC.StoppingProgram.countDecision_complement_hit
#print axioms ThresholdHC.StoppingProgram.countDecision_state
#print axioms ThresholdHC.StoppingProgram.countMean
#print axioms ThresholdHC.StoppingProgram.countMean_ge_root
#print axioms ThresholdHC.StoppingProgram.countMean_nonneg
#print axioms ThresholdHC.StoppingProgram.countMean_pruneArray
#print axioms ThresholdHC.StoppingProgram.countMean_raw
#print axioms ThresholdHC.StoppingProgram.countMean_scale
#print axioms ThresholdHC.StoppingProgram.countMean_single
#print axioms ThresholdHC.StoppingProgram.countMean_stop_eq_intensity
#print axioms ThresholdHC.StoppingProgram.countStopProbability
#print axioms ThresholdHC.StoppingProgram.countStopProbability_bounds
#print axioms ThresholdHC.StoppingProgram.countStopProbability_root
#print axioms ThresholdHC.StoppingProgram.decisionFactor
#print axioms ThresholdHC.StoppingProgram.decisionFactor_nonneg
#print axioms ThresholdHC.StoppingProgram.decisionFactor_sum
#print axioms ThresholdHC.StoppingProgram.decisionWeight
#print axioms ThresholdHC.StoppingProgram.decisionWeight_join
#print axioms ThresholdHC.StoppingProgram.decisionWeight_match
#print axioms ThresholdHC.StoppingProgram.decisionWeight_nonneg
#print axioms ThresholdHC.StoppingProgram.decisionWeight_product
#print axioms ThresholdHC.StoppingProgram.decisionWeight_single
#print axioms ThresholdHC.StoppingProgram.decisionWeight_sum
#print axioms ThresholdHC.StoppingProgram.decisionWeight_sum_split
#print axioms ThresholdHC.StoppingProgram.dualRatio
#print axioms ThresholdHC.StoppingProgram.dualRatio_le_certificate
#print axioms ThresholdHC.StoppingProgram.dualValue
#print axioms ThresholdHC.StoppingProgram.enumeratedTable_sum
#print axioms ThresholdHC.StoppingProgram.feasible_points_closed
#print axioms ThresholdHC.StoppingProgram.feasible_sublevel_bounds
#print axioms ThresholdHC.StoppingProgram.flowDecisionParameters
#print axioms ThresholdHC.StoppingProgram.flowDecisionParameters_before
#print axioms ThresholdHC.StoppingProgram.flowInformation
#print axioms ThresholdHC.StoppingProgram.flowInformation_finite_of_ratio_finite
#print axioms ThresholdHC.StoppingProgram.flowInformation_le_ratio_budget
#print axioms ThresholdHC.StoppingProgram.flowInformation_le_ratio_work
#print axioms ThresholdHC.StoppingProgram.flowInformation_scale
#print axioms ThresholdHC.StoppingProgram.flowInformation_toReal_le
#print axioms ThresholdHC.StoppingProgram.flowInformation_zero_of_intensity_zero
#print axioms ThresholdHC.StoppingProgram.flowPoissonCalls
#print axioms ThresholdHC.StoppingProgram.flowPoissonEstimator
#print axioms ThresholdHC.StoppingProgram.flowPoissonRates
#print axioms ThresholdHC.StoppingProgram.flowPoisson_squaredRisk
#print axioms ThresholdHC.StoppingProgram.flowPoisson_work
#print axioms ThresholdHC.StoppingProgram.flowTableOutput
#print axioms ThresholdHC.StoppingProgram.flowTableOutput_mean
#print axioms ThresholdHC.StoppingProgram.flowTableOutput_moment
#print axioms ThresholdHC.StoppingProgram.flowTableRate
#print axioms ThresholdHC.StoppingProgram.flowTableRate_continue
#print axioms ThresholdHC.StoppingProgram.flowTableRate_nonneg
#print axioms ThresholdHC.StoppingProgram.flowTableRate_stop
#print axioms ThresholdHC.StoppingProgram.flowTableRate_sum
#print axioms ThresholdHC.StoppingProgram.flowTableRate_supported
#print axioms ThresholdHC.StoppingProgram.flow_cone_lagrange
#print axioms ThresholdHC.StoppingProgram.flow_continue_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_mixture_arrival
#print axioms ThresholdHC.StoppingProgram.flow_mixture_mean
#print axioms ThresholdHC.StoppingProgram.flow_mixture_probability
#print axioms ThresholdHC.StoppingProgram.flow_mixture_second_moment
#print axioms ThresholdHC.StoppingProgram.flow_mixture_supported_tables
#print axioms ThresholdHC.StoppingProgram.flow_mixture_weights
#print axioms ThresholdHC.StoppingProgram.flow_mixture_work
#print axioms ThresholdHC.StoppingProgram.flow_output_mean
#print axioms ThresholdHC.StoppingProgram.flow_output_second_moment
#print axioms ThresholdHC.StoppingProgram.flow_output_zero_of_stop_zero
#print axioms ThresholdHC.StoppingProgram.flow_stop_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_total_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_work_ge_intensity
#print axioms ThresholdHC.StoppingProgram.flow_zero_intensity
#print axioms ThresholdHC.StoppingProgram.fullCapFlow
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_cone
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_intensity
#print axioms ThresholdHC.StoppingProgram.fullCap_arrayAt
#print axioms ThresholdHC.StoppingProgram.gap_tape_prefix_real
#print axioms ThresholdHC.StoppingProgram.independent_decision_factor
#print axioms ThresholdHC.StoppingProgram.informationRatio
#print axioms ThresholdHC.StoppingProgram.informationRatio_finite_of_statewise
#print axioms ThresholdHC.StoppingProgram.integrable_count_mixture
#print axioms ThresholdHC.StoppingProgram.intensity
#print axioms ThresholdHC.StoppingProgram.intensity_scale
#print axioms ThresholdHC.StoppingProgram.joinDecision
#print axioms ThresholdHC.StoppingProgram.joinDecision_other
#print axioms ThresholdHC.StoppingProgram.joinDecision_self
#print axioms ThresholdHC.StoppingProgram.joinDecision_update
#print axioms ThresholdHC.StoppingProgram.le_compactMaximum
#print axioms ThresholdHC.StoppingProgram.minimax_le_certificate
#print axioms ThresholdHC.StoppingProgram.minimax_le_program
#print axioms ThresholdHC.StoppingProgram.mixture_arrival_continue
#print axioms ThresholdHC.StoppingProgram.mixture_arrival_stop
#print axioms ThresholdHC.StoppingProgram.mixture_policyArrival
#print axioms ThresholdHC.StoppingProgram.momentCoordinateBound
#print axioms ThresholdHC.StoppingProgram.normalized_flow
#print axioms ThresholdHC.StoppingProgram.nullPruned_points_closed
#print axioms ThresholdHC.StoppingProgram.offsetCoordinateBound
#print axioms ThresholdHC.StoppingProgram.optimizedOutput
#print axioms ThresholdHC.StoppingProgram.optimizedOutput_cone
#print axioms ThresholdHC.StoppingProgram.optimizedOutput_lagrange
#print axioms ThresholdHC.StoppingProgram.optimized_perspective_identity
#print axioms ThresholdHC.StoppingProgram.outputCoordinateBound
#print axioms ThresholdHC.StoppingProgram.pascal_weights_sum
#print axioms ThresholdHC.StoppingProgram.perspective
#print axioms ThresholdHC.StoppingProgram.perspectiveCone_add
#print axioms ThresholdHC.StoppingProgram.perspective_add_le
#print axioms ThresholdHC.StoppingProgram.perspective_cone_attains
#print axioms ThresholdHC.StoppingProgram.perspective_cone_lower
#print axioms ThresholdHC.StoppingProgram.perspective_cone_lower_toReal
#print axioms ThresholdHC.StoppingProgram.perspective_finite_iff
#print axioms ThresholdHC.StoppingProgram.perspective_nonzero_zero
#print axioms ThresholdHC.StoppingProgram.perspective_pos
#print axioms ThresholdHC.StoppingProgram.perspective_scale
#print axioms ThresholdHC.StoppingProgram.perspective_zero_zero
#print axioms ThresholdHC.StoppingProgram.pointCertificate
#print axioms ThresholdHC.StoppingProgram.pointCertificate_certificatePoint
#print axioms ThresholdHC.StoppingProgram.pointFlow
#print axioms ThresholdHC.StoppingProgram.pointFlow_combo
#print axioms ThresholdHC.StoppingProgram.pointFlow_cone_closed
#print axioms ThresholdHC.StoppingProgram.pointFlow_cone_iff
#print axioms ThresholdHC.StoppingProgram.pointObjective
#print axioms ThresholdHC.StoppingProgram.pointObjective_continuous
#print axioms ThresholdHC.StoppingProgram.pointObjective_convex
#print axioms ThresholdHC.StoppingProgram.pointResidual
#print axioms ThresholdHC.StoppingProgram.pointResidual_combo_point
#print axioms ThresholdHC.StoppingProgram.pointResidual_combo_prior
#print axioms ThresholdHC.StoppingProgram.pointResidual_continuous_point
#print axioms ThresholdHC.StoppingProgram.pointResidual_continuous_prior
#print axioms ThresholdHC.StoppingProgram.point_feasible_iff
#print axioms ThresholdHC.StoppingProgram.poissonPlan_unscaled_squaredRisk
#print axioms ThresholdHC.StoppingProgram.policyArrival
#print axioms ThresholdHC.StoppingProgram.policyArrival_congr_before
#print axioms ThresholdHC.StoppingProgram.policyArrival_eq_raw
#print axioms ThresholdHC.StoppingProgram.policyArrival_mul
#print axioms ThresholdHC.StoppingProgram.policyArrival_outside
#print axioms ThresholdHC.StoppingProgram.policy_weights_realize_flow
#print axioms ThresholdHC.StoppingProgram.population_prefix_integrable
#print axioms ThresholdHC.StoppingProgram.population_prefix_integral
#print axioms ThresholdHC.StoppingProgram.population_tape_prefix_real
#print axioms ThresholdHC.StoppingProgram.population_word_integral
#print axioms ThresholdHC.StoppingProgram.positiveTable_enumeration
#print axioms ThresholdHC.StoppingProgram.positiveTable_nonempty
#print axioms ThresholdHC.StoppingProgram.positiveTable_sum
#print axioms ThresholdHC.StoppingProgram.positive_decision_one
#print axioms ThresholdHC.StoppingProgram.positive_decision_zero
#print axioms ThresholdHC.StoppingProgram.positive_dual_witness
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient_add
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient_nonneg
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient_root
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood_add
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood_nonneg
#print axioms ThresholdHC.StoppingProgram.priorCoordinates
#print axioms ThresholdHC.StoppingProgram.priorMomentImage
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_compact_convex
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_mem
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_nonempty
#print axioms ThresholdHC.StoppingProgram.programDomain
#print axioms ThresholdHC.StoppingProgram.programDomain_closed
#print axioms ThresholdHC.StoppingProgram.programDomain_convex
#print axioms ThresholdHC.StoppingProgram.programSquared
#print axioms ThresholdHC.StoppingProgram.programSquared_attained
#print axioms ThresholdHC.StoppingProgram.programSquared_finite
#print axioms ThresholdHC.StoppingProgram.programSquared_le_constant
#print axioms ThresholdHC.StoppingProgram.programSquared_pos
#print axioms ThresholdHC.StoppingProgram.programValue
#print axioms ThresholdHC.StoppingProgram.program_upper
#print axioms ThresholdHC.StoppingProgram.pruneArray
#print axioms ThresholdHC.StoppingProgram.pruneCertificate
#print axioms ThresholdHC.StoppingProgram.pruneCertificate_feasible
#print axioms ThresholdHC.StoppingProgram.pruneCertificate_pruned
#print axioms ThresholdHC.StoppingProgram.pruneFlow
#print axioms ThresholdHC.StoppingProgram.pruneFlow_cone
#print axioms ThresholdHC.StoppingProgram.prunedSublevel
#print axioms ThresholdHC.StoppingProgram.prunedSublevel_box
#print axioms ThresholdHC.StoppingProgram.prunedSublevel_closed
#print axioms ThresholdHC.StoppingProgram.prunedSublevel_compact
#print axioms ThresholdHC.StoppingProgram.quadratic_div_add_le
#print axioms ThresholdHC.StoppingProgram.rareMomentSet
#print axioms ThresholdHC.StoppingProgram.rareMomentSet_compact_convex
#print axioms ThresholdHC.StoppingProgram.rareMomentSet_eq_half_image
#print axioms ThresholdHC.StoppingProgram.rawArray
#print axioms ThresholdHC.StoppingProgram.rawArray_mul
#print axioms ThresholdHC.StoppingProgram.rawArray_outside
#print axioms ThresholdHC.StoppingProgram.rawArray_terminal
#print axioms ThresholdHC.StoppingProgram.rawChildren
#print axioms ThresholdHC.StoppingProgram.rawLayer
#print axioms ThresholdHC.StoppingProgram.rawLayer_countMean
#print axioms ThresholdHC.StoppingProgram.raw_continue_fraction
#print axioms ThresholdHC.StoppingProgram.raw_flow_recursion
#print axioms ThresholdHC.StoppingProgram.raw_layer_conservation
#print axioms ThresholdHC.StoppingProgram.raw_root_total
#print axioms ThresholdHC.StoppingProgram.raw_stop_fraction
#print axioms ThresholdHC.StoppingProgram.raw_weighted_telescope
#print axioms ThresholdHC.StoppingProgram.robustResidual
#print axioms ThresholdHC.StoppingProgram.robustResidual_convex
#print axioms ThresholdHC.StoppingProgram.robustResidual_nonpos_iff
#print axioms ThresholdHC.StoppingProgram.rootState
#print axioms ThresholdHC.StoppingProgram.scaleFlow
#print axioms ThresholdHC.StoppingProgram.shiftEstimator
#print axioms ThresholdHC.StoppingProgram.shiftEstimator_experiment
#print axioms ThresholdHC.StoppingProgram.shiftEstimator_squaredRisk
#print axioms ThresholdHC.StoppingProgram.shiftEstimator_work
#print axioms ThresholdHC.StoppingProgram.shortWord
#print axioms ThresholdHC.StoppingProgram.shortWord_self
#print axioms ThresholdHC.StoppingProgram.shortWord_snoc
#print axioms ThresholdHC.StoppingProgram.shortWord_tapePrefix
#print axioms ThresholdHC.StoppingProgram.singleOutput
#print axioms ThresholdHC.StoppingProgram.singleOutput_cone
#print axioms ThresholdHC.StoppingProgram.squared_bias_bound
#print axioms ThresholdHC.StoppingProgram.state_eq_root
#print axioms ThresholdHC.StoppingProgram.sum_words_by_heads
#print axioms ThresholdHC.StoppingProgram.tableCall
#print axioms ThresholdHC.StoppingProgram.tableCall_cost_le
#print axioms ThresholdHC.StoppingProgram.tableCost
#print axioms ThresholdHC.StoppingProgram.tableCost_eq_iff
#print axioms ThresholdHC.StoppingProgram.tableCost_ge_iff
#print axioms ThresholdHC.StoppingProgram.tableCost_integral
#print axioms ThresholdHC.StoppingProgram.tableCost_positive
#print axioms ThresholdHC.StoppingProgram.tableCost_word_expansion
#print axioms ThresholdHC.StoppingProgram.tableDecision_at_stop
#print axioms ThresholdHC.StoppingProgram.tableHit
#print axioms ThresholdHC.StoppingProgram.tableStoppedState
#print axioms ThresholdHC.StoppingProgram.tableValue
#print axioms ThresholdHC.StoppingProgram.tableValue_bounded
#print axioms ThresholdHC.StoppingProgram.tableValue_eq
#print axioms ThresholdHC.StoppingProgram.tableValue_full_prefix
#print axioms ThresholdHC.StoppingProgram.tableValue_integral
#print axioms ThresholdHC.StoppingProgram.tableValue_integral_full_prefix
#print axioms ThresholdHC.StoppingProgram.tableValue_second_moment
#print axioms ThresholdHC.StoppingProgram.tableValue_sq
#print axioms ThresholdHC.StoppingProgram.tableValue_word_expansion
#print axioms ThresholdHC.StoppingProgram.weak_duality
#print axioms ThresholdHC.StoppingProgram.withOutputs
#print axioms ThresholdHC.StoppingProgram.wordArrival
#print axioms ThresholdHC.StoppingProgram.wordArrivalCount
#print axioms ThresholdHC.StoppingProgram.wordArrivalCount_eq_policyArrival
#print axioms ThresholdHC.StoppingProgram.wordArrivalCount_succ
#print axioms ThresholdHC.StoppingProgram.wordArrivalCount_zero
#print axioms ThresholdHC.StoppingProgram.wordArrival_snoc
#print axioms ThresholdHC.StoppingProgram.wordArrival_tape_indicator
#print axioms ThresholdHC.StoppingProgram.wordContinue_tape_indicator
#print axioms ThresholdHC.StoppingProgram.wordHeads_le_length
#print axioms ThresholdHC.StoppingProgram.wordHeads_snoc
#print axioms ThresholdHC.StoppingProgram.wordHeads_sum
#print axioms ThresholdHC.StoppingProgram.wordStop_tape_indicator
#print axioms ThresholdHC.StoppingProgram.zeroFlow
#print axioms ThresholdHC.StoppingProgram.zeroFlow_cone
