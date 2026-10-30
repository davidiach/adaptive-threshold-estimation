import ThresholdHC.StoppingProgram.Perspective
import ThresholdHC.StoppingProgram.Model
import ThresholdHC.StoppingProgram.FlowBasics
import ThresholdHC.StoppingProgram.FlowBounds
import ThresholdHC.StoppingProgram.FlowOperations
import ThresholdHC.StoppingProgram.ProgramGeometry
import ThresholdHC.StoppingProgram.RareCompactness
import ThresholdHC.StoppingProgram.FullCapFlow
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
import ThresholdHC.StoppingProgram.Slater
import ThresholdHC.StoppingProgram.ProgramMultipliers
import ThresholdHC.StoppingProgram.MinimaxSelection
import ThresholdHC.StoppingProgram.FourPriorMultipliers
import ThresholdHC.StoppingProgram.PriceMultipliers
import ThresholdHC.StoppingProgram.ConePriceRatio
import ThresholdHC.StoppingProgram.StrongDuality
import ThresholdHC.StoppingProgram.Specification
import ThresholdHC.StoppingProgram.DualTheorem

open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram
example : AttainedDualStatement := attained_four_prior_dual
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (N : ℕ), 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < N →
    programSquared μ ρ B N = dualValue μ ρ B N ∧
    ∃ (C : Certificate N) (Q : FourPriors),
      Feasible μ ρ B C ∧ Admissible μ ρ Q ∧
      certificateSquared C = programSquared μ ρ B N ∧
      dualRatio μ B N Q = programSquared μ ρ B N ∧
      0 < programSquared μ ρ B N ∧ informationRatio μ N Q < ⊤ := attained_four_prior_dual

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
#print axioms ThresholdHC.StoppingProgram.PriorTuple
#print axioms ThresholdHC.StoppingProgram.ProgramPoint
#print axioms ThresholdHC.StoppingProgram.ProgramUpperStatement
#print axioms ThresholdHC.StoppingProgram.abs_le_square_bound
#print axioms ThresholdHC.StoppingProgram.addFlow
#print axioms ThresholdHC.StoppingProgram.arrayAt
#print axioms ThresholdHC.StoppingProgram.arrayAt_add_flow
#print axioms ThresholdHC.StoppingProgram.arrayAt_continuous
#print axioms ThresholdHC.StoppingProgram.arrayAt_le_of
#print axioms ThresholdHC.StoppingProgram.arrayAt_scale_flow
#print axioms ThresholdHC.StoppingProgram.arrayAt_zero
#print axioms ThresholdHC.StoppingProgram.attained_four_prior_dual
#print axioms ThresholdHC.StoppingProgram.attained_price_multipliers
#print axioms ThresholdHC.StoppingProgram.certificateCap
#print axioms ThresholdHC.StoppingProgram.certificatePoint
#print axioms ThresholdHC.StoppingProgram.certificatePoint_mem_domain
#print axioms ThresholdHC.StoppingProgram.certificateSquared
#print axioms ThresholdHC.StoppingProgram.certificate_lagrange
#print axioms ThresholdHC.StoppingProgram.compactMaximum
#print axioms ThresholdHC.StoppingProgram.compactMaximum_attained
#print axioms ThresholdHC.StoppingProgram.compactMaximum_convex
#print axioms ThresholdHC.StoppingProgram.compactMaximum_le_iff
#print axioms ThresholdHC.StoppingProgram.compact_minimax_selection
#print axioms ThresholdHC.StoppingProgram.conePrice
#print axioms ThresholdHC.StoppingProgram.conePrice_information_bound
#print axioms ThresholdHC.StoppingProgram.conePrice_information_finite
#print axioms ThresholdHC.StoppingProgram.conePrice_null_contrast
#print axioms ThresholdHC.StoppingProgram.conePrice_ratio_bound
#print axioms ThresholdHC.StoppingProgram.conePrice_ratio_finite
#print axioms ThresholdHC.StoppingProgram.conePrice_ratio_real_bound
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
#print axioms ThresholdHC.StoppingProgram.countMean
#print axioms ThresholdHC.StoppingProgram.countMean_ge_root
#print axioms ThresholdHC.StoppingProgram.countMean_nonneg
#print axioms ThresholdHC.StoppingProgram.countMean_pruneArray
#print axioms ThresholdHC.StoppingProgram.countMean_scale
#print axioms ThresholdHC.StoppingProgram.countMean_single
#print axioms ThresholdHC.StoppingProgram.dualRatio
#print axioms ThresholdHC.StoppingProgram.dualRatio_le_certificate
#print axioms ThresholdHC.StoppingProgram.dualValue
#print axioms ThresholdHC.StoppingProgram.feasible_points_closed
#print axioms ThresholdHC.StoppingProgram.feasible_sublevel_bounds
#print axioms ThresholdHC.StoppingProgram.finite_slater_multipliers
#print axioms ThresholdHC.StoppingProgram.flowInformation
#print axioms ThresholdHC.StoppingProgram.flowInformation_finite_of_ratio_finite
#print axioms ThresholdHC.StoppingProgram.flowInformation_le_ratio_budget
#print axioms ThresholdHC.StoppingProgram.flowInformation_le_ratio_work
#print axioms ThresholdHC.StoppingProgram.flowInformation_scale
#print axioms ThresholdHC.StoppingProgram.flowInformation_toReal_le
#print axioms ThresholdHC.StoppingProgram.flowInformation_zero_of_intensity_zero
#print axioms ThresholdHC.StoppingProgram.flow_cone_lagrange
#print axioms ThresholdHC.StoppingProgram.flow_continue_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_output_zero_of_stop_zero
#print axioms ThresholdHC.StoppingProgram.flow_stop_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_total_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_work_ge_intensity
#print axioms ThresholdHC.StoppingProgram.flow_zero_intensity
#print axioms ThresholdHC.StoppingProgram.four_prior_multipliers
#print axioms ThresholdHC.StoppingProgram.fullCapFlow
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_cone
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_intensity
#print axioms ThresholdHC.StoppingProgram.fullCap_arrayAt
#print axioms ThresholdHC.StoppingProgram.informationRatio
#print axioms ThresholdHC.StoppingProgram.informationRatio_finite_of_statewise
#print axioms ThresholdHC.StoppingProgram.integrable_count_mixture
#print axioms ThresholdHC.StoppingProgram.intensity
#print axioms ThresholdHC.StoppingProgram.intensity_scale
#print axioms ThresholdHC.StoppingProgram.le_compactMaximum
#print axioms ThresholdHC.StoppingProgram.linear_lower_bound_forces_zero
#print axioms ThresholdHC.StoppingProgram.linear_pi_expansion
#print axioms ThresholdHC.StoppingProgram.linear_ray_lower_bound_forces_nonneg
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
#print axioms ThresholdHC.StoppingProgram.positive_dual_witness
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood_nonneg
#print axioms ThresholdHC.StoppingProgram.priorCoordinates
#print axioms ThresholdHC.StoppingProgram.priorMomentImage
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_compact_convex
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_mem
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_nonempty
#print axioms ThresholdHC.StoppingProgram.priorTupleSet
#print axioms ThresholdHC.StoppingProgram.programDomain
#print axioms ThresholdHC.StoppingProgram.programDomain_closed
#print axioms ThresholdHC.StoppingProgram.programDomain_convex
#print axioms ThresholdHC.StoppingProgram.programSquared
#print axioms ThresholdHC.StoppingProgram.programSquared_attained
#print axioms ThresholdHC.StoppingProgram.programSquared_finite
#print axioms ThresholdHC.StoppingProgram.programSquared_le_constant
#print axioms ThresholdHC.StoppingProgram.programSquared_pos
#print axioms ThresholdHC.StoppingProgram.programValue
#print axioms ThresholdHC.StoppingProgram.program_multipliers
#print axioms ThresholdHC.StoppingProgram.program_point_lower
#print axioms ThresholdHC.StoppingProgram.program_strict_inequalities
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
#print axioms ThresholdHC.StoppingProgram.robustResidual
#print axioms ThresholdHC.StoppingProgram.robustResidual_convex
#print axioms ThresholdHC.StoppingProgram.robustResidual_nonpos_iff
#print axioms ThresholdHC.StoppingProgram.rootState
#print axioms ThresholdHC.StoppingProgram.scaleFlow
#print axioms ThresholdHC.StoppingProgram.singleOutput
#print axioms ThresholdHC.StoppingProgram.singleOutput_cone
#print axioms ThresholdHC.StoppingProgram.state_eq_root
#print axioms ThresholdHC.StoppingProgram.strong_four_prior_duality
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian_concave
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian_continuous_point
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian_continuous_prior
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian_convex
#print axioms ThresholdHC.StoppingProgram.tuple_multipliers
#print axioms ThresholdHC.StoppingProgram.weak_duality
#print axioms ThresholdHC.StoppingProgram.withOutputs
#print axioms ThresholdHC.StoppingProgram.zeroFlow
#print axioms ThresholdHC.StoppingProgram.zeroFlow_cone
