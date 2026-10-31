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
import ThresholdHC.StoppingProgram.OrderedPrefix
import ThresholdHC.StoppingProgram.RawFlowConstruction
import ThresholdHC.StoppingProgram.OrderedWeights
import ThresholdHC.StoppingProgram.OrderedStoppedLaw
import ThresholdHC.StoppingProgram.OrderedAffinity
import ThresholdHC.StoppingProgram.WordStopping
import ThresholdHC.StoppingProgram.TableExpansion
import ThresholdHC.StoppingProgram.TableStatistics
import ThresholdHC.StoppingProgram.PrefixInformation
import ThresholdHC.StoppingProgram.FlowCostMoment
import ThresholdHC.StoppingProgram.OrderedRewards
import ThresholdHC.StoppingProgram.PolicyFlow
import ThresholdHC.StoppingProgram.Bellman
import ThresholdHC.StoppingProgram.FlowPotential
import ThresholdHC.StoppingProgram.BellmanFlow
import ThresholdHC.StoppingProgram.PriceRatio
import ThresholdHC.StoppingProgram.InformationBellman
import ThresholdHC.StoppingProgram.FlowOperations
import ThresholdHC.StoppingProgram.InformationBound
import ThresholdHC.StoppingProgram.InformationFiniteness
import ThresholdHC.StoppingProgram.MomentImage
import ThresholdHC.StoppingProgram.CompactMaximum
import ThresholdHC.StoppingProgram.FunctionMomentImage
import ThresholdHC.StoppingProgram.PriorMixtures
import ThresholdHC.StoppingProgram.PerspectiveMonotonic
import ThresholdHC.StoppingProgram.AbsorbedPriors
import ThresholdHC.StoppingProgram.MidpointInformation
import ThresholdHC.StoppingProgram.OrderedHellinger
import ThresholdHC.StoppingProgram.OrderedWork
import ThresholdHC.StoppingProgram.OrderedInformationBound
import ThresholdHC.StoppingProgram.FinitePopulationInformation
import ThresholdHC.StoppingProgram.CreationInformation
import ThresholdHC.StoppingProgram.ObservableInformation
import ThresholdHC.StoppingProgram.AffinityOverlap
import ThresholdHC.StoppingProgram.AffinityRisk
import ThresholdHC.StoppingProgram.PriorContraction
import ThresholdHC.StoppingProgram.PrefixRisk
import ThresholdHC.StoppingProgram.ContractionScale
import ThresholdHC.StoppingProgram.AbsorptionRatio
import ThresholdHC.StoppingProgram.ProgramGeometry
import ThresholdHC.StoppingProgram.RobustConstraints
import ThresholdHC.StoppingProgram.ClosedProgram
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
import ThresholdHC.StoppingProgram.MidpointComparison
import ThresholdHC.StoppingProgram.PrefixModulus

open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ {Ω : Type} [MeasurableSpace Ω],
    ∀ (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    ∀ (f : Ω → ℝ), Measurable f → ∀ a b : ℝ,
    ENNReal.ofReal ((b-a)^2*(hellingerAffinity P Q).toReal^2/4) ≤
      max (squaredRisk P f a) (squaredRisk Q f b) := affinity_squared_risk
example : ∀ {Ω : Type} [MeasurableSpace Ω],
    ∀ (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    ∀ (f : Ω → ℝ), Measurable f → ∀ a b : ℝ, a ≤ b →
    ENNReal.ofReal ((b-a)*(hellingerAffinity P Q).toReal/2) ≤
      max (rootMeanRisk P f a) (rootMeanRisk Q f b) := affinity_rms_risk
example : ∀ {R : Type} [MeasurableSpace R],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R),
    ∀ (q r : SignLaw) (N : ℕ) (B : ℝ), 0 ≤ B →
    expectedWork μ A (ThresholdHC.StoppingProgram.midpointPrior q r) ≤ ENNReal.ofReal B →
    1-(hellingerAffinity
      ((experimentLaw μ A q).map (fun z => (z.1.1,processPrefix N z.2)))
      ((experimentLaw μ A r).map (fun z => (z.1.1,processPrefix N z.2)))).toReal ≤
      (informationRatio μ N (midpointFourPriors q r)).toReal/4*B := by
  intro R _ μ _ A q r N B hB hw
  simpa only [observablePrefixLaw] using observable_prefix_information_budget μ A q r N B hB hw
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    ∀ (q r : SignLaw) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1),
    signMean μ (contractPrior r q s hs).val-signMean μ (contractPrior q r s hs).val =
      s*(signMean μ r.val-signMean μ q.val) := contractPrior_gap
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    ∀ (N : ℕ) (q r : SignLaw) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1),
    informationRatio μ N (midpointFourPriors (contractPrior q r s hs) (contractPrior r q s hs)) =
      ENNReal.ofReal (s^2)*informationRatio μ N (midpointFourPriors q r) := contractPrior_informationRatio
example : ∀ {R : Type} [MeasurableSpace R],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R),
    ∀ (q r : SignLaw) (N : ℕ) (B : ℝ), 0 ≤ B →
    expectedWork μ A (ThresholdHC.StoppingProgram.midpointPrior q r) ≤ ENNReal.ofReal B →
    signMean μ q.val ≤ signMean μ r.val →
    ∀ (f : R × (Fin N → Option Bool) → ℝ), Measurable f →
    ENNReal.ofReal ((signMean μ r.val-signMean μ q.val)/2 *
      (1-(informationRatio μ N (midpointFourPriors q r)).toReal*B/4)) ≤
        max (rootMeanRisk (observablePrefixLaw μ A q N) f (signMean μ q.val))
          (rootMeanRisk (observablePrefixLaw μ A r N) f (signMean μ r.val)) := observable_prefix_risk
example : ∀ {R : Type} [MeasurableSpace R],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R),
    ∀ (ρ B : ℝ), 0 < ρ → ρ ≤ 1/2 → 0 < B → RareBudget μ A ρ B →
    ∀ (N : ℕ) (f : R × (Fin N → Option Bool) → ℝ), Measurable f →
    ∀ T : ℝ≥0∞, (∀ u : SignLaw, RarePrior μ ρ u →
      rootMeanRisk (observablePrefixLaw μ A u N) f (signMean μ u.val) ≤ T) →
    programValue μ ρ B N ≤ 8*T := prefix_program_bound

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
#print axioms ThresholdHC.StoppingProgram.StopTree
#print axioms ThresholdHC.StoppingProgram.abs_le_square_bound
#print axioms ThresholdHC.StoppingProgram.absorbedHigh
#print axioms ThresholdHC.StoppingProgram.absorbedLow
#print axioms ThresholdHC.StoppingProgram.absorbedPriors
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_admissible
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_contrast
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_dualRatio
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_gap
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_informationRatio_le
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_information_le
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_mean_work_ge
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_perspective_le
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_reference
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_variance_ge
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_work_ge
#print axioms ThresholdHC.StoppingProgram.addFlow
#print axioms ThresholdHC.StoppingProgram.affinity_integral_sqrt_overlap
#print axioms ThresholdHC.StoppingProgram.affinity_rms_risk
#print axioms ThresholdHC.StoppingProgram.affinity_sq_le_overlap
#print axioms ThresholdHC.StoppingProgram.affinity_squared_risk
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
#print axioms ThresholdHC.StoppingProgram.attained_four_prior_dual
#print axioms ThresholdHC.StoppingProgram.attained_price_multipliers
#print axioms ThresholdHC.StoppingProgram.bellman
#print axioms ThresholdHC.StoppingProgram.bellmanFlow
#print axioms ThresholdHC.StoppingProgram.bellmanFlow_cone
#print axioms ThresholdHC.StoppingProgram.bellmanFlow_intensity
#print axioms ThresholdHC.StoppingProgram.bellmanFlow_score
#print axioms ThresholdHC.StoppingProgram.bellmanRatio
#print axioms ThresholdHC.StoppingProgram.bellmanRatio_nonneg
#print axioms ThresholdHC.StoppingProgram.bellmanStopProbability
#print axioms ThresholdHC.StoppingProgram.bellmanStopProbability_binary
#print axioms ThresholdHC.StoppingProgram.bellmanStopProbability_complementarity
#print axioms ThresholdHC.StoppingProgram.bellmanStopProbability_root
#print axioms ThresholdHC.StoppingProgram.bellmanStopProbability_terminal
#print axioms ThresholdHC.StoppingProgram.boundedFirst_eq_iff
#print axioms ThresholdHC.StoppingProgram.certificateCap
#print axioms ThresholdHC.StoppingProgram.certificatePoint
#print axioms ThresholdHC.StoppingProgram.certificatePoint_mem_domain
#print axioms ThresholdHC.StoppingProgram.certificateSquared
#print axioms ThresholdHC.StoppingProgram.certificate_lagrange
#print axioms ThresholdHC.StoppingProgram.choose_pascal_high
#print axioms ThresholdHC.StoppingProgram.choose_pascal_low
#print axioms ThresholdHC.StoppingProgram.compactMaximum
#print axioms ThresholdHC.StoppingProgram.compactMaximum_attained
#print axioms ThresholdHC.StoppingProgram.compactMaximum_convex
#print axioms ThresholdHC.StoppingProgram.compactMaximum_le_iff
#print axioms ThresholdHC.StoppingProgram.compact_minimax_selection
#print axioms ThresholdHC.StoppingProgram.completedStop
#print axioms ThresholdHC.StoppingProgram.completedStop_eq_iff
#print axioms ThresholdHC.StoppingProgram.completedStop_le_cap
#print axioms ThresholdHC.StoppingProgram.completedStop_snoc_le_iff
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
#print axioms ThresholdHC.StoppingProgram.continuous_bellman
#print axioms ThresholdHC.StoppingProgram.continuous_rootBellman
#print axioms ThresholdHC.StoppingProgram.contractPrior
#print axioms ThresholdHC.StoppingProgram.contractPrior_contrast
#print axioms ThresholdHC.StoppingProgram.contractPrior_gap
#print axioms ThresholdHC.StoppingProgram.contractPrior_information
#print axioms ThresholdHC.StoppingProgram.contractPrior_informationRatio
#print axioms ThresholdHC.StoppingProgram.contractPrior_midpoint
#print axioms ThresholdHC.StoppingProgram.contractPrior_rare
#print axioms ThresholdHC.StoppingProgram.contraction_scale
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
#print axioms ThresholdHC.StoppingProgram.countInformation_eq
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
#print axioms ThresholdHC.StoppingProgram.creation_population_information
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
#print axioms ThresholdHC.StoppingProgram.density_squared_loss
#print axioms ThresholdHC.StoppingProgram.dualRatio
#print axioms ThresholdHC.StoppingProgram.dualRatio_le_certificate
#print axioms ThresholdHC.StoppingProgram.dualValue
#print axioms ThresholdHC.StoppingProgram.dualValue_le_nine_midpointSquared
#print axioms ThresholdHC.StoppingProgram.factored_affinity_nonnegative
#print axioms ThresholdHC.StoppingProgram.feasible_points_closed
#print axioms ThresholdHC.StoppingProgram.feasible_sublevel_bounds
#print axioms ThresholdHC.StoppingProgram.finite_population_information
#print axioms ThresholdHC.StoppingProgram.finite_slater_multipliers
#print axioms ThresholdHC.StoppingProgram.finite_word_projection_integral
#print axioms ThresholdHC.StoppingProgram.flowDecisionParameters
#print axioms ThresholdHC.StoppingProgram.flowDecisionParameters_before
#print axioms ThresholdHC.StoppingProgram.flowInformation
#print axioms ThresholdHC.StoppingProgram.flowInformation_finite_of_ratio_finite
#print axioms ThresholdHC.StoppingProgram.flowInformation_finite_prefixes
#print axioms ThresholdHC.StoppingProgram.flowInformation_le_ratio_budget
#print axioms ThresholdHC.StoppingProgram.flowInformation_le_ratio_work
#print axioms ThresholdHC.StoppingProgram.flowInformation_raw
#print axioms ThresholdHC.StoppingProgram.flowInformation_raw_states
#print axioms ThresholdHC.StoppingProgram.flowInformation_scale
#print axioms ThresholdHC.StoppingProgram.flowInformation_toReal_le
#print axioms ThresholdHC.StoppingProgram.flowInformation_toReal_raw
#print axioms ThresholdHC.StoppingProgram.flowInformation_zero_of_intensity_zero
#print axioms ThresholdHC.StoppingProgram.flowScore_information
#print axioms ThresholdHC.StoppingProgram.flowScore_le_rootBellman
#print axioms ThresholdHC.StoppingProgram.flowScore_maximum
#print axioms ThresholdHC.StoppingProgram.flow_cone_lagrange
#print axioms ThresholdHC.StoppingProgram.flow_continue_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_mixture_arrival
#print axioms ThresholdHC.StoppingProgram.flow_mixture_probability
#print axioms ThresholdHC.StoppingProgram.flow_mixture_supported_tables
#print axioms ThresholdHC.StoppingProgram.flow_mixture_weights
#print axioms ThresholdHC.StoppingProgram.flow_output_zero_of_stop_zero
#print axioms ThresholdHC.StoppingProgram.flow_potential_bound
#print axioms ThresholdHC.StoppingProgram.flow_stop_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_total_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_work_ge_intensity
#print axioms ThresholdHC.StoppingProgram.flow_work_stopping_depth
#print axioms ThresholdHC.StoppingProgram.flow_zero_intensity
#print axioms ThresholdHC.StoppingProgram.forcedBellman
#print axioms ThresholdHC.StoppingProgram.forcedBellman_continue
#print axioms ThresholdHC.StoppingProgram.forcedBellman_recursion
#print axioms ThresholdHC.StoppingProgram.forcedBellman_stop
#print axioms ThresholdHC.StoppingProgram.four_prior_multipliers
#print axioms ThresholdHC.StoppingProgram.fullCapFlow
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_cone
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_intensity
#print axioms ThresholdHC.StoppingProgram.fullCap_arrayAt
#print axioms ThresholdHC.StoppingProgram.functionMomentImage
#print axioms ThresholdHC.StoppingProgram.functionMomentImage_compact_convex
#print axioms ThresholdHC.StoppingProgram.functionMomentImage_nonempty
#print axioms ThresholdHC.StoppingProgram.gap_tape_prefix_real
#print axioms ThresholdHC.StoppingProgram.headCountMass
#print axioms ThresholdHC.StoppingProgram.headCountMass_add
#print axioms ThresholdHC.StoppingProgram.headCountMass_nonneg
#print axioms ThresholdHC.StoppingProgram.headCountMass_outside
#print axioms ThresholdHC.StoppingProgram.headCountMass_snoc
#print axioms ThresholdHC.StoppingProgram.independent_decision_factor
#print axioms ThresholdHC.StoppingProgram.informationRatio
#print axioms ThresholdHC.StoppingProgram.informationRatio_bellman_attained
#print axioms ThresholdHC.StoppingProgram.informationRatio_bellman_zero
#print axioms ThresholdHC.StoppingProgram.informationRatio_finite_iff
#print axioms ThresholdHC.StoppingProgram.informationRatio_finite_of_statewise
#print axioms ThresholdHC.StoppingProgram.informationRatio_le_bellmanRatio
#print axioms ThresholdHC.StoppingProgram.informationRatio_top_iff
#print axioms ThresholdHC.StoppingProgram.integrable_count_mixture
#print axioms ThresholdHC.StoppingProgram.integrable_orderedContinueIndicator
#print axioms ThresholdHC.StoppingProgram.integrable_orderedStopIndicator
#print axioms ThresholdHC.StoppingProgram.integrable_overlapDensity
#print axioms ThresholdHC.StoppingProgram.integrable_prior_function
#print axioms ThresholdHC.StoppingProgram.intensity
#print axioms ThresholdHC.StoppingProgram.intensity_scale
#print axioms ThresholdHC.StoppingProgram.joinDecision
#print axioms ThresholdHC.StoppingProgram.joinDecision_other
#print axioms ThresholdHC.StoppingProgram.joinDecision_self
#print axioms ThresholdHC.StoppingProgram.joinDecision_update
#print axioms ThresholdHC.StoppingProgram.le_compactMaximum
#print axioms ThresholdHC.StoppingProgram.le_priceValue
#print axioms ThresholdHC.StoppingProgram.le_ratioValue
#print axioms ThresholdHC.StoppingProgram.linear_lower_bound_forces_zero
#print axioms ThresholdHC.StoppingProgram.linear_pi_expansion
#print axioms ThresholdHC.StoppingProgram.linear_ray_lower_bound_forces_nonneg
#print axioms ThresholdHC.StoppingProgram.measurable_completedStop
#print axioms ThresholdHC.StoppingProgram.measurable_orderedContinueIndicator
#print axioms ThresholdHC.StoppingProgram.measurable_orderedStopIndicator
#print axioms ThresholdHC.StoppingProgram.measurable_overlapDensity
#print axioms ThresholdHC.StoppingProgram.midpointFourPriors
#print axioms ThresholdHC.StoppingProgram.midpointFourPriors_admissible
#print axioms ThresholdHC.StoppingProgram.midpointPrior
#print axioms ThresholdHC.StoppingProgram.midpointPrior_comm
#print axioms ThresholdHC.StoppingProgram.midpointPrior_countCoefficient
#print axioms ThresholdHC.StoppingProgram.midpointPrior_mean
#print axioms ThresholdHC.StoppingProgram.midpointSquared
#print axioms ThresholdHC.StoppingProgram.midpointSquared_le_dualValue
#print axioms ThresholdHC.StoppingProgram.midpointValue
#print axioms ThresholdHC.StoppingProgram.midpoint_comparison
#print axioms ThresholdHC.StoppingProgram.midpoint_dual_root
#print axioms ThresholdHC.StoppingProgram.midpoint_informationRatio_finite
#print axioms ThresholdHC.StoppingProgram.midpoint_prefixCoefficient
#print axioms ThresholdHC.StoppingProgram.midpoint_prefixInformation_finite
#print axioms ThresholdHC.StoppingProgram.midpoint_prefixReward
#print axioms ThresholdHC.StoppingProgram.midpoint_quadratic_hellinger
#print axioms ThresholdHC.StoppingProgram.mixPrior
#print axioms ThresholdHC.StoppingProgram.mixPrior_countCoefficient
#print axioms ThresholdHC.StoppingProgram.mixPrior_integral
#print axioms ThresholdHC.StoppingProgram.mixPrior_mean
#print axioms ThresholdHC.StoppingProgram.mixPrior_rare
#print axioms ThresholdHC.StoppingProgram.mixture_arrival_continue
#print axioms ThresholdHC.StoppingProgram.mixture_arrival_stop
#print axioms ThresholdHC.StoppingProgram.mixture_policyArrival
#print axioms ThresholdHC.StoppingProgram.momentCoordinateBound
#print axioms ThresholdHC.StoppingProgram.normalizedRawFlow
#print axioms ThresholdHC.StoppingProgram.normalizedRawFlow_cone
#print axioms ThresholdHC.StoppingProgram.normalizedRawFlow_intensity
#print axioms ThresholdHC.StoppingProgram.normalized_flow
#print axioms ThresholdHC.StoppingProgram.nullPruned_points_closed
#print axioms ThresholdHC.StoppingProgram.observable_prefix_information
#print axioms ThresholdHC.StoppingProgram.observable_prefix_information_budget
#print axioms ThresholdHC.StoppingProgram.observable_prefix_risk
#print axioms ThresholdHC.StoppingProgram.offsetCoordinateBound
#print axioms ThresholdHC.StoppingProgram.optimalTree
#print axioms ThresholdHC.StoppingProgram.optimalTree_score
#print axioms ThresholdHC.StoppingProgram.optimizedOutput
#print axioms ThresholdHC.StoppingProgram.optimizedOutput_cone
#print axioms ThresholdHC.StoppingProgram.optimizedOutput_lagrange
#print axioms ThresholdHC.StoppingProgram.optimized_perspective_identity
#print axioms ThresholdHC.StoppingProgram.orderedContinueIndicator
#print axioms ThresholdHC.StoppingProgram.orderedContinueMass
#print axioms ThresholdHC.StoppingProgram.orderedCountContinue
#print axioms ThresholdHC.StoppingProgram.orderedCountStop
#print axioms ThresholdHC.StoppingProgram.orderedFlow
#print axioms ThresholdHC.StoppingProgram.orderedFlow_actual_work
#print axioms ThresholdHC.StoppingProgram.orderedFlow_cone
#print axioms ThresholdHC.StoppingProgram.orderedFlow_information
#print axioms ThresholdHC.StoppingProgram.orderedFlow_midpoint_hellinger
#print axioms ThresholdHC.StoppingProgram.orderedFlow_stopped_rewards
#print axioms ThresholdHC.StoppingProgram.orderedFlow_work_moment
#print axioms ThresholdHC.StoppingProgram.orderedStopIndicator
#print axioms ThresholdHC.StoppingProgram.orderedStopMass
#print axioms ThresholdHC.StoppingProgram.orderedStopMass_eq
#print axioms ThresholdHC.StoppingProgram.ordered_indicator_bounds
#print axioms ThresholdHC.StoppingProgram.ordered_indicator_conservation
#print axioms ThresholdHC.StoppingProgram.ordered_indicator_terminal
#print axioms ThresholdHC.StoppingProgram.ordered_mass_conservation
#print axioms ThresholdHC.StoppingProgram.ordered_stopped_hellinger_work
#print axioms ThresholdHC.StoppingProgram.original_stopped_word_affinity
#print axioms ThresholdHC.StoppingProgram.original_stopped_word_integral
#print axioms ThresholdHC.StoppingProgram.original_stopped_word_mass
#print axioms ThresholdHC.StoppingProgram.original_work_stopped_integral
#print axioms ThresholdHC.StoppingProgram.outputCoordinateBound
#print axioms ThresholdHC.StoppingProgram.overlapDensity
#print axioms ThresholdHC.StoppingProgram.overlapDensity_le_one
#print axioms ThresholdHC.StoppingProgram.overlapDensity_nonneg
#print axioms ThresholdHC.StoppingProgram.pascal_weights_sum
#print axioms ThresholdHC.StoppingProgram.perspective
#print axioms ThresholdHC.StoppingProgram.perspectiveCone_add
#print axioms ThresholdHC.StoppingProgram.perspective_add_le
#print axioms ThresholdHC.StoppingProgram.perspective_antitone_reference
#print axioms ThresholdHC.StoppingProgram.perspective_cone_attains
#print axioms ThresholdHC.StoppingProgram.perspective_cone_lower
#print axioms ThresholdHC.StoppingProgram.perspective_cone_lower_toReal
#print axioms ThresholdHC.StoppingProgram.perspective_finite_iff
#print axioms ThresholdHC.StoppingProgram.perspective_nonzero_zero
#print axioms ThresholdHC.StoppingProgram.perspective_pos
#print axioms ThresholdHC.StoppingProgram.perspective_scale
#print axioms ThresholdHC.StoppingProgram.perspective_scale_contrast
#print axioms ThresholdHC.StoppingProgram.perspective_toReal_eq
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
#print axioms ThresholdHC.StoppingProgram.policyArrival
#print axioms ThresholdHC.StoppingProgram.policyArrival_congr_before
#print axioms ThresholdHC.StoppingProgram.policyArrival_eq_raw
#print axioms ThresholdHC.StoppingProgram.policyArrival_nonneg
#print axioms ThresholdHC.StoppingProgram.policyArrival_outside
#print axioms ThresholdHC.StoppingProgram.policyFlow
#print axioms ThresholdHC.StoppingProgram.policyFlow_cone
#print axioms ThresholdHC.StoppingProgram.policyFlow_intensity
#print axioms ThresholdHC.StoppingProgram.policy_weights_realize_flow
#print axioms ThresholdHC.StoppingProgram.population_prefix_integrable
#print axioms ThresholdHC.StoppingProgram.population_prefix_integral
#print axioms ThresholdHC.StoppingProgram.population_tape_prefix_real
#print axioms ThresholdHC.StoppingProgram.population_word_integral
#print axioms ThresholdHC.StoppingProgram.positive_decision_one
#print axioms ThresholdHC.StoppingProgram.positive_decision_zero
#print axioms ThresholdHC.StoppingProgram.positive_dual_witness
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient_add
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient_nonneg
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient_root
#print axioms ThresholdHC.StoppingProgram.prefixInformation
#print axioms ThresholdHC.StoppingProgram.prefixInformation_children
#print axioms ThresholdHC.StoppingProgram.prefixInformation_finite_of_ratio
#print axioms ThresholdHC.StoppingProgram.prefixInformation_finite_of_terminal
#print axioms ThresholdHC.StoppingProgram.prefixInformation_root
#print axioms ThresholdHC.StoppingProgram.prefixInformation_top_iff
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood_add
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood_nonneg
#print axioms ThresholdHC.StoppingProgram.prefixReward
#print axioms ThresholdHC.StoppingProgram.prefix_pair_modulus
#print axioms ThresholdHC.StoppingProgram.prefix_program_bound
#print axioms ThresholdHC.StoppingProgram.priceValue
#print axioms ThresholdHC.StoppingProgram.priceValue_at_ratio
#print axioms ThresholdHC.StoppingProgram.priceValue_attained
#print axioms ThresholdHC.StoppingProgram.priceValue_le_zero_iff
#print axioms ThresholdHC.StoppingProgram.priceValue_strictAnti
#print axioms ThresholdHC.StoppingProgram.priceValue_zero_iff
#print axioms ThresholdHC.StoppingProgram.priorCoordinates
#print axioms ThresholdHC.StoppingProgram.priorMomentImage
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_compact_convex
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_mem
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_nonempty
#print axioms ThresholdHC.StoppingProgram.priorTupleSet
#print axioms ThresholdHC.StoppingProgram.prior_function_le_rareFunctional
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
#print axioms ThresholdHC.StoppingProgram.randomized_price_le
#print axioms ThresholdHC.StoppingProgram.rareFunctional
#print axioms ThresholdHC.StoppingProgram.rareFunctional_attained
#print axioms ThresholdHC.StoppingProgram.rareMomentSet
#print axioms ThresholdHC.StoppingProgram.rareMomentSet_compact_convex
#print axioms ThresholdHC.StoppingProgram.rareMomentSet_eq_half_image
#print axioms ThresholdHC.StoppingProgram.ratioValue
#print axioms ThresholdHC.StoppingProgram.ratioValue_attained
#print axioms ThresholdHC.StoppingProgram.ratioValue_nonneg
#print axioms ThresholdHC.StoppingProgram.rawArray
#print axioms ThresholdHC.StoppingProgram.rawArray_nonneg
#print axioms ThresholdHC.StoppingProgram.rawArray_outside
#print axioms ThresholdHC.StoppingProgram.rawArray_terminal
#print axioms ThresholdHC.StoppingProgram.rawChildren
#print axioms ThresholdHC.StoppingProgram.rawFlowScore
#print axioms ThresholdHC.StoppingProgram.rawLayer
#print axioms ThresholdHC.StoppingProgram.rawLayer_countMean
#print axioms ThresholdHC.StoppingProgram.rawLayer_depth_weight
#print axioms ThresholdHC.StoppingProgram.rawLayer_mul_depth
#print axioms ThresholdHC.StoppingProgram.raw_continue_fraction
#print axioms ThresholdHC.StoppingProgram.raw_flow_recursion
#print axioms ThresholdHC.StoppingProgram.raw_layer_conservation
#print axioms ThresholdHC.StoppingProgram.raw_normalizedRawFlow_continue
#print axioms ThresholdHC.StoppingProgram.raw_normalizedRawFlow_stop
#print axioms ThresholdHC.StoppingProgram.raw_policyFlow_continue
#print axioms ThresholdHC.StoppingProgram.raw_policyFlow_stop
#print axioms ThresholdHC.StoppingProgram.raw_root_total
#print axioms ThresholdHC.StoppingProgram.raw_stop_fraction
#print axioms ThresholdHC.StoppingProgram.raw_weighted_telescope
#print axioms ThresholdHC.StoppingProgram.robustResidual
#print axioms ThresholdHC.StoppingProgram.robustResidual_convex
#print axioms ThresholdHC.StoppingProgram.robustResidual_nonpos_iff
#print axioms ThresholdHC.StoppingProgram.rootBellman
#print axioms ThresholdHC.StoppingProgram.rootBellman_eq_priceValue
#print axioms ThresholdHC.StoppingProgram.rootBellman_maximum
#print axioms ThresholdHC.StoppingProgram.rootBellman_strictAnti
#print axioms ThresholdHC.StoppingProgram.rootBellman_zero_iff
#print axioms ThresholdHC.StoppingProgram.rootInformation
#print axioms ThresholdHC.StoppingProgram.rootState
#print axioms ThresholdHC.StoppingProgram.rootWork
#print axioms ThresholdHC.StoppingProgram.rootWork_bounds
#print axioms ThresholdHC.StoppingProgram.scaleFlow
#print axioms ThresholdHC.StoppingProgram.shortWord
#print axioms ThresholdHC.StoppingProgram.shortWord_self
#print axioms ThresholdHC.StoppingProgram.shortWord_snoc
#print axioms ThresholdHC.StoppingProgram.shortWord_tapePrefix
#print axioms ThresholdHC.StoppingProgram.singleOutput
#print axioms ThresholdHC.StoppingProgram.singleOutput_cone
#print axioms ThresholdHC.StoppingProgram.squared_loss_overlap_integral
#print axioms ThresholdHC.StoppingProgram.state_eq_root
#print axioms ThresholdHC.StoppingProgram.stopTree_fintype
#print axioms ThresholdHC.StoppingProgram.stopTree_nonempty
#print axioms ThresholdHC.StoppingProgram.stoppedHellinger
#print axioms ThresholdHC.StoppingProgram.stoppedHellinger_squares
#print axioms ThresholdHC.StoppingProgram.stoppedReferenceSum
#print axioms ThresholdHC.StoppingProgram.stoppedReferenceSum_total
#print axioms ThresholdHC.StoppingProgram.strong_four_prior_duality
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
#print axioms ThresholdHC.StoppingProgram.treeInformation
#print axioms ThresholdHC.StoppingProgram.treeInformation_nonneg
#print axioms ThresholdHC.StoppingProgram.treeScore
#print axioms ThresholdHC.StoppingProgram.treeScore_eq
#print axioms ThresholdHC.StoppingProgram.treeScore_le_bellman
#print axioms ThresholdHC.StoppingProgram.treeWork
#print axioms ThresholdHC.StoppingProgram.treeWork_le
#print axioms ThresholdHC.StoppingProgram.treeWork_nonneg
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian_concave
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian_continuous_point
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian_continuous_prior
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian_convex
#print axioms ThresholdHC.StoppingProgram.tuple_multipliers
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
