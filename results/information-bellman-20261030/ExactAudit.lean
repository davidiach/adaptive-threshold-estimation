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
import ThresholdHC.StoppingProgram.PolicyFlow
import ThresholdHC.StoppingProgram.Bellman
import ThresholdHC.StoppingProgram.FlowPotential
import ThresholdHC.StoppingProgram.BellmanFlow
import ThresholdHC.StoppingProgram.PrefixInformation
import ThresholdHC.StoppingProgram.PriceRatio
import ThresholdHC.StoppingProgram.InformationBellman
import ThresholdHC.StoppingProgram.FlowOperations
import ThresholdHC.StoppingProgram.InformationBound
import ThresholdHC.StoppingProgram.InformationFiniteness
import ThresholdHC.StoppingProgram.InformationIncrement
import ThresholdHC.StoppingProgram.BellmanTheorem

open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    0 < N → informationRatio μ N Q ≠ ⊤ →
    informationRatio μ N Q = ENNReal.ofReal (bellmanRatio μ N Q) ∧
    (∀ κ : ℝ, rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work) κ (N-1) = 0 ↔
      κ = (informationRatio μ N Q).toReal) ∧
    ∃ p : ℕ → ℕ → ℝ, (∀ n k, p n k = 0 ∨ p n k = 1) ∧ p 0 0 = 0 ∧
      (∀ k, k ≤ N → p N k = 1) ∧ FlowCone (policyFlow N p) ∧ intensity (policyFlow N p) = 1 ∧
      flowInformation μ Q (policyFlow N p)/
        ENNReal.ofReal (countMean μ Q.work (policyFlow N p).continueWeight) = informationRatio μ N Q :=
  informationRatio_bellman
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors), 0 < N →
    (informationRatio μ N Q = ⊤ ↔ ∃ n k, n ≤ N ∧ k ≤ n ∧
      prefixCoefficient μ Q.variance n k = 0 ∧
      prefixCoefficient μ Q.high n k ≠ prefixCoefficient μ Q.low n k) := informationRatio_top_iff
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    0 < N → informationRatio μ N Q ≠ ⊤ → ∀ f : Flow N, FlowCone f →
    (∀ n k, n < N → k ≤ n → 0 ≤ informationIncrement μ Q n k) ∧
    (flowInformation μ Q f).toReal = ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n+1),
      rawArray f.continueWeight n k*informationIncrement μ Q n k := informationRatio_increment_identity
example : ∀ (μ : Measure Gap) (N : ℕ) (Q : FourPriors),
    Continuous (fun κ => rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work) κ (N-1)) ∧
    StrictAnti (fun κ => rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work) κ (N-1)) := by
  intro μ N Q
  exact ⟨continuous_rootBellman _ _ _,rootBellman_strictAnti _ _ (prefixCoefficient_nonneg μ Q.work) _⟩
example : ∀ (r w : ℕ → ℕ → ℝ) (κ : ℝ) {N : ℕ}, 0 < N → w 0 0 = 1 →
    (∀ f : Flow N, FlowCone f → intensity f = 1 → rawFlowScore f r w κ ≤ rootBellman r w κ (N-1)) ∧
    ∃ f : Flow N, FlowCone f ∧ intensity f = 1 ∧ rawFlowScore f r w κ = rootBellman r w κ (N-1) :=
  flowScore_maximum

#print axioms ThresholdHC.StoppingProgram.Admissible
#print axioms ThresholdHC.StoppingProgram.Certificate
#print axioms ThresholdHC.StoppingProgram.CountState
#print axioms ThresholdHC.StoppingProgram.Feasible
#print axioms ThresholdHC.StoppingProgram.Flow
#print axioms ThresholdHC.StoppingProgram.FlowCone
#print axioms ThresholdHC.StoppingProgram.FlowCone.add
#print axioms ThresholdHC.StoppingProgram.FlowCone.scale
#print axioms ThresholdHC.StoppingProgram.FourPriors
#print axioms ThresholdHC.StoppingProgram.StopTree
#print axioms ThresholdHC.StoppingProgram.addFlow
#print axioms ThresholdHC.StoppingProgram.arrayAt
#print axioms ThresholdHC.StoppingProgram.arrayAt_add_flow
#print axioms ThresholdHC.StoppingProgram.arrayAt_le_of
#print axioms ThresholdHC.StoppingProgram.arrayAt_nonneg
#print axioms ThresholdHC.StoppingProgram.arrayAt_scale_flow
#print axioms ThresholdHC.StoppingProgram.arrayAt_state
#print axioms ThresholdHC.StoppingProgram.arrayAt_zero
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
#print axioms ThresholdHC.StoppingProgram.certificateSquared
#print axioms ThresholdHC.StoppingProgram.choose_pascal_high
#print axioms ThresholdHC.StoppingProgram.choose_pascal_low
#print axioms ThresholdHC.StoppingProgram.constantCertificate
#print axioms ThresholdHC.StoppingProgram.constantCertificate_feasible
#print axioms ThresholdHC.StoppingProgram.continuous_bellman
#print axioms ThresholdHC.StoppingProgram.continuous_rootBellman
#print axioms ThresholdHC.StoppingProgram.countCoefficient
#print axioms ThresholdHC.StoppingProgram.countCoefficient_nonneg
#print axioms ThresholdHC.StoppingProgram.countCoefficient_root
#print axioms ThresholdHC.StoppingProgram.countInformation_eq
#print axioms ThresholdHC.StoppingProgram.countMean
#print axioms ThresholdHC.StoppingProgram.countMean_ge_root
#print axioms ThresholdHC.StoppingProgram.countMean_nonneg
#print axioms ThresholdHC.StoppingProgram.countMean_raw
#print axioms ThresholdHC.StoppingProgram.countMean_scale
#print axioms ThresholdHC.StoppingProgram.countMean_stop_eq_intensity
#print axioms ThresholdHC.StoppingProgram.countStopProbability
#print axioms ThresholdHC.StoppingProgram.countStopProbability_bounds
#print axioms ThresholdHC.StoppingProgram.countStopProbability_root
#print axioms ThresholdHC.StoppingProgram.dualRatio
#print axioms ThresholdHC.StoppingProgram.dualValue
#print axioms ThresholdHC.StoppingProgram.flowInformation
#print axioms ThresholdHC.StoppingProgram.flowInformation_finite_of_ratio_finite
#print axioms ThresholdHC.StoppingProgram.flowInformation_finite_prefixes
#print axioms ThresholdHC.StoppingProgram.flowInformation_increments
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
#print axioms ThresholdHC.StoppingProgram.flow_continue_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_output_zero_of_stop_zero
#print axioms ThresholdHC.StoppingProgram.flow_potential_bound
#print axioms ThresholdHC.StoppingProgram.flow_stop_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_total_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_work_ge_intensity
#print axioms ThresholdHC.StoppingProgram.flow_zero_intensity
#print axioms ThresholdHC.StoppingProgram.forcedBellman
#print axioms ThresholdHC.StoppingProgram.forcedBellman_continue
#print axioms ThresholdHC.StoppingProgram.forcedBellman_recursion
#print axioms ThresholdHC.StoppingProgram.forcedBellman_stop
#print axioms ThresholdHC.StoppingProgram.fullCapFlow
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_cone
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_intensity
#print axioms ThresholdHC.StoppingProgram.fullCap_arrayAt
#print axioms ThresholdHC.StoppingProgram.informationIncrement
#print axioms ThresholdHC.StoppingProgram.informationIncrement_nonneg
#print axioms ThresholdHC.StoppingProgram.informationRatio
#print axioms ThresholdHC.StoppingProgram.informationRatio_bellman
#print axioms ThresholdHC.StoppingProgram.informationRatio_bellman_attained
#print axioms ThresholdHC.StoppingProgram.informationRatio_bellman_zero
#print axioms ThresholdHC.StoppingProgram.informationRatio_finite_iff
#print axioms ThresholdHC.StoppingProgram.informationRatio_increment_identity
#print axioms ThresholdHC.StoppingProgram.informationRatio_le_bellmanRatio
#print axioms ThresholdHC.StoppingProgram.informationRatio_top_iff
#print axioms ThresholdHC.StoppingProgram.intensity
#print axioms ThresholdHC.StoppingProgram.intensity_scale
#print axioms ThresholdHC.StoppingProgram.le_priceValue
#print axioms ThresholdHC.StoppingProgram.le_ratioValue
#print axioms ThresholdHC.StoppingProgram.normalized_flow
#print axioms ThresholdHC.StoppingProgram.optimalTree
#print axioms ThresholdHC.StoppingProgram.optimalTree_score
#print axioms ThresholdHC.StoppingProgram.pascal_weights_sum
#print axioms ThresholdHC.StoppingProgram.perspective
#print axioms ThresholdHC.StoppingProgram.perspectiveCone_add
#print axioms ThresholdHC.StoppingProgram.perspective_add_le
#print axioms ThresholdHC.StoppingProgram.perspective_cone_attains
#print axioms ThresholdHC.StoppingProgram.perspective_cone_lower
#print axioms ThresholdHC.StoppingProgram.perspective_finite_iff
#print axioms ThresholdHC.StoppingProgram.perspective_nonzero_zero
#print axioms ThresholdHC.StoppingProgram.perspective_pos
#print axioms ThresholdHC.StoppingProgram.perspective_scale
#print axioms ThresholdHC.StoppingProgram.perspective_zero_zero
#print axioms ThresholdHC.StoppingProgram.policyArrival
#print axioms ThresholdHC.StoppingProgram.policyArrival_eq_raw
#print axioms ThresholdHC.StoppingProgram.policyArrival_nonneg
#print axioms ThresholdHC.StoppingProgram.policyArrival_outside
#print axioms ThresholdHC.StoppingProgram.policyFlow
#print axioms ThresholdHC.StoppingProgram.policyFlow_cone
#print axioms ThresholdHC.StoppingProgram.policyFlow_intensity
#print axioms ThresholdHC.StoppingProgram.policy_weights_realize_flow
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
#print axioms ThresholdHC.StoppingProgram.priceValue
#print axioms ThresholdHC.StoppingProgram.priceValue_at_ratio
#print axioms ThresholdHC.StoppingProgram.priceValue_attained
#print axioms ThresholdHC.StoppingProgram.priceValue_le_zero_iff
#print axioms ThresholdHC.StoppingProgram.priceValue_strictAnti
#print axioms ThresholdHC.StoppingProgram.priceValue_zero_iff
#print axioms ThresholdHC.StoppingProgram.programSquared
#print axioms ThresholdHC.StoppingProgram.programSquared_finite
#print axioms ThresholdHC.StoppingProgram.programSquared_le_constant
#print axioms ThresholdHC.StoppingProgram.programValue
#print axioms ThresholdHC.StoppingProgram.quadratic_div_add_le
#print axioms ThresholdHC.StoppingProgram.randomized_price_le
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
#print axioms ThresholdHC.StoppingProgram.raw_continue_fraction
#print axioms ThresholdHC.StoppingProgram.raw_flow_recursion
#print axioms ThresholdHC.StoppingProgram.raw_layer_conservation
#print axioms ThresholdHC.StoppingProgram.raw_policyFlow_continue
#print axioms ThresholdHC.StoppingProgram.raw_policyFlow_stop
#print axioms ThresholdHC.StoppingProgram.raw_root_total
#print axioms ThresholdHC.StoppingProgram.raw_stop_fraction
#print axioms ThresholdHC.StoppingProgram.raw_weighted_telescope
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
#print axioms ThresholdHC.StoppingProgram.state_eq_root
#print axioms ThresholdHC.StoppingProgram.stopTree_fintype
#print axioms ThresholdHC.StoppingProgram.stopTree_nonempty
#print axioms ThresholdHC.StoppingProgram.treeInformation
#print axioms ThresholdHC.StoppingProgram.treeInformation_nonneg
#print axioms ThresholdHC.StoppingProgram.treeScore
#print axioms ThresholdHC.StoppingProgram.treeScore_eq
#print axioms ThresholdHC.StoppingProgram.treeScore_le_bellman
#print axioms ThresholdHC.StoppingProgram.treeWork
#print axioms ThresholdHC.StoppingProgram.treeWork_le
#print axioms ThresholdHC.StoppingProgram.treeWork_nonneg
#print axioms ThresholdHC.StoppingProgram.zeroFlow
#print axioms ThresholdHC.StoppingProgram.zeroFlow_cone
