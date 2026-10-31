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
import ThresholdHC.StoppingProgram.Bellman
import ThresholdHC.StoppingProgram.FlowPotential
import ThresholdHC.StoppingProgram.TableCall

open MeasureTheory
open scoped BigOperators
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)
example : ∀ {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (f : Flow N),
    FlowCone f → countMean μ q f.stopWeight = intensity f := countMean_stop_eq_intensity
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → ∀ (r w : ℕ → ℕ → ℝ) (κ : ℝ), w 0 0 = 1 →
    (∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1),
      (rawArray f.stopWeight n k*r n k-κ*rawArray f.continueWeight n k*w n k)) ≤
        intensity f*rootBellman r w κ (N-1) := flowScore_le_rootBellman
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → ∀ s : CountState N,
    (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b*
      (policyArrival (intensity f) (countDecision b) s.1.val s.2.val*countDecision b s.1.val s.2.val)) =
        rawArray f.stopWeight s.1.val s.2.val ∧
    (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b*
      (policyArrival (intensity f) (countDecision b) s.1.val s.2.val*(1-countDecision b s.1.val s.2.val))) =
        rawArray f.continueWeight s.1.val s.2.val := flow_mixture_weights
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → 0 < N →
    (∀ b, 0 ≤ decisionWeight (flowDecisionParameters f) b) ∧
    (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b) = 1 ∧
    ∀ b : CountState N → Bool, 0 < decisionWeight (flowDecisionParameters f) b →
      b (rootState N) = false ∧ ∀ s : CountState N, s.1.val = N → b s = true := by
  intro N f hf hN
  exact ⟨(flow_mixture_probability f hf).1,(flow_mixture_probability f hf).2,
    fun b hb => flow_mixture_supported_tables f hf hN b hb⟩
example : ∀ {N : ℕ} (hN : 0 < N) (b : CountState N → Bool) (y : CountState N → ℝ),
    ∀ ω : ℕ → Bool, (tableCall hN b y).cost ω ≤ N ∧
      (tableCall hN b y).value ω = y (tableStoppedState b ω) ∧
      ‖(tableCall hN b y).value ω‖ ≤ ∑ s, ‖y s‖ := by
  intro N hN b y ω
  exact ⟨tableCall_cost_le hN b y ω,tableValue_eq b y ω,tableValue_bounded b y ω⟩

#print axioms ThresholdHC.StoppingProgram.Admissible
#print axioms ThresholdHC.StoppingProgram.Certificate
#print axioms ThresholdHC.StoppingProgram.CountState
#print axioms ThresholdHC.StoppingProgram.Feasible
#print axioms ThresholdHC.StoppingProgram.Flow
#print axioms ThresholdHC.StoppingProgram.FlowCone
#print axioms ThresholdHC.StoppingProgram.FourPriors
#print axioms ThresholdHC.StoppingProgram.StopTree
#print axioms ThresholdHC.StoppingProgram.arrayAt
#print axioms ThresholdHC.StoppingProgram.arrayAt_le_of
#print axioms ThresholdHC.StoppingProgram.arrayAt_nonneg
#print axioms ThresholdHC.StoppingProgram.arrayAt_state
#print axioms ThresholdHC.StoppingProgram.arrayAt_zero
#print axioms ThresholdHC.StoppingProgram.arrival_independent_current
#print axioms ThresholdHC.StoppingProgram.bellman
#print axioms ThresholdHC.StoppingProgram.boundedFirst_eq_iff
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
#print axioms ThresholdHC.StoppingProgram.countDecision
#print axioms ThresholdHC.StoppingProgram.countDecision_state
#print axioms ThresholdHC.StoppingProgram.countMean
#print axioms ThresholdHC.StoppingProgram.countMean_ge_root
#print axioms ThresholdHC.StoppingProgram.countMean_nonneg
#print axioms ThresholdHC.StoppingProgram.countMean_raw
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
#print axioms ThresholdHC.StoppingProgram.dualValue
#print axioms ThresholdHC.StoppingProgram.flowDecisionParameters
#print axioms ThresholdHC.StoppingProgram.flowDecisionParameters_before
#print axioms ThresholdHC.StoppingProgram.flowInformation
#print axioms ThresholdHC.StoppingProgram.flowScore_le_rootBellman
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
#print axioms ThresholdHC.StoppingProgram.flow_zero_intensity
#print axioms ThresholdHC.StoppingProgram.forcedBellman
#print axioms ThresholdHC.StoppingProgram.forcedBellman_continue
#print axioms ThresholdHC.StoppingProgram.forcedBellman_stop
#print axioms ThresholdHC.StoppingProgram.fullCapFlow
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_cone
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_intensity
#print axioms ThresholdHC.StoppingProgram.fullCap_arrayAt
#print axioms ThresholdHC.StoppingProgram.independent_decision_factor
#print axioms ThresholdHC.StoppingProgram.informationRatio
#print axioms ThresholdHC.StoppingProgram.intensity
#print axioms ThresholdHC.StoppingProgram.joinDecision
#print axioms ThresholdHC.StoppingProgram.joinDecision_other
#print axioms ThresholdHC.StoppingProgram.joinDecision_self
#print axioms ThresholdHC.StoppingProgram.joinDecision_update
#print axioms ThresholdHC.StoppingProgram.mixture_arrival_continue
#print axioms ThresholdHC.StoppingProgram.mixture_arrival_stop
#print axioms ThresholdHC.StoppingProgram.mixture_policyArrival
#print axioms ThresholdHC.StoppingProgram.optimalTree
#print axioms ThresholdHC.StoppingProgram.optimalTree_score
#print axioms ThresholdHC.StoppingProgram.pascal_weights_sum
#print axioms ThresholdHC.StoppingProgram.perspective
#print axioms ThresholdHC.StoppingProgram.perspective_add_le
#print axioms ThresholdHC.StoppingProgram.perspective_cone_attains
#print axioms ThresholdHC.StoppingProgram.perspective_cone_lower
#print axioms ThresholdHC.StoppingProgram.perspective_finite_iff
#print axioms ThresholdHC.StoppingProgram.perspective_nonzero_zero
#print axioms ThresholdHC.StoppingProgram.perspective_pos
#print axioms ThresholdHC.StoppingProgram.perspective_scale
#print axioms ThresholdHC.StoppingProgram.perspective_zero_zero
#print axioms ThresholdHC.StoppingProgram.policyArrival
#print axioms ThresholdHC.StoppingProgram.policyArrival_congr_before
#print axioms ThresholdHC.StoppingProgram.policyArrival_eq_raw
#print axioms ThresholdHC.StoppingProgram.policyArrival_outside
#print axioms ThresholdHC.StoppingProgram.policy_weights_realize_flow
#print axioms ThresholdHC.StoppingProgram.positive_decision_one
#print axioms ThresholdHC.StoppingProgram.positive_decision_zero
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient_add
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient_nonneg
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient_root
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood_add
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood_nonneg
#print axioms ThresholdHC.StoppingProgram.programSquared
#print axioms ThresholdHC.StoppingProgram.programSquared_finite
#print axioms ThresholdHC.StoppingProgram.programSquared_le_constant
#print axioms ThresholdHC.StoppingProgram.programValue
#print axioms ThresholdHC.StoppingProgram.quadratic_div_add_le
#print axioms ThresholdHC.StoppingProgram.rareMomentSet
#print axioms ThresholdHC.StoppingProgram.rareMomentSet_compact_convex
#print axioms ThresholdHC.StoppingProgram.rareMomentSet_eq_half_image
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
#print axioms ThresholdHC.StoppingProgram.raw_root_total
#print axioms ThresholdHC.StoppingProgram.raw_stop_fraction
#print axioms ThresholdHC.StoppingProgram.raw_weighted_telescope
#print axioms ThresholdHC.StoppingProgram.rootBellman
#print axioms ThresholdHC.StoppingProgram.rootBellman_maximum
#print axioms ThresholdHC.StoppingProgram.rootInformation
#print axioms ThresholdHC.StoppingProgram.rootState
#print axioms ThresholdHC.StoppingProgram.rootWork
#print axioms ThresholdHC.StoppingProgram.rootWork_bounds
#print axioms ThresholdHC.StoppingProgram.state_eq_root
#print axioms ThresholdHC.StoppingProgram.stopTree_fintype
#print axioms ThresholdHC.StoppingProgram.stopTree_nonempty
#print axioms ThresholdHC.StoppingProgram.tableCall
#print axioms ThresholdHC.StoppingProgram.tableCall_cost_le
#print axioms ThresholdHC.StoppingProgram.tableCost
#print axioms ThresholdHC.StoppingProgram.tableCost_eq_iff
#print axioms ThresholdHC.StoppingProgram.tableCost_positive
#print axioms ThresholdHC.StoppingProgram.tableHit
#print axioms ThresholdHC.StoppingProgram.tableStoppedState
#print axioms ThresholdHC.StoppingProgram.tableValue
#print axioms ThresholdHC.StoppingProgram.tableValue_bounded
#print axioms ThresholdHC.StoppingProgram.tableValue_eq
#print axioms ThresholdHC.StoppingProgram.treeInformation
#print axioms ThresholdHC.StoppingProgram.treeScore
#print axioms ThresholdHC.StoppingProgram.treeScore_eq
#print axioms ThresholdHC.StoppingProgram.treeScore_le_bellman
#print axioms ThresholdHC.StoppingProgram.treeWork
#print axioms ThresholdHC.StoppingProgram.treeWork_le
#print axioms ThresholdHC.StoppingProgram.treeWork_nonneg
#print axioms ThresholdHC.StoppingProgram.wordHeads_le_length
#print axioms ThresholdHC.StoppingProgram.zeroFlow
#print axioms ThresholdHC.StoppingProgram.zeroFlow_cone
