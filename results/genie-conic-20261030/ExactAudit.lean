import ThresholdHC.Genie.DirectRiskOptimization
import ThresholdHC.Genie.Model
import ThresholdHC.Genie.InfiniteCoordinates
import ThresholdHC.Genie.PerspectiveTopology
import ThresholdHC.Genie.InformationTopology
import ThresholdHC.Genie.DualTopology
import ThresholdHC.Genie.CompactPriorDomain
import ThresholdHC.Genie.CompactDecreasingMaximum
import ThresholdHC.Genie.FlowExtension
import ThresholdHC.Genie.CapMonotonicity
import ThresholdHC.Genie.InfiniteDualLimit
import ThresholdHC.Genie.InfiniteComparison
import ThresholdHC.Genie.InfiniteDuality
import ThresholdHC.Genie.InfiniteMidpoint
import ThresholdHC.Genie.PerspectiveIntegral
import ThresholdHC.Genie.RevealReward
import ThresholdHC.Genie.ExtendedFlowConservation
import ThresholdHC.Genie.RevealProgram
import ThresholdHC.Genie.RevealFiniteness
import ThresholdHC.Genie.RevealBellman
import ThresholdHC.Genie.FlowTruncation
import ThresholdHC.Genie.RevealTruncation
import ThresholdHC.Genie.CapLimits
import ThresholdHC.Genie.DirectRisk
import ThresholdHC.Genie.FinitePriors
import ThresholdHC.Genie.FiniteReveal
import ThresholdHC.Genie.BellmanEnvelope
import ThresholdHC.Genie.FiniteConicEnvelope
import ThresholdHC.Genie.FiniteConicPrice
import ThresholdHC.Genie.ReferenceRegularization
import ThresholdHC.Genie.OptimizedBrackets
import ThresholdHC.Genie.ScalarPrice
import ThresholdHC.Genie.FiniteConicValue
import ThresholdHC.Genie.AtomConicModel
import ThresholdHC.Genie.AtomConicRealization

open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ t x : ℝ, 0 ≤ t → 0 ≤ x →
    IsGreatest ((directRiskProfile t x) '' Set.Icc (0:ℝ) 1)
      (directRiskProfile t x (directRiskScale x)) := directRiskProfile_greatest
example : ∀ t x : ℝ, 0 ≤ x →
    (directRiskProfile t x (directRiskScale x))^2 =
      if x ≤ 4/3 then t^2/4*(1-x/4)^2 else 4*t^2/(27*x) := directRiskProfile_square
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 ≤ ρ → 0 ≤ B →
    ∀ Q : FourPriors, Admissible μ ρ Q → signMean μ Q.low.val ≤ signMean μ Q.high.val →
    ∀ N : ℕ, 0 < N → ∀ κ : ℝ, 0 ≤ κ → genieInformationRatio μ N Q ≤ ENNReal.ofReal κ →
    ENNReal.ofReal (directRiskSquared ((signMean μ Q.high.val-signMean μ Q.low.val)/3) (B*κ)) ≤
      rareMinimaxRisk μ ρ B ^ 2 := genie_direct_squared_risk
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 ≤ ρ → 0 ≤ B →
    ∀ Q : FourPriors, Admissible μ ρ Q → signMean μ Q.low.val ≤ signMean μ Q.high.val →
    latentDivergence μ Q ≠ ⊤ → ∀ N : ℕ, 0 < N → ∀ κ : ℝ, 0 ≤ κ →
    rootBellman (genieReward μ Q N) (prefixCoefficient μ Q.work) κ (N-1) ≤ 0 →
    ENNReal.ofReal (directRiskSquared ((signMean μ Q.high.val-signMean μ Q.low.val)/3) (B*κ)) ≤
      rareMinimaxRisk μ ρ B ^ 2 := genie_bellman_direct_squared_risk
variable {I : Type*} [Fintype I]
example : ∀ (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 < w i) → μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) →
    ∀ Q : FourPriors, 0 < N → ∀ α η : ℝ, 0 < α → 0 ≤ η →
    ((∃ X rp rm, FiniteGenieCones (N := N) μ w d Q α η X rp rm) ↔
      genieInformationRatio μ N Q ≤ ENNReal.ofReal (4*η/α^2)) := finiteGenieCones_iff_price
example : ∀ (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 < w i) → μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) →
    ∀ B : ℝ, 0 < B → ∀ Q : FourPriors, 0 < N →
    ∃ (α η : ℝ) (X : CountState N → ℝ) (rp rm : I → ℝ), 0 ≤ α ∧ 0 ≤ η ∧
      FiniteGenieCones μ w d Q α η X rp rm ∧
      ENNReal.ofReal (α*(signMean μ Q.high.val-signMean μ Q.low.val)-α^2-η*B) = genieDualRatio μ B N Q :=
    finiteGenieCones_objective_attained
example : ∀ {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 ≤ w i) → μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) → Function.Injective d →
    ∀ ρ B : ℝ, 0 ≤ ρ → ∀ v : AtomConicPoint I N, AtomConicFeasible w d ρ v →
    ∃ Q : FourPriors, Admissible μ ρ Q ∧
      FiniteGenieCones μ w d Q v.scale v.price v.bellman v.revealPlus v.revealMinus ∧
      atomConicObjective w B v ≤ v.scale*(signMean μ Q.high.val-signMean μ Q.low.val)-v.scale^2-v.price*B :=
    atomConic_realization
example : ∀ (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 < w i) → μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) → Function.Injective d →
    ∀ ρ B : ℝ, 0 ≤ ρ → 0 < B → 0 < N →
    atomConicValue N w d ρ B = genieSquared μ ρ B N := atomConicValue_eq_genieSquared
example : ∀ (I : Type*) [Fintype I] (N : ℕ),
    atomConicVariableCount I N ≤ 3+6*Fintype.card I+(N+1)^2 := atomConicVariableCount_bound

#print axioms ThresholdHC.Genie.AllCountIndex
#print axioms ThresholdHC.Genie.AllFourCoordinates
#print axioms ThresholdHC.Genie.AtomBox
#print axioms ThresholdHC.Genie.AtomConicFeasible
#print axioms ThresholdHC.Genie.AtomConicPoint
#print axioms ThresholdHC.Genie.BellmanEnvelope
#print axioms ThresholdHC.Genie.FiniteGenieCones
#print axioms ThresholdHC.Genie.LatentCones
#print axioms ThresholdHC.Genie.PriorDomain
#print axioms ThresholdHC.Genie.absorbedPriors_infiniteDualRatio
#print axioms ThresholdHC.Genie.absorbedPriors_infiniteInformation_le
#print axioms ThresholdHC.Genie.allFourPriorCoordinates
#print axioms ThresholdHC.Genie.allFourPriorMomentImage
#print axioms ThresholdHC.Genie.allFourPriorMomentImage_compact
#print axioms ThresholdHC.Genie.allFourPriorMomentImage_iff
#print axioms ThresholdHC.Genie.allPriorCoordinates
#print axioms ThresholdHC.Genie.allPriorMomentImage
#print axioms ThresholdHC.Genie.allPriorMomentImage_compact_convex
#print axioms ThresholdHC.Genie.allPriorMomentImage_nonempty
#print axioms ThresholdHC.Genie.arrayAt_bellmanEnvelopeArray
#print axioms ThresholdHC.Genie.arrayAt_extendArray
#print axioms ThresholdHC.Genie.arrayAt_nonneg
#print axioms ThresholdHC.Genie.arrayAt_truncate_continue
#print axioms ThresholdHC.Genie.arrayAt_truncate_stop
#print axioms ThresholdHC.Genie.atomBox_of_prior
#print axioms ThresholdHC.Genie.atomConicFeasible_of_priors
#print axioms ThresholdHC.Genie.atomConicObjective
#print axioms ThresholdHC.Genie.atomConicObjective_of_priors
#print axioms ThresholdHC.Genie.atomConicValue
#print axioms ThresholdHC.Genie.atomConicValue_eq_genieSquared
#print axioms ThresholdHC.Genie.atomConicVariableCount
#print axioms ThresholdHC.Genie.atomConicVariableCount_bound
#print axioms ThresholdHC.Genie.atomConic_realization
#print axioms ThresholdHC.Genie.atomPointOfPriors
#print axioms ThresholdHC.Genie.atomPrefixCoefficient
#print axioms ThresholdHC.Genie.atomSignLaw
#print axioms ThresholdHC.Genie.atomSignLaw_apply
#print axioms ThresholdHC.Genie.atomSignLaw_rare
#print axioms ThresholdHC.Genie.bellmanEnvelopeArray
#print axioms ThresholdHC.Genie.bellman_le_envelope
#print axioms ThresholdHC.Genie.bellman_scale
#print axioms ThresholdHC.Genie.binary_difference_sq_bound
#print axioms ThresholdHC.Genie.capped_reward_le_truncated_reveal
#print axioms ThresholdHC.Genie.compact_decreasing_maximum
#print axioms ThresholdHC.Genie.continue_arrayAt_ge_cap
#print axioms ThresholdHC.Genie.countMean_extendArray
#print axioms ThresholdHC.Genie.countState_card_le_square
#print axioms ThresholdHC.Genie.directRiskProfile
#print axioms ThresholdHC.Genie.directRiskProfile_greatest
#print axioms ThresholdHC.Genie.directRiskProfile_max
#print axioms ThresholdHC.Genie.directRiskProfile_square
#print axioms ThresholdHC.Genie.directRiskScale
#print axioms ThresholdHC.Genie.directRiskScale_mem
#print axioms ThresholdHC.Genie.directRiskSquared
#print axioms ThresholdHC.Genie.direct_large_scale
#print axioms ThresholdHC.Genie.direct_large_scale_data
#print axioms ThresholdHC.Genie.direct_pair_risk
#print axioms ThresholdHC.Genie.direct_small_scale
#print axioms ThresholdHC.Genie.domainPriors
#print axioms ThresholdHC.Genie.domainPriors_admissible
#print axioms ThresholdHC.Genie.domainPriors_coordinates
#print axioms ThresholdHC.Genie.domain_dualRatio_upperSemicontinuous
#print axioms ThresholdHC.Genie.dualRatio_antitone
#print axioms ThresholdHC.Genie.dualRatio_coordinates_congr
#print axioms ThresholdHC.Genie.dualRatio_upperSemicontinuous
#print axioms ThresholdHC.Genie.dualValue_eq_domain_sup
#print axioms ThresholdHC.Genie.eRawChildren
#print axioms ThresholdHC.Genie.eRawLayer
#print axioms ThresholdHC.Genie.eRawLayer_mono
#print axioms ThresholdHC.Genie.eRaw_fullCap_layer
#print axioms ThresholdHC.Genie.eRaw_fullCap_reward
#print axioms ThresholdHC.Genie.eRaw_harmonic_conservation
#print axioms ThresholdHC.Genie.eRaw_layer_conservation
#print axioms ThresholdHC.Genie.eRaw_recursion
#print axioms ThresholdHC.Genie.eRaw_root_total
#print axioms ThresholdHC.Genie.eRaw_tail_harmonic
#print axioms ThresholdHC.Genie.eRaw_terminal
#print axioms ThresholdHC.Genie.eRaw_truncate_stop_before
#print axioms ThresholdHC.Genie.eRaw_truncate_stop_terminal
#print axioms ThresholdHC.Genie.envelope_root
#print axioms ThresholdHC.Genie.exists_bellmanEnvelope_iff
#print axioms ThresholdHC.Genie.exists_scaled_atom_prior
#print axioms ThresholdHC.Genie.extendArray
#print axioms ThresholdHC.Genie.extendCertificate
#print axioms ThresholdHC.Genie.extendFlow
#print axioms ThresholdHC.Genie.extendFlow_cone
#print axioms ThresholdHC.Genie.extendFlow_intensity
#print axioms ThresholdHC.Genie.feasible_extendCertificate
#print axioms ThresholdHC.Genie.finiteGenieCones_envelope
#print axioms ThresholdHC.Genie.finiteGenieCones_iff_bellman
#print axioms ThresholdHC.Genie.finiteGenieCones_iff_price
#print axioms ThresholdHC.Genie.finiteGenieCones_objective_attained
#print axioms ThresholdHC.Genie.finiteGenieCones_objective_le
#print axioms ThresholdHC.Genie.finiteGenieCones_of_envelope
#print axioms ThresholdHC.Genie.finiteGenieCones_zero
#print axioms ThresholdHC.Genie.finiteGenieConicValue
#print axioms ThresholdHC.Genie.finiteGenieConicValue_eq
#print axioms ThresholdHC.Genie.finiteRevealBound
#print axioms ThresholdHC.Genie.finiteRevealBound_exact
#print axioms ThresholdHC.Genie.finiteRevealBound_lower
#print axioms ThresholdHC.Genie.finite_latentDivergence
#print axioms ThresholdHC.Genie.finite_latent_perspectives
#print axioms ThresholdHC.Genie.finite_law_lintegral
#print axioms ThresholdHC.Genie.finite_prefixCoefficient
#print axioms ThresholdHC.Genie.finite_prior_mean
#print axioms ThresholdHC.Genie.finite_revealReward
#print axioms ThresholdHC.Genie.finite_revealReward_toReal
#print axioms ThresholdHC.Genie.finite_scaled_mean
#print axioms ThresholdHC.Genie.finite_scaled_prefixCoefficient
#print axioms ThresholdHC.Genie.flowInformation_extendFlow
#print axioms ThresholdHC.Genie.flowInformation_le_genie
#print axioms ThresholdHC.Genie.flowInformation_le_truncated_reveal
#print axioms ThresholdHC.Genie.flow_ratio_lowerSemicontinuous
#print axioms ThresholdHC.Genie.flow_ratio_perspective_sum
#print axioms ThresholdHC.Genie.genieBellmanRatio
#print axioms ThresholdHC.Genie.genieBellmanRatio_nonneg
#print axioms ThresholdHC.Genie.genieDualRatio
#print axioms ThresholdHC.Genie.genieDualRatio_le_infinite
#print axioms ThresholdHC.Genie.genieDualRatio_real
#print axioms ThresholdHC.Genie.genieFlowInformation
#print axioms ThresholdHC.Genie.genieFlowInformation_finite
#print axioms ThresholdHC.Genie.genieFlowInformation_fullCap
#print axioms ThresholdHC.Genie.genieFlowInformation_le_latent
#print axioms ThresholdHC.Genie.genieFlowInformation_le_truncated
#print axioms ThresholdHC.Genie.genieFlowInformation_toReal_raw
#print axioms ThresholdHC.Genie.genieFlowInformation_truncate
#print axioms ThresholdHC.Genie.genieFlowScore_information
#print axioms ThresholdHC.Genie.genieInformationRatio
#print axioms ThresholdHC.Genie.genieInformationRatio_antitone
#print axioms ThresholdHC.Genie.genieInformationRatio_antitone_cap
#print axioms ThresholdHC.Genie.genieInformationRatio_bellman_attained
#print axioms ThresholdHC.Genie.genieInformationRatio_bellman_certificate
#print axioms ThresholdHC.Genie.genieInformationRatio_bellman_zero
#print axioms ThresholdHC.Genie.genieInformationRatio_le_genieBellmanRatio
#print axioms ThresholdHC.Genie.genieInformationRatio_le_latent
#print axioms ThresholdHC.Genie.genieInformationRatio_top_iff
#print axioms ThresholdHC.Genie.geniePrefixInformation
#print axioms ThresholdHC.Genie.geniePrefixInformation_finite
#print axioms ThresholdHC.Genie.geniePrefixInformation_le_reveal
#print axioms ThresholdHC.Genie.genieReward
#print axioms ThresholdHC.Genie.genieSquared
#print axioms ThresholdHC.Genie.genieSquared_le_infinite
#print axioms ThresholdHC.Genie.genieSquared_mono
#print axioms ThresholdHC.Genie.genieValue
#print axioms ThresholdHC.Genie.genieValue_le_infinite
#print axioms ThresholdHC.Genie.genieValue_mono
#print axioms ThresholdHC.Genie.genieValue_positive
#print axioms ThresholdHC.Genie.genie_bellman_direct_squared_risk
#print axioms ThresholdHC.Genie.genie_direct_risk
#print axioms ThresholdHC.Genie.genie_direct_squared_risk
#print axioms ThresholdHC.Genie.genie_risk_bracket
#print axioms ThresholdHC.Genie.genie_stopping_certificate
#print axioms ThresholdHC.Genie.infiniteDualRatio
#print axioms ThresholdHC.Genie.infiniteDualRatio_eq_iInf
#print axioms ThresholdHC.Genie.infiniteDualValue
#print axioms ThresholdHC.Genie.infiniteInformationRatio
#print axioms ThresholdHC.Genie.infiniteInformationRatio_le_genie
#print axioms ThresholdHC.Genie.infiniteMidpointSquared
#print axioms ThresholdHC.Genie.infiniteMidpointValue
#print axioms ThresholdHC.Genie.infiniteProgramValue
#print axioms ThresholdHC.Genie.infiniteProgramValue_le_cap
#print axioms ThresholdHC.Genie.infiniteProgramValue_sq
#print axioms ThresholdHC.Genie.infinite_dual_positive_attained
#print axioms ThresholdHC.Genie.infinite_four_prior_duality
#print axioms ThresholdHC.Genie.infinite_midpoint_comparison
#print axioms ThresholdHC.Genie.infinite_midpoint_squared_comparison
#print axioms ThresholdHC.Genie.infinite_program_comparison
#print axioms ThresholdHC.Genie.infinite_program_positive
#print axioms ThresholdHC.Genie.infinite_weak_duality
#print axioms ThresholdHC.Genie.informationRatio_le_earlier_genie
#print axioms ThresholdHC.Genie.informationRatio_le_genie
#print axioms ThresholdHC.Genie.informationRatio_le_infinite
#print axioms ThresholdHC.Genie.informationRatio_lowerSemicontinuous
#print axioms ThresholdHC.Genie.informationRatio_mono
#print axioms ThresholdHC.Genie.informationRatio_tendsto
#print axioms ThresholdHC.Genie.latentCones_bounds
#print axioms ThresholdHC.Genie.latentCones_finite
#print axioms ThresholdHC.Genie.latentCones_of_finite
#print axioms ThresholdHC.Genie.latentDivergence
#print axioms ThresholdHC.Genie.lowerSemicontinuous_perspective
#print axioms ThresholdHC.Genie.measurable_perspective
#print axioms ThresholdHC.Genie.measurable_prefixLikelihood
#print axioms ThresholdHC.Genie.measurable_revealIntegrand
#print axioms ThresholdHC.Genie.ofReal_integral_le_lintegral_positive
#print axioms ThresholdHC.Genie.perspective_eq_iSup_test
#print axioms ThresholdHC.Genie.perspective_integral_le
#print axioms ThresholdHC.Genie.perspective_le_finite_iff
#print axioms ThresholdHC.Genie.perspective_neg_left
#print axioms ThresholdHC.Genie.perspective_scale_reference
#print axioms ThresholdHC.Genie.prefixDensity
#print axioms ThresholdHC.Genie.prefixDensity_information_le
#print axioms ThresholdHC.Genie.prefixDensity_integrable
#print axioms ThresholdHC.Genie.prefixDensity_nonneg
#print axioms ThresholdHC.Genie.prefixInformation_le_genie
#print axioms ThresholdHC.Genie.prefixInformation_le_revealReward
#print axioms ThresholdHC.Genie.priorDomainCompact
#print axioms ThresholdHC.Genie.priorDomain_nonempty
#print axioms ThresholdHC.Genie.priorPoint
#print axioms ThresholdHC.Genie.programSquared_antitone
#print axioms ThresholdHC.Genie.programValue_antitone
#print axioms ThresholdHC.Genie.programValue_tendsto
#print axioms ThresholdHC.Genie.quadratic_slack_iff
#print axioms ThresholdHC.Genie.quadratic_test_le_perspective
#print axioms ThresholdHC.Genie.rawArray_nonneg
#print axioms ThresholdHC.Genie.rawLayer_above_cap
#print axioms ThresholdHC.Genie.rawLayer_extendArray
#print axioms ThresholdHC.Genie.raw_truncate_continue_le
#print axioms ThresholdHC.Genie.raw_truncate_stop
#print axioms ThresholdHC.Genie.regularizedPriors
#print axioms ThresholdHC.Genie.regularizedPriors_admissible
#print axioms ThresholdHC.Genie.regularized_count_reference
#print axioms ThresholdHC.Genie.regularized_flowInformation
#print axioms ThresholdHC.Genie.regularized_infiniteInformation
#print axioms ThresholdHC.Genie.regularized_informationRatio
#print axioms ThresholdHC.Genie.regularized_latentDivergence_bound
#print axioms ThresholdHC.Genie.regularized_latent_perspective
#print axioms ThresholdHC.Genie.revealReward
#print axioms ThresholdHC.Genie.revealReward_children
#print axioms ThresholdHC.Genie.revealReward_le_latentDivergence
#print axioms ThresholdHC.Genie.revealReward_root
#print axioms ThresholdHC.Genie.rootBellman_scale
#print axioms ThresholdHC.Genie.scale_objective_attained
#print axioms ThresholdHC.Genie.scale_objective_bound
#print axioms ThresholdHC.Genie.scaled_genie_root
#print axioms ThresholdHC.Genie.terminal_reveal_sum
#print axioms ThresholdHC.Genie.truncateFlow
#print axioms ThresholdHC.Genie.truncateFlow_cone
#print axioms ThresholdHC.Genie.truncateFlow_intensity
#print axioms ThresholdHC.Genie.truncateFlow_work_le
#print axioms ThresholdHC.Genie.upperSemicontinuous_information_quotient
