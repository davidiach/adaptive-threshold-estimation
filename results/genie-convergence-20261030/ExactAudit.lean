import ThresholdHC.Genie.Model
import ThresholdHC.Genie.LatentModel
import ThresholdHC.Genie.PerspectiveIntegral
import ThresholdHC.Genie.RevealReward
import ThresholdHC.Genie.LatentScore
import ThresholdHC.Genie.TapeIdentification
import ThresholdHC.Genie.ObservationFiltration
import ThresholdHC.Genie.LatentTape
import ThresholdHC.Genie.LatentMoments
import ThresholdHC.Genie.FinitePosterior
import ThresholdHC.Genie.FlowExtension
import ThresholdHC.Genie.ExtendedFlowConservation
import ThresholdHC.Genie.RevealProgram
import ThresholdHC.Genie.RevealFiniteness
import ThresholdHC.Genie.RevealResidual
import ThresholdHC.Genie.LatentPrefix
import ThresholdHC.Genie.CapMonotonicity
import ThresholdHC.Genie.InfiniteDualLimit
import ThresholdHC.Genie.CapLimits
import ThresholdHC.Genie.RevealConvergence
import ThresholdHC.Genie.FlowTruncation
import ThresholdHC.Genie.RevealTruncation
import ThresholdHC.Genie.InfiniteCoordinates
import ThresholdHC.Genie.PerspectiveTopology
import ThresholdHC.Genie.InformationTopology
import ThresholdHC.Genie.DualTopology
import ThresholdHC.Genie.CompactPriorDomain
import ThresholdHC.Genie.CompactDecreasingMaximum
import ThresholdHC.Genie.InfiniteComparison
import ThresholdHC.Genie.InfiniteDuality
import ThresholdHC.Genie.ReferenceRegularization
import ThresholdHC.Genie.OptimizedBrackets
import ThresholdHC.Genie.OptimizedConvergence

open MeasureTheory Filter
open scoped ENNReal Topology
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    (∫⁻ z, ENNReal.ofReal ((latentScore Q z)^2) ∂latentReference μ Q.variance) = latentDivergence μ Q :=
  latentScore_secondMoment
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    ∀ n : ℕ, (∫⁻ z, ENNReal.ofReal ((((latentTapeLaw μ Q.variance)[latentTapeScore Q |
      observationFiltration latentObservedTape measurable_latentObservedTape n]) z)^2)
        ∂latentTapeLaw μ Q.variance) = terminalInformation μ Q n := posterior_secondMoment_eq_terminal
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    let P := latentTapeLaw μ Q.variance
    let ℱ := observationFiltration latentObservedTape measurable_latentObservedTape
    ∀ᵐ z ∂P, Tendsto (fun n => (P[latentTapeScore Q | ℱ n]) z) atTop (𝓝 (latentTapeScore Q z)) :=
  latent_score_posterior_tendsto
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    Tendsto (terminalInformation μ Q) atTop (𝓝 (latentDivergence μ Q)) := terminalInformation_tendsto
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    Tendsto (revealResidual μ Q) atTop (𝓝 0) := revealResidual_tendsto_zero
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    Tendsto (fun n : ℕ => genieInformationRatio μ (n+1) Q) atTop (𝓝 (infiniteInformationRatio μ Q)) :=
  genieInformationRatio_tendsto
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors) (ε : ℝ)
    (hε : 0 ≤ ε ∧ ε ≤ 1), 0 < ε →
    latentDivergence μ (regularizedPriors Q ε hε) ≤ ENNReal.ofReal (4/ε) := regularized_latentDivergence_bound
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors) (ε : ℝ)
    (hε : 0 ≤ ε ∧ ε ≤ 1), ε < 1 → infiniteInformationRatio μ (regularizedPriors Q ε hε) ≤
      ENNReal.ofReal (1/(1-ε))*infiniteInformationRatio μ Q := regularized_infiniteInformation
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/2 → 0 < B →
    (⨆ n : ℕ, genieSquared μ ρ B (n+1)) = infiniteProgramValue μ ρ B ^ 2 := genieSquared_sup_eq_infinite
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/2 → 0 < B →
    Tendsto (fun n : ℕ => genieValue μ ρ B (n+1)) atTop (𝓝 (infiniteProgramValue μ ρ B)) := genieValue_tendsto
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 < ρ → ρ ≤ 1/2 → 0 < B →
    ∀ N : ℕ, 0 < N → genieValue μ ρ B N/8 ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N := genie_risk_bracket
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/2 → 0 < B →
    ∃ N : ℕ, 0 < N ∧ programValue μ ρ B N ≤ 2*genieValue μ ρ B N ∧
      rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧ programValue μ ρ B N ≤ 16*rareMinimaxRisk μ ρ B :=
  genie_stopping_terminates

#print axioms ThresholdHC.Genie.AllCountIndex
#print axioms ThresholdHC.Genie.AllFourCoordinates
#print axioms ThresholdHC.Genie.LatentState
#print axioms ThresholdHC.Genie.LatentTapeState
#print axioms ThresholdHC.Genie.PriorDomain
#print axioms ThresholdHC.Genie.allFourPriorCoordinates
#print axioms ThresholdHC.Genie.allFourPriorMomentImage
#print axioms ThresholdHC.Genie.allFourPriorMomentImage_compact
#print axioms ThresholdHC.Genie.allFourPriorMomentImage_iff
#print axioms ThresholdHC.Genie.allPriorCoordinates
#print axioms ThresholdHC.Genie.allPriorMomentImage
#print axioms ThresholdHC.Genie.allPriorMomentImage_compact_convex
#print axioms ThresholdHC.Genie.allPriorMomentImage_nonempty
#print axioms ThresholdHC.Genie.arrayAt_extendArray
#print axioms ThresholdHC.Genie.arrayAt_nonneg
#print axioms ThresholdHC.Genie.arrayAt_truncate_continue
#print axioms ThresholdHC.Genie.arrayAt_truncate_stop
#print axioms ThresholdHC.Genie.binary_difference_sq_bound
#print axioms ThresholdHC.Genie.bitValue
#print axioms ThresholdHC.Genie.capped_reward_le_truncated_reveal
#print axioms ThresholdHC.Genie.compact_decreasing_maximum
#print axioms ThresholdHC.Genie.continue_arrayAt_ge_cap
#print axioms ThresholdHC.Genie.countMean_extendArray
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
#print axioms ThresholdHC.Genie.empiricalMean
#print axioms ThresholdHC.Genie.extendArray
#print axioms ThresholdHC.Genie.extendCertificate
#print axioms ThresholdHC.Genie.extendFlow
#print axioms ThresholdHC.Genie.extendFlow_cone
#print axioms ThresholdHC.Genie.extendFlow_intensity
#print axioms ThresholdHC.Genie.feasible_extendCertificate
#print axioms ThresholdHC.Genie.finite_latent_perspectives_ae
#print axioms ThresholdHC.Genie.finite_posterior_secondMoment
#print axioms ThresholdHC.Genie.flowInformation_extendFlow
#print axioms ThresholdHC.Genie.flowInformation_le_genie
#print axioms ThresholdHC.Genie.flowInformation_le_truncated_reveal
#print axioms ThresholdHC.Genie.flow_ratio_lowerSemicontinuous
#print axioms ThresholdHC.Genie.flow_ratio_perspective_sum
#print axioms ThresholdHC.Genie.genieDualRatio
#print axioms ThresholdHC.Genie.genieDualRatio_le_infinite
#print axioms ThresholdHC.Genie.genieDualRatio_tendsto
#print axioms ThresholdHC.Genie.genieFlowInformation
#print axioms ThresholdHC.Genie.genieFlowInformation_finite
#print axioms ThresholdHC.Genie.genieFlowInformation_fullCap
#print axioms ThresholdHC.Genie.genieFlowInformation_gap
#print axioms ThresholdHC.Genie.genieFlowInformation_le_add_residual
#print axioms ThresholdHC.Genie.genieFlowInformation_le_latent
#print axioms ThresholdHC.Genie.genieFlowInformation_le_truncated
#print axioms ThresholdHC.Genie.genieFlowInformation_truncate
#print axioms ThresholdHC.Genie.genieInformationRatio
#print axioms ThresholdHC.Genie.genieInformationRatio_antitone
#print axioms ThresholdHC.Genie.genieInformationRatio_antitone_cap
#print axioms ThresholdHC.Genie.genieInformationRatio_le_add_residual
#print axioms ThresholdHC.Genie.genieInformationRatio_le_latent
#print axioms ThresholdHC.Genie.genieInformationRatio_tendsto
#print axioms ThresholdHC.Genie.genieInformationRatio_top_iff
#print axioms ThresholdHC.Genie.geniePrefixInformation
#print axioms ThresholdHC.Genie.geniePrefixInformation_finite
#print axioms ThresholdHC.Genie.geniePrefixInformation_le_reveal
#print axioms ThresholdHC.Genie.genieSquared
#print axioms ThresholdHC.Genie.genieSquared_le_infinite
#print axioms ThresholdHC.Genie.genieSquared_mono
#print axioms ThresholdHC.Genie.genieSquared_sup_eq_infinite
#print axioms ThresholdHC.Genie.genieSquared_tendsto
#print axioms ThresholdHC.Genie.genieValue
#print axioms ThresholdHC.Genie.genieValue_le_infinite
#print axioms ThresholdHC.Genie.genieValue_mono
#print axioms ThresholdHC.Genie.genieValue_positive
#print axioms ThresholdHC.Genie.genieValue_tendsto
#print axioms ThresholdHC.Genie.genie_information_error
#print axioms ThresholdHC.Genie.genie_risk_bracket
#print axioms ThresholdHC.Genie.genie_stopping_certificate
#print axioms ThresholdHC.Genie.genie_stopping_eventually
#print axioms ThresholdHC.Genie.genie_stopping_terminates
#print axioms ThresholdHC.Genie.infiniteDualRatio
#print axioms ThresholdHC.Genie.infiniteDualRatio_eq_iInf
#print axioms ThresholdHC.Genie.infiniteDualRatio_le_genieSup
#print axioms ThresholdHC.Genie.infiniteDualRatio_le_genieSup_of_finite
#print axioms ThresholdHC.Genie.infiniteDualValue
#print axioms ThresholdHC.Genie.infiniteInformationRatio
#print axioms ThresholdHC.Genie.infiniteInformationRatio_le_genie
#print axioms ThresholdHC.Genie.infiniteProgramValue
#print axioms ThresholdHC.Genie.infiniteProgramValue_le_cap
#print axioms ThresholdHC.Genie.infiniteProgramValue_ne_top
#print axioms ThresholdHC.Genie.infiniteProgramValue_sq
#print axioms ThresholdHC.Genie.infinite_dual_positive_attained
#print axioms ThresholdHC.Genie.infinite_four_prior_duality
#print axioms ThresholdHC.Genie.infinite_program_comparison
#print axioms ThresholdHC.Genie.infinite_program_positive
#print axioms ThresholdHC.Genie.infinite_weak_duality
#print axioms ThresholdHC.Genie.informationRatio_le_earlier_genie
#print axioms ThresholdHC.Genie.informationRatio_le_genie
#print axioms ThresholdHC.Genie.informationRatio_le_infinite
#print axioms ThresholdHC.Genie.informationRatio_lowerSemicontinuous
#print axioms ThresholdHC.Genie.informationRatio_mono
#print axioms ThresholdHC.Genie.informationRatio_tendsto
#print axioms ThresholdHC.Genie.latentDivergence
#print axioms ThresholdHC.Genie.latentObservedTape
#print axioms ThresholdHC.Genie.latentParameter
#print axioms ThresholdHC.Genie.latentParameter_embedding
#print axioms ThresholdHC.Genie.latentParameter_injective
#print axioms ThresholdHC.Genie.latentReference
#print axioms ThresholdHC.Genie.latentReference_integral
#print axioms ThresholdHC.Genie.latentReference_lintegral
#print axioms ThresholdHC.Genie.latentReference_probability
#print axioms ThresholdHC.Genie.latentScore
#print axioms ThresholdHC.Genie.latentScore_integrable
#print axioms ThresholdHC.Genie.latentScore_memLp_two
#print axioms ThresholdHC.Genie.latentScore_secondMoment
#print axioms ThresholdHC.Genie.latentSelector
#print axioms ThresholdHC.Genie.latentTapeLaw
#print axioms ThresholdHC.Genie.latentTapeLaw_probability
#print axioms ThresholdHC.Genie.latentTapeScore
#print axioms ThresholdHC.Genie.latentTapeScore_integrable
#print axioms ThresholdHC.Genie.latentTapeScore_secondMoment
#print axioms ThresholdHC.Genie.latentTape_parameter_ae
#print axioms ThresholdHC.Genie.latentTape_score_reconstruction
#print axioms ThresholdHC.Genie.latent_prefix_integral
#print axioms ThresholdHC.Genie.latent_prefix_mass
#print axioms ThresholdHC.Genie.latent_prefix_score
#print axioms ThresholdHC.Genie.latent_score_posterior_tendsto
#print axioms ThresholdHC.Genie.lowerSemicontinuous_perspective
#print axioms ThresholdHC.Genie.measurable_bitValue
#print axioms ThresholdHC.Genie.measurable_empiricalMean
#print axioms ThresholdHC.Genie.measurable_latentObservedTape
#print axioms ThresholdHC.Genie.measurable_latentParameter
#print axioms ThresholdHC.Genie.measurable_latentScore
#print axioms ThresholdHC.Genie.measurable_latentSelector
#print axioms ThresholdHC.Genie.measurable_latentTapeScore
#print axioms ThresholdHC.Genie.measurable_parameterScore
#print axioms ThresholdHC.Genie.measurable_perspective
#print axioms ThresholdHC.Genie.measurable_prefixLikelihood
#print axioms ThresholdHC.Genie.measurable_revealIntegrand
#print axioms ThresholdHC.Genie.measurable_tapeParameter
#print axioms ThresholdHC.Genie.observationFiltration
#print axioms ThresholdHC.Genie.observationFiltration_eq_comap
#print axioms ThresholdHC.Genie.observedPrefix
#print axioms ThresholdHC.Genie.observedPrefix_measurable
#print axioms ThresholdHC.Genie.observedTape_measurable_iSup
#print axioms ThresholdHC.Genie.ofReal_integral_le_lintegral_positive
#print axioms ThresholdHC.Genie.parameterScore
#print axioms ThresholdHC.Genie.parameterScore_latent
#print axioms ThresholdHC.Genie.parameter_mixture_identification
#print axioms ThresholdHC.Genie.perspective_eq_iSup_test
#print axioms ThresholdHC.Genie.perspective_integral_le
#print axioms ThresholdHC.Genie.perspective_le_finite_iff
#print axioms ThresholdHC.Genie.perspective_neg_left
#print axioms ThresholdHC.Genie.perspective_scale_reference
#print axioms ThresholdHC.Genie.posterior_secondMoment_eq_terminal
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
#print axioms ThresholdHC.Genie.quadratic_test_le_perspective
#print axioms ThresholdHC.Genie.rawArray_nonneg
#print axioms ThresholdHC.Genie.rawLayer_above_cap
#print axioms ThresholdHC.Genie.rawLayer_extendArray
#print axioms ThresholdHC.Genie.raw_stop_le_choose
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
#print axioms ThresholdHC.Genie.revealGap
#print axioms ThresholdHC.Genie.revealResidual
#print axioms ThresholdHC.Genie.revealResidual_add_terminal
#print axioms ThresholdHC.Genie.revealResidual_eq_sub
#print axioms ThresholdHC.Genie.revealResidual_tendsto_zero
#print axioms ThresholdHC.Genie.revealReward
#print axioms ThresholdHC.Genie.revealReward_children
#print axioms ThresholdHC.Genie.revealReward_eq_add_gap
#print axioms ThresholdHC.Genie.revealReward_le_latentDivergence
#print axioms ThresholdHC.Genie.revealReward_root
#print axioms ThresholdHC.Genie.sum_words_by_heads_ennreal
#print axioms ThresholdHC.Genie.tapeParameter
#print axioms ThresholdHC.Genie.tapeParameter_ae
#print axioms ThresholdHC.Genie.tape_parameter_identification
#print axioms ThresholdHC.Genie.terminalInformation
#print axioms ThresholdHC.Genie.terminalInformation_le_latent
#print axioms ThresholdHC.Genie.terminalInformation_tendsto
#print axioms ThresholdHC.Genie.terminal_reveal_sum
#print axioms ThresholdHC.Genie.truncateFlow
#print axioms ThresholdHC.Genie.truncateFlow_cone
#print axioms ThresholdHC.Genie.truncateFlow_intensity
#print axioms ThresholdHC.Genie.truncateFlow_work_le
#print axioms ThresholdHC.Genie.uniform_gap_prefix_real
#print axioms ThresholdHC.Genie.uniform_tapeParameter_ae
#print axioms ThresholdHC.Genie.upperSemicontinuous_information_quotient
#print axioms ThresholdHC.Genie.weighted_score
#print axioms ThresholdHC.Genie.weighted_score_square
