import ThresholdHC.Genie.Model
import ThresholdHC.Genie.PerspectiveIntegral
import ThresholdHC.Genie.RevealReward
import ThresholdHC.Genie.FlowExtension
import ThresholdHC.Genie.ExtendedFlowConservation
import ThresholdHC.Genie.RevealProgram
import ThresholdHC.Genie.FlowTruncation
import ThresholdHC.Genie.CapMonotonicity
import ThresholdHC.Genie.RevealTruncation
import ThresholdHC.Genie.RevealFiniteness
import ThresholdHC.Genie.RevealBellman
import ThresholdHC.Genie.RevealResidual

open MeasureTheory
open scoped ENNReal
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (N : ℕ), 0 < N → ∀ Q : FourPriors,
    infiniteInformationRatio μ Q ≤ genieInformationRatio μ N Q := infiniteInformationRatio_le_genie
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors),
    Antitone (fun N : ℕ => genieInformationRatio μ (N+1) Q) := genieInformationRatio_antitone
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    latentDivergence μ Q ≠ ⊤ → genieInformationRatio μ N Q-informationRatio μ N Q ≤
      latentDivergence μ Q-terminalInformation μ Q N := genie_information_error
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    0 < N → latentDivergence μ Q ≠ ⊤ →
    genieInformationRatio μ N Q = ENNReal.ofReal (genieBellmanRatio μ N Q) ∧
    let f := bellmanFlow (genieReward μ Q N) (prefixCoefficient μ Q.work) (genieBellmanRatio μ N Q) N
    FlowCone f ∧ intensity f = 1 ∧ genieFlowInformation μ Q f /
      ENNReal.ofReal (countMean μ Q.work f.continueWeight) = genieInformationRatio μ N Q :=
  genieInformationRatio_bellman_attained
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    0 < N → latentDivergence μ Q ≠ ⊤ → ∀ κ : ℝ, 0 ≤ κ →
    (genieInformationRatio μ N Q ≤ ENNReal.ofReal κ ↔
      rootBellman (genieReward μ Q N) (prefixCoefficient μ Q.work) κ (N-1) ≤ 0) :=
  genieInformationRatio_bellman_certificate
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ), 0 < N → ∀ Q : FourPriors,
    (genieInformationRatio μ N Q = ⊤ ↔ latentDivergence μ Q = ⊤) := genieInformationRatio_top_iff
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors) (n k : ℕ),
    prefixInformation μ Q n k ≤ revealReward μ Q n k := prefixInformation_le_revealReward
example : ∀ (μ : Measure Gap) (Q : FourPriors) (N : ℕ),
    genieFlowInformation μ Q (fullCapFlow N) = latentDivergence μ Q := genieFlowInformation_fullCap

#print axioms ThresholdHC.Genie.arrayAt_extendArray
#print axioms ThresholdHC.Genie.arrayAt_nonneg
#print axioms ThresholdHC.Genie.arrayAt_truncate_continue
#print axioms ThresholdHC.Genie.arrayAt_truncate_stop
#print axioms ThresholdHC.Genie.capped_reward_le_truncated_reveal
#print axioms ThresholdHC.Genie.continue_arrayAt_ge_cap
#print axioms ThresholdHC.Genie.countMean_extendArray
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
#print axioms ThresholdHC.Genie.extendArray
#print axioms ThresholdHC.Genie.extendCertificate
#print axioms ThresholdHC.Genie.extendFlow
#print axioms ThresholdHC.Genie.extendFlow_cone
#print axioms ThresholdHC.Genie.extendFlow_intensity
#print axioms ThresholdHC.Genie.feasible_extendCertificate
#print axioms ThresholdHC.Genie.flowInformation_extendFlow
#print axioms ThresholdHC.Genie.flowInformation_le_genie
#print axioms ThresholdHC.Genie.flowInformation_le_truncated_reveal
#print axioms ThresholdHC.Genie.genieBellmanRatio
#print axioms ThresholdHC.Genie.genieBellmanRatio_nonneg
#print axioms ThresholdHC.Genie.genieFlowInformation
#print axioms ThresholdHC.Genie.genieFlowInformation_finite
#print axioms ThresholdHC.Genie.genieFlowInformation_fullCap
#print axioms ThresholdHC.Genie.genieFlowInformation_gap
#print axioms ThresholdHC.Genie.genieFlowInformation_le_add_residual
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
#print axioms ThresholdHC.Genie.genieInformationRatio_le_add_residual
#print axioms ThresholdHC.Genie.genieInformationRatio_le_genieBellmanRatio
#print axioms ThresholdHC.Genie.genieInformationRatio_le_latent
#print axioms ThresholdHC.Genie.genieInformationRatio_top_iff
#print axioms ThresholdHC.Genie.geniePrefixInformation
#print axioms ThresholdHC.Genie.geniePrefixInformation_finite
#print axioms ThresholdHC.Genie.geniePrefixInformation_le_reveal
#print axioms ThresholdHC.Genie.genieReward
#print axioms ThresholdHC.Genie.genie_information_error
#print axioms ThresholdHC.Genie.infiniteDualRatio
#print axioms ThresholdHC.Genie.infiniteInformationRatio
#print axioms ThresholdHC.Genie.infiniteInformationRatio_le_genie
#print axioms ThresholdHC.Genie.infiniteProgramValue
#print axioms ThresholdHC.Genie.informationRatio_le_earlier_genie
#print axioms ThresholdHC.Genie.informationRatio_le_genie
#print axioms ThresholdHC.Genie.informationRatio_mono
#print axioms ThresholdHC.Genie.latentDivergence
#print axioms ThresholdHC.Genie.measurable_perspective
#print axioms ThresholdHC.Genie.measurable_prefixLikelihood
#print axioms ThresholdHC.Genie.measurable_revealIntegrand
#print axioms ThresholdHC.Genie.ofReal_integral_le_lintegral_positive
#print axioms ThresholdHC.Genie.perspective_eq_iSup_test
#print axioms ThresholdHC.Genie.perspective_integral_le
#print axioms ThresholdHC.Genie.perspective_neg_left
#print axioms ThresholdHC.Genie.prefixDensity
#print axioms ThresholdHC.Genie.prefixDensity_information_le
#print axioms ThresholdHC.Genie.prefixDensity_integrable
#print axioms ThresholdHC.Genie.prefixDensity_nonneg
#print axioms ThresholdHC.Genie.prefixInformation_le_genie
#print axioms ThresholdHC.Genie.prefixInformation_le_revealReward
#print axioms ThresholdHC.Genie.programSquared_antitone
#print axioms ThresholdHC.Genie.programValue_antitone
#print axioms ThresholdHC.Genie.quadratic_test_le_perspective
#print axioms ThresholdHC.Genie.rawArray_nonneg
#print axioms ThresholdHC.Genie.rawLayer_above_cap
#print axioms ThresholdHC.Genie.rawLayer_extendArray
#print axioms ThresholdHC.Genie.raw_stop_le_choose
#print axioms ThresholdHC.Genie.raw_truncate_continue_le
#print axioms ThresholdHC.Genie.raw_truncate_stop
#print axioms ThresholdHC.Genie.revealGap
#print axioms ThresholdHC.Genie.revealResidual
#print axioms ThresholdHC.Genie.revealResidual_add_terminal
#print axioms ThresholdHC.Genie.revealResidual_eq_sub
#print axioms ThresholdHC.Genie.revealReward
#print axioms ThresholdHC.Genie.revealReward_children
#print axioms ThresholdHC.Genie.revealReward_eq_add_gap
#print axioms ThresholdHC.Genie.revealReward_le_latentDivergence
#print axioms ThresholdHC.Genie.revealReward_root
#print axioms ThresholdHC.Genie.terminalInformation
#print axioms ThresholdHC.Genie.terminal_reveal_sum
#print axioms ThresholdHC.Genie.truncateFlow
#print axioms ThresholdHC.Genie.truncateFlow_cone
#print axioms ThresholdHC.Genie.truncateFlow_intensity
#print axioms ThresholdHC.Genie.truncateFlow_work_le
