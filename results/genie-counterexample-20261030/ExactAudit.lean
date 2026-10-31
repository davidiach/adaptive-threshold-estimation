import ThresholdHC.Genie.Model
import ThresholdHC.Genie.PerspectiveIntegral
import ThresholdHC.Genie.RevealReward
import ThresholdHC.Genie.FlowExtension
import ThresholdHC.Genie.ExtendedFlowConservation
import ThresholdHC.Genie.RevealProgram
import ThresholdHC.Genie.RevealFiniteness
import ThresholdHC.Genie.UniformGapModel
import ThresholdHC.Genie.InfiniteDivergence
import ThresholdHC.Genie.UniformMoments
import ThresholdHC.Genie.UniformPrefixes
import ThresholdHC.Genie.SingularPrefixBound
import ThresholdHC.Genie.FlowDepth
import ThresholdHC.Genie.SingularFlowBound
import ThresholdHC.Genie.InfiniteDivergenceExample

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6
example : Admissible uniformGapLaw (1/4) singularExamplePriors ∧
    latentDivergence uniformGapLaw singularExamplePriors = ⊤ ∧
    (∀ N : ℕ, 0 < N → genieInformationRatio uniformGapLaw N singularExamplePriors = ⊤) ∧
    infiniteInformationRatio uniformGapLaw singularExamplePriors ≤ ENNReal.ofReal (3/4) ∧
    ¬Tendsto (fun n : ℕ => genieInformationRatio uniformGapLaw (n+1) singularExamplePriors)
      atTop (𝓝 (infiniteInformationRatio uniformGapLaw singularExamplePriors)) := infinite_divergence_counterexample
example : ∀ {N : ℕ} (f : Flow N), FlowCone f →
    flowInformation uniformGapLaw singularExamplePriors f ≤
      ENNReal.ofReal (3/4*countMean uniformGapLaw singularExamplePriors.work f.continueWeight) :=
  singular_flow_information
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → ∀ u : ℕ → ℕ → ℝ,
    (∀ n k, k ≤ n → u (n+1) k+u (n+1) (k+1) = u n k) →
    (∑ n ∈ Finset.range (N+1), rawLayer f.stopWeight (fun n k => (n:ℝ)*u n k) n) =
      ∑ n ∈ Finset.range (N+1), rawLayer f.continueWeight u n := raw_stopping_depth

#print axioms ThresholdHC.Genie.arrayAt_extendArray
#print axioms ThresholdHC.Genie.arrayAt_nonneg
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
#print axioms ThresholdHC.Genie.extendArray
#print axioms ThresholdHC.Genie.extendFlow
#print axioms ThresholdHC.Genie.extendFlow_cone
#print axioms ThresholdHC.Genie.extendFlow_intensity
#print axioms ThresholdHC.Genie.flowInformation_le_genie
#print axioms ThresholdHC.Genie.genieFlowInformation
#print axioms ThresholdHC.Genie.genieFlowInformation_finite
#print axioms ThresholdHC.Genie.genieFlowInformation_fullCap
#print axioms ThresholdHC.Genie.genieFlowInformation_le_latent
#print axioms ThresholdHC.Genie.genieInformationRatio
#print axioms ThresholdHC.Genie.genieInformationRatio_le_latent
#print axioms ThresholdHC.Genie.genieInformationRatio_top_iff
#print axioms ThresholdHC.Genie.geniePrefixInformation
#print axioms ThresholdHC.Genie.geniePrefixInformation_finite
#print axioms ThresholdHC.Genie.geniePrefixInformation_le_reveal
#print axioms ThresholdHC.Genie.infiniteDualRatio
#print axioms ThresholdHC.Genie.infiniteInformationRatio
#print axioms ThresholdHC.Genie.infiniteProgramValue
#print axioms ThresholdHC.Genie.infinite_divergence_counterexample
#print axioms ThresholdHC.Genie.informationRatio_le_genie
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
#print axioms ThresholdHC.Genie.quadratic_test_le_perspective
#print axioms ThresholdHC.Genie.rawArray_nonneg
#print axioms ThresholdHC.Genie.rawLayer_above_cap
#print axioms ThresholdHC.Genie.rawLayer_extendArray
#print axioms ThresholdHC.Genie.raw_stopping_depth
#print axioms ThresholdHC.Genie.revealReward
#print axioms ThresholdHC.Genie.revealReward_children
#print axioms ThresholdHC.Genie.revealReward_le_latentDivergence
#print axioms ThresholdHC.Genie.revealReward_root
#print axioms ThresholdHC.Genie.singularExamplePriors
#print axioms ThresholdHC.Genie.singularExample_admissible
#print axioms ThresholdHC.Genie.singularExample_genie_top
#print axioms ThresholdHC.Genie.singularExample_latentDivergence
#print axioms ThresholdHC.Genie.singularExample_no_pointwise_convergence
#print axioms ThresholdHC.Genie.singularVariancePrior
#print axioms ThresholdHC.Genie.singularVariancePrior_mean
#print axioms ThresholdHC.Genie.singular_flow_information
#print axioms ThresholdHC.Genie.singular_infiniteInformationRatio_bound
#print axioms ThresholdHC.Genie.singular_informationRatio_bound
#print axioms ThresholdHC.Genie.singular_prefix_gap
#print axioms ThresholdHC.Genie.singular_prefix_information
#print axioms ThresholdHC.Genie.singular_variance_prefix_moment
#print axioms ThresholdHC.Genie.singular_work_prefix
#print axioms ThresholdHC.Genie.stopping_depth_countMean
#print axioms ThresholdHC.Genie.terminal_reveal_sum
#print axioms ThresholdHC.Genie.uniformGapLaw
#print axioms ThresholdHC.Genie.uniformGapLaw_probability
#print axioms ThresholdHC.Genie.uniformGap_integral
#print axioms ThresholdHC.Genie.uniformGap_inverse_not_integrable
#print axioms ThresholdHC.Genie.uniformGap_symmetrize
#print axioms ThresholdHC.Genie.uniformMoment
#print axioms ThresholdHC.Genie.uniformMoment_balance
#print axioms ThresholdHC.Genie.uniformMoment_harmonic
#print axioms ThresholdHC.Genie.uniformMoment_nonneg
#print axioms ThresholdHC.Genie.uniformMoment_pos
#print axioms ThresholdHC.Genie.uniformMoment_recurrence
#print axioms ThresholdHC.Genie.uniformMonomial
#print axioms ThresholdHC.Genie.uniformMonomial_continuous
#print axioms ThresholdHC.Genie.uniformSignPrior
#print axioms ThresholdHC.Genie.uniform_prefix_moment
