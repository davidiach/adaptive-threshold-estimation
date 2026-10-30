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
import ThresholdHC.Genie.CapLimits

open MeasureTheory Filter
open scoped ENNReal Topology
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ∀ {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    infiniteProgramValue μ ρ B ^ 2 = infiniteDualValue μ ρ B ∧
    ∃ Q : FourPriors, Admissible μ ρ Q ∧
      infiniteDualRatio μ B Q = infiniteProgramValue μ ρ B ^ 2 := infinite_four_prior_duality
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ∀ {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    ∃ Q : FourPriors, Admissible μ ρ Q ∧
      infiniteDualRatio μ B Q = infiniteProgramValue μ ρ B ^ 2 ∧
      0 < infiniteProgramValue μ ρ B ^ 2 ∧ infiniteInformationRatio μ Q < ⊤ := infinite_dual_positive_attained
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    infiniteMidpointValue μ ρ B ≤ infiniteProgramValue μ ρ B ∧
    infiniteProgramValue μ ρ B ≤ 3*infiniteMidpointValue μ ρ B := infinite_midpoint_comparison
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ infiniteProgramValue μ ρ B ∧
    infiniteProgramValue μ ρ B ≤ 8*rareMinimaxRisk μ ρ B := infinite_program_comparison
example : ∀ (μ : Measure Gap) (Q : FourPriors),
    Monotone (fun N => informationRatio μ N Q) := informationRatio_mono
example : ∀ (μ : Measure Gap) (ρ B : ℝ),
    Antitone (fun N => programValue μ ρ B N) := programValue_antitone
example : ∀ (μ : Measure Gap) (ρ B : ℝ),
    Tendsto (fun N : ℕ => programValue μ ρ B (N+1)) atTop
      (𝓝 (infiniteProgramValue μ ρ B)) := programValue_tendsto
example : ∀ (μ : Measure Gap) (Q : FourPriors),
    Tendsto (fun N : ℕ => informationRatio μ (N+1) Q) atTop
      (𝓝 (infiniteInformationRatio μ Q)) := informationRatio_tendsto

#print axioms ThresholdHC.Genie.AllCountIndex
#print axioms ThresholdHC.Genie.AllFourCoordinates
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
#print axioms ThresholdHC.Genie.arrayAt_extendArray
#print axioms ThresholdHC.Genie.arrayAt_nonneg
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
#print axioms ThresholdHC.Genie.extendArray
#print axioms ThresholdHC.Genie.extendCertificate
#print axioms ThresholdHC.Genie.extendFlow
#print axioms ThresholdHC.Genie.extendFlow_cone
#print axioms ThresholdHC.Genie.extendFlow_intensity
#print axioms ThresholdHC.Genie.feasible_extendCertificate
#print axioms ThresholdHC.Genie.flowInformation_extendFlow
#print axioms ThresholdHC.Genie.flow_ratio_lowerSemicontinuous
#print axioms ThresholdHC.Genie.flow_ratio_perspective_sum
#print axioms ThresholdHC.Genie.infiniteDualRatio
#print axioms ThresholdHC.Genie.infiniteDualRatio_eq_iInf
#print axioms ThresholdHC.Genie.infiniteDualValue
#print axioms ThresholdHC.Genie.infiniteInformationRatio
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
#print axioms ThresholdHC.Genie.informationRatio_le_infinite
#print axioms ThresholdHC.Genie.informationRatio_lowerSemicontinuous
#print axioms ThresholdHC.Genie.informationRatio_mono
#print axioms ThresholdHC.Genie.informationRatio_tendsto
#print axioms ThresholdHC.Genie.latentDivergence
#print axioms ThresholdHC.Genie.lowerSemicontinuous_perspective
#print axioms ThresholdHC.Genie.perspective_le_finite_iff
#print axioms ThresholdHC.Genie.priorDomainCompact
#print axioms ThresholdHC.Genie.priorDomain_nonempty
#print axioms ThresholdHC.Genie.priorPoint
#print axioms ThresholdHC.Genie.programSquared_antitone
#print axioms ThresholdHC.Genie.programValue_antitone
#print axioms ThresholdHC.Genie.programValue_tendsto
#print axioms ThresholdHC.Genie.rawLayer_above_cap
#print axioms ThresholdHC.Genie.rawLayer_extendArray
#print axioms ThresholdHC.Genie.revealReward
#print axioms ThresholdHC.Genie.upperSemicontinuous_information_quotient
