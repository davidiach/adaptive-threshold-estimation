import ThresholdHC.CapIdentification.AffineCentering
import ThresholdHC.CapIdentification.AffineRecovery
import ThresholdHC.CapIdentification.BiasApproximation
import ThresholdHC.CapIdentification.BiasFloor
import ThresholdHC.CapIdentification.BudgetLimit
import ThresholdHC.CapIdentification.CenteredBasis
import ThresholdHC.CapIdentification.ContrastFunctional
import ThresholdHC.CapIdentification.CountBounds
import ThresholdHC.CapIdentification.CountMatching
import ThresholdHC.CapIdentification.DiameterAttainment
import ThresholdHC.CapIdentification.DiameterConsequences
import ThresholdHC.CapIdentification.FiniteSeparation
import ThresholdHC.CapIdentification.FiniteSupportTarget
import ThresholdHC.CapIdentification.Full
import ThresholdHC.CapIdentification.FullCapCertificate
import ThresholdHC.CapIdentification.InformationZero
import ThresholdHC.CapIdentification.Interpolation
import ThresholdHC.CapIdentification.MomentCoordinates
import ThresholdHC.CapIdentification.OddPolynomials
import ThresholdHC.CapIdentification.OrthogonalContrast
import ThresholdHC.CapIdentification.PolynomialL2
import ThresholdHC.CapIdentification.PrefixBasis
import ThresholdHC.CapIdentification.PrefixRepresentation
import ThresholdHC.CapIdentification.RareContrast
import ThresholdHC.CapIdentification.StoppedMatching
import ThresholdHC.CapIdentification.SupportIdentification
import ThresholdHC.CapIdentification.TerminalMoments
import ThresholdHC.StoppingProgram.Bellman
import ThresholdHC.StoppingProgram.FlowBasics
import ThresholdHC.StoppingProgram.FlowBounds
import ThresholdHC.StoppingProgram.FullCapFlow
import ThresholdHC.StoppingProgram.Model
import ThresholdHC.StoppingProgram.Perspective
import ThresholdHC.StoppingProgram.PriceRatio
import ThresholdHC.StoppingProgram.RareCompactness
import ThresholdHC.StoppingProgram.Specification

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open ThresholdHC.StoppingProgram ThresholdHC.CapIdentification
example : ∀ (r w : ℕ → ℕ → ℝ) (κ : ℝ) (d : ℕ),
    (∀ a : StopTree d × StopTree d,
      rootInformation r d a-κ*rootWork w d a ≤ rootBellman r w κ d) ∧
    ∃ a : StopTree d × StopTree d,
      rootInformation r d a-κ*rootWork w d a = rootBellman r w κ d := rootBellman_maximum
example : ∀ (r w : ℕ → ℕ → ℝ), (∀ n k, 0 ≤ w n k) → ∀ d κ,
    rootBellman r w κ d = 0 ↔ κ = ratioValue (rootInformation r d) (rootWork w d) := rootBellman_zero_iff
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → intensity f = 0 → ∀ s : CountState N,
    f.stopWeight s = 0 ∧ f.continueWeight s = 0 ∧ f.outputWeight s = 0 := flow_zero_intensity
example : ∀ {m : ℕ} (d : Fin m → ℝ) (N : ℕ), (∀ i, 0 < d i) → Function.Injective d → 0 < m →
    ((∀ g : Fin m → ℝ,
      (∀ j : Fin ((N+1)/2), (∑ i, g i*(d i)^(2*j.val+1)) = 0) → (∑ i, g i) = 0) ↔
        2*m-1 ≤ N) := moments_cap_threshold
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsFiniteMeasure μ]
    (qH qL : ThresholdHC.Tier6.SignLaw) (N : ℕ),
    (∀ j : Fin ((N+1)/2), ∫ d, (qH.val d-qL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0) ↔
      ∀ s : CountState N, countCoefficient μ qH s = countCoefficient μ qL s :=
  odd_moments_iff_count_match
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    informationRatio μ N Q = 0 ↔
      ∀ j : Fin ((N+1)/2), ∫ d, (Q.high.val d-Q.low.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0 :=
  informationRatio_zero_iff_moments
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (N : ℕ) (S : Finset ThresholdHC.Tier6.Gap),
    μ.support = (S:Set ThresholdHC.Tier6.Gap) → 0 < S.card →
    ((∀ qH qL : ThresholdHC.Tier6.SignLaw,
      ThresholdHC.RareAboveTwo.RarePrior μ ρ qH → ThresholdHC.RareAboveTwo.RarePrior μ ρ qL →
      (∀ s : CountState N, countCoefficient μ qH s = countCoefficient μ qL s) →
      ThresholdHC.Tier6.signMean μ qH.val = ThresholdHC.Tier6.signMean μ qL.val) ↔
      2*S.card-1 ≤ N) := finite_support_target_threshold
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ],
    μ.support.Infinite → ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ N : ℕ,
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ B : ℝ, c ≤ programSquared μ ρ B N := infinite_support_program_floor
example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (qH qL : ThresholdHC.Tier6.SignLaw) (N : ℕ),
    (∀ j : Fin ((N+1)/2), ∫ d, (qH.val d-qL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0) →
    ∀ (A : ThresholdHC.CriticalEntropy.StoppedProcedure R E), (∀ z, A.stop z ≤ N) →
    ThresholdHC.CriticalEntropy.cappedTranscriptLaw μ ν
      (ThresholdHC.ObservableSimulation.gapParameter false) (ThresholdHC.ObservableSimulation.gapParameter true)
      (ThresholdHC.ObservableSimulation.signUnit qH) A N =
    ThresholdHC.CriticalEntropy.cappedTranscriptLaw μ ν
      (ThresholdHC.ObservableSimulation.gapParameter false) (ThresholdHC.ObservableSimulation.gapParameter true)
      (ThresholdHC.ObservableSimulation.signUnit qL) A N := stopped_law_eq_of_odd_moments
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ N : ℕ, 0 < N →
    (∃ qH qL : ThresholdHC.Tier6.SignLaw,
      ThresholdHC.RareAboveTwo.RarePrior μ ρ qH ∧ ThresholdHC.RareAboveTwo.RarePrior μ ρ qL ∧
      (∀ j : Fin ((N+1)/2), ∫ d, (qH.val d-qL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0) ∧
      capDiameter μ ρ N = ThresholdHC.Tier6.signMean μ qH.val-ThresholdHC.Tier6.signMean μ qL.val ∧
      ∀ rH rL : ThresholdHC.Tier6.SignLaw,
        ThresholdHC.RareAboveTwo.RarePrior μ ρ rH → ThresholdHC.RareAboveTwo.RarePrior μ ρ rL →
        (∀ j : Fin ((N+1)/2), ∫ d, (rH.val d-rL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0) →
        ThresholdHC.Tier6.signMean μ rH.val-ThresholdHC.Tier6.signMean μ rL.val ≤ capDiameter μ ρ N) ∧
    Tendsto (fun B : ℝ => programValue μ ρ B N) atTop (𝓝 (ENNReal.ofReal (capDiameter μ ρ N/2))) ∧
    (∀ S : Finset ThresholdHC.Tier6.Gap, μ.support = (S:Set ThresholdHC.Tier6.Gap) → 0 < S.card →
      (capDiameter μ ρ N = 0 ↔ 2*S.card-1 ≤ N)) ∧
    (μ.support.Infinite → 0 < capDiameter μ ρ N) := fixed_cap_identification

#print axioms ThresholdHC.CapIdentification.CapDeterminesTarget
#print axioms ThresholdHC.CapIdentification.CountMatch
#print axioms ThresholdHC.CapIdentification.MomentsDetermineTarget
#print axioms ThresholdHC.CapIdentification.OddMomentMatch
#print axioms ThresholdHC.CapIdentification.affine_bias_approximation
#print axioms ThresholdHC.CapIdentification.annihilates_prefix_iff
#print axioms ThresholdHC.CapIdentification.annihilates_prefixes_below
#print axioms ThresholdHC.CapIdentification.approximate_diameter_program_upper
#print axioms ThresholdHC.CapIdentification.arrayAt_const_mul
#print axioms ThresholdHC.CapIdentification.capDiameter
#print axioms ThresholdHC.CapIdentification.capDiameter_antitone
#print axioms ThresholdHC.CapIdentification.capDiameter_attained
#print axioms ThresholdHC.CapIdentification.capDiameter_bounds
#print axioms ThresholdHC.CapIdentification.capDiameter_program_floor
#print axioms ThresholdHC.CapIdentification.capDiameter_zero_iff_target
#print axioms ThresholdHC.CapIdentification.cap_threshold_equivalence
#print axioms ThresholdHC.CapIdentification.centeredPower
#print axioms ThresholdHC.CapIdentification.centeredPower_degree
#print axioms ThresholdHC.CapIdentification.centeredPower_eval_minus
#print axioms ThresholdHC.CapIdentification.centeredPower_eval_plus
#print axioms ThresholdHC.CapIdentification.centered_annihilation_iff
#print axioms ThresholdHC.CapIdentification.compact_affine_bias
#print axioms ThresholdHC.CapIdentification.compact_affine_recovery
#print axioms ThresholdHC.CapIdentification.constant_not_in_oddL2Span
#print axioms ThresholdHC.CapIdentification.constant_not_in_oddL2Span_infinite
#print axioms ThresholdHC.CapIdentification.constant_not_in_odd_span
#print axioms ThresholdHC.CapIdentification.countCoefficient_difference
#print axioms ThresholdHC.CapIdentification.countCoefficient_eq_iff_contrast
#print axioms ThresholdHC.CapIdentification.countCoefficient_le_choose
#print axioms ThresholdHC.CapIdentification.countCoefficient_polynomial
#print axioms ThresholdHC.CapIdentification.countEnvelope
#print axioms ThresholdHC.CapIdentification.countEnvelope_pos
#print axioms ThresholdHC.CapIdentification.countMean_eq_of_count_match
#print axioms ThresholdHC.CapIdentification.countMean_le_envelope
#print axioms ThresholdHC.CapIdentification.countMean_terminal
#print axioms ThresholdHC.CapIdentification.count_match_of_terminal
#print axioms ThresholdHC.CapIdentification.derivativeCore
#print axioms ThresholdHC.CapIdentification.derivativeCore_degree_le
#print axioms ThresholdHC.CapIdentification.exists_count_coefficients
#print axioms ThresholdHC.CapIdentification.exists_max_matching_gap
#print axioms ThresholdHC.CapIdentification.exists_odd_moment_contrast
#print axioms ThresholdHC.CapIdentification.exists_polynomial_moment_contrast
#print axioms ThresholdHC.CapIdentification.exists_prefix_coefficients
#print axioms ThresholdHC.CapIdentification.finite_moment_target_identified
#print axioms ThresholdHC.CapIdentification.finite_support_diameter_zero_iff
#print axioms ThresholdHC.CapIdentification.finite_support_target_of_moments
#print axioms ThresholdHC.CapIdentification.finite_support_target_threshold
#print axioms ThresholdHC.CapIdentification.finset_odd_interpolation
#print axioms ThresholdHC.CapIdentification.fixed_cap_identification
#print axioms ThresholdHC.CapIdentification.fullOutputFlow
#print axioms ThresholdHC.CapIdentification.fullOutputFlow_cone
#print axioms ThresholdHC.CapIdentification.fullOutputFlow_variance_bound
#print axioms ThresholdHC.CapIdentification.fullOutputFlow_work_bound
#print axioms ThresholdHC.CapIdentification.full_output_program_upper
#print axioms ThresholdHC.CapIdentification.functional_eq_coordinate_sum
#print axioms ThresholdHC.CapIdentification.gap_wordLikelihood
#print axioms ThresholdHC.CapIdentification.infinite_support_diameter_pos
#print axioms ThresholdHC.CapIdentification.infinite_support_program_floor
#print axioms ThresholdHC.CapIdentification.infinite_support_rare_indistinguishable
#print axioms ThresholdHC.CapIdentification.infinite_support_target_not_identified
#print axioms ThresholdHC.CapIdentification.informationRatio_pos_of_not_count_match
#print axioms ThresholdHC.CapIdentification.informationRatio_zero_iff_moments
#print axioms ThresholdHC.CapIdentification.informationRatio_zero_of_count_match
#print axioms ThresholdHC.CapIdentification.integrable_polynomial_probability
#print axioms ThresholdHC.CapIdentification.integrable_prefixLikelihood
#print axioms ThresholdHC.CapIdentification.integrable_sign_polynomial
#print axioms ThresholdHC.CapIdentification.integrable_weighted_prefix
#print axioms ThresholdHC.CapIdentification.liftTerminalOutput
#print axioms ThresholdHC.CapIdentification.matchingCoordinatePairs
#print axioms ThresholdHC.CapIdentification.matchingCoordinatePairs_compact
#print axioms ThresholdHC.CapIdentification.matchingCoordinatePairs_nonempty
#print axioms ThresholdHC.CapIdentification.matchingTargetGaps
#print axioms ThresholdHC.CapIdentification.matching_pair_certificate_floor
#print axioms ThresholdHC.CapIdentification.matching_pair_program_floor
#print axioms ThresholdHC.CapIdentification.matching_target_gap_le_twice_bias
#print axioms ThresholdHC.CapIdentification.mem_oddL2Span
#print axioms ThresholdHC.CapIdentification.momentCoordinates
#print axioms ThresholdHC.CapIdentification.momentCoordinates_match_iff
#print axioms ThresholdHC.CapIdentification.momentCoordinates_mem
#print axioms ThresholdHC.CapIdentification.momentCoordinates_none
#print axioms ThresholdHC.CapIdentification.momentCoordinates_some
#print axioms ThresholdHC.CapIdentification.momentPolynomial
#print axioms ThresholdHC.CapIdentification.moments_cap_threshold
#print axioms ThresholdHC.CapIdentification.moments_determine_target_iff
#print axioms ThresholdHC.CapIdentification.nullPolynomialMean
#print axioms ThresholdHC.CapIdentification.nullSignLaw
#print axioms ThresholdHC.CapIdentification.oddL2Span
#print axioms ThresholdHC.CapIdentification.oddL2Span_finite
#print axioms ThresholdHC.CapIdentification.oddMomentMatch_mono
#print axioms ThresholdHC.CapIdentification.oddMomentRepresentative
#print axioms ThresholdHC.CapIdentification.oddMomentRepresentative_degree
#print axioms ThresholdHC.CapIdentification.oddMomentRepresentative_difference
#print axioms ThresholdHC.CapIdentification.oddPolynomial
#print axioms ThresholdHC.CapIdentification.oddPolynomial_derivative_eval
#print axioms ThresholdHC.CapIdentification.oddPolynomial_eval
#print axioms ThresholdHC.CapIdentification.oddPolynomial_eval_zero
#print axioms ThresholdHC.CapIdentification.oddVector
#print axioms ThresholdHC.CapIdentification.odd_centered_prefix_equivalence
#print axioms ThresholdHC.CapIdentification.odd_interpolation
#print axioms ThresholdHC.CapIdentification.odd_level_card_le
#print axioms ThresholdHC.CapIdentification.odd_moments_iff_count_match
#print axioms ThresholdHC.CapIdentification.odd_moments_iff_prefix_contrast
#print axioms ThresholdHC.CapIdentification.original_wordLikelihood_integral
#print axioms ThresholdHC.CapIdentification.outputSquareSum
#print axioms ThresholdHC.CapIdentification.outputSquareSum_ge
#print axioms ThresholdHC.CapIdentification.outputSquareSum_nonneg
#print axioms ThresholdHC.CapIdentification.perspective_strict_pos
#print axioms ThresholdHC.CapIdentification.perspective_zero_left
#print axioms ThresholdHC.CapIdentification.polynomialL2
#print axioms ThresholdHC.CapIdentification.polynomialL2_ae
#print axioms ThresholdHC.CapIdentification.polynomialL2_inner
#print axioms ThresholdHC.CapIdentification.polynomialL2_odd
#print axioms ThresholdHC.CapIdentification.polynomialMomentSet
#print axioms ThresholdHC.CapIdentification.polynomialMomentSet_compact_convex
#print axioms ThresholdHC.CapIdentification.polynomialMomentSet_coordinates
#print axioms ThresholdHC.CapIdentification.polynomialMomentSet_eq_rareMomentSet
#print axioms ThresholdHC.CapIdentification.polynomial_gap_bound
#print axioms ThresholdHC.CapIdentification.polynomial_gap_memLp
#print axioms ThresholdHC.CapIdentification.polynomial_mem_prefix_span
#print axioms ThresholdHC.CapIdentification.polynomial_moment_difference
#print axioms ThresholdHC.CapIdentification.populationPolynomialMean
#print axioms ThresholdHC.CapIdentification.populationPolynomialMean_odd
#print axioms ThresholdHC.CapIdentification.populationPolynomialMean_prefix
#print axioms ThresholdHC.CapIdentification.positive_square_injective
#print axioms ThresholdHC.CapIdentification.prefixLikelihood_le_one
#print axioms ThresholdHC.CapIdentification.prefixPolynomial
#print axioms ThresholdHC.CapIdentification.prefixPolynomial_degree
#print axioms ThresholdHC.CapIdentification.prefixPolynomial_diagonal
#print axioms ThresholdHC.CapIdentification.prefixPolynomial_elevation
#print axioms ThresholdHC.CapIdentification.prefixPolynomial_eval_minus
#print axioms ThresholdHC.CapIdentification.prefixPolynomial_eval_plus
#print axioms ThresholdHC.CapIdentification.programSquared_budget_limit
#print axioms ThresholdHC.CapIdentification.programValue_budget_limit
#print axioms ThresholdHC.CapIdentification.rare_indistinguishable_of_large_support
#print axioms ThresholdHC.CapIdentification.rare_indistinguishable_of_not_in_span
#print axioms ThresholdHC.CapIdentification.rare_priors_of_bounded_contrast
#print axioms ThresholdHC.CapIdentification.signContrast
#print axioms ThresholdHC.CapIdentification.signContrast_apply
#print axioms ThresholdHC.CapIdentification.signContrast_even
#print axioms ThresholdHC.CapIdentification.signContrast_odd
#print axioms ThresholdHC.CapIdentification.signDifference_norm
#print axioms ThresholdHC.CapIdentification.stopped_law_eq_of_odd_moments
#print axioms ThresholdHC.CapIdentification.sum_terminal
#print axioms ThresholdHC.CapIdentification.terminalArray
#print axioms ThresholdHC.CapIdentification.terminal_polynomial_representation
#print axioms ThresholdHC.CapIdentification.topState
#print axioms ThresholdHC.CapIdentification.weightedPolynomialIntegral
#print axioms ThresholdHC.CapIdentification.wordLikelihood_eq_of_count_match
#print axioms ThresholdHC.StoppingProgram.Admissible
#print axioms ThresholdHC.StoppingProgram.AttainedDualStatement
#print axioms ThresholdHC.StoppingProgram.Certificate
#print axioms ThresholdHC.StoppingProgram.CountState
#print axioms ThresholdHC.StoppingProgram.Feasible
#print axioms ThresholdHC.StoppingProgram.FiniteCertificateStatement
#print axioms ThresholdHC.StoppingProgram.Flow
#print axioms ThresholdHC.StoppingProgram.FlowCone
#print axioms ThresholdHC.StoppingProgram.FourPriors
#print axioms ThresholdHC.StoppingProgram.ProgramUpperStatement
#print axioms ThresholdHC.StoppingProgram.StopTree
#print axioms ThresholdHC.StoppingProgram.arrayAt
#print axioms ThresholdHC.StoppingProgram.arrayAt_le_of
#print axioms ThresholdHC.StoppingProgram.arrayAt_zero
#print axioms ThresholdHC.StoppingProgram.bellman
#print axioms ThresholdHC.StoppingProgram.certificateCap
#print axioms ThresholdHC.StoppingProgram.certificateSquared
#print axioms ThresholdHC.StoppingProgram.constantCertificate
#print axioms ThresholdHC.StoppingProgram.constantCertificate_feasible
#print axioms ThresholdHC.StoppingProgram.continuous_bellman
#print axioms ThresholdHC.StoppingProgram.continuous_rootBellman
#print axioms ThresholdHC.StoppingProgram.countCoefficient
#print axioms ThresholdHC.StoppingProgram.countCoefficient_nonneg
#print axioms ThresholdHC.StoppingProgram.countCoefficient_root
#print axioms ThresholdHC.StoppingProgram.countMean
#print axioms ThresholdHC.StoppingProgram.countMean_ge_root
#print axioms ThresholdHC.StoppingProgram.countMean_nonneg
#print axioms ThresholdHC.StoppingProgram.dualRatio
#print axioms ThresholdHC.StoppingProgram.dualValue
#print axioms ThresholdHC.StoppingProgram.flowInformation
#print axioms ThresholdHC.StoppingProgram.flow_continue_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_output_zero_of_stop_zero
#print axioms ThresholdHC.StoppingProgram.flow_stop_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_total_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_work_ge_intensity
#print axioms ThresholdHC.StoppingProgram.flow_zero_intensity
#print axioms ThresholdHC.StoppingProgram.fullCapFlow
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_cone
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_intensity
#print axioms ThresholdHC.StoppingProgram.fullCap_arrayAt
#print axioms ThresholdHC.StoppingProgram.informationRatio
#print axioms ThresholdHC.StoppingProgram.intensity
#print axioms ThresholdHC.StoppingProgram.le_priceValue
#print axioms ThresholdHC.StoppingProgram.le_ratioValue
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
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood_nonneg
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
#print axioms ThresholdHC.StoppingProgram.rootBellman
#print axioms ThresholdHC.StoppingProgram.rootBellman_eq_priceValue
#print axioms ThresholdHC.StoppingProgram.rootBellman_maximum
#print axioms ThresholdHC.StoppingProgram.rootBellman_strictAnti
#print axioms ThresholdHC.StoppingProgram.rootBellman_zero_iff
#print axioms ThresholdHC.StoppingProgram.rootInformation
#print axioms ThresholdHC.StoppingProgram.rootState
#print axioms ThresholdHC.StoppingProgram.rootWork
#print axioms ThresholdHC.StoppingProgram.rootWork_bounds
#print axioms ThresholdHC.StoppingProgram.state_eq_root
#print axioms ThresholdHC.StoppingProgram.stopTree_fintype
#print axioms ThresholdHC.StoppingProgram.stopTree_nonempty
#print axioms ThresholdHC.StoppingProgram.treeInformation
#print axioms ThresholdHC.StoppingProgram.treeScore
#print axioms ThresholdHC.StoppingProgram.treeScore_eq
#print axioms ThresholdHC.StoppingProgram.treeScore_le_bellman
#print axioms ThresholdHC.StoppingProgram.treeWork
#print axioms ThresholdHC.StoppingProgram.treeWork_le
#print axioms ThresholdHC.StoppingProgram.treeWork_nonneg
#print axioms ThresholdHC.StoppingProgram.zeroFlow
#print axioms ThresholdHC.StoppingProgram.zeroFlow_cone
