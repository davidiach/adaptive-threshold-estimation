import ThresholdHC.StoppingProgram.RareCompactness
import ThresholdHC.StoppingProgram.CompactMaximum
import ThresholdHC.StoppingProgram.FunctionMomentImage
import ThresholdHC.StoppingProgram.Slater
import ThresholdHC.StoppingProgram.RarityMultiplier
import ThresholdHC.StoppingProgram.RaritySupport
import ThresholdHC.StoppingProgram.RarityOptimality
import ThresholdHC.StoppingProgram.FractionalCutoff
import ThresholdHC.StoppingProgram.RarityTheorem
import ThresholdHC.StoppingProgram.Perspective
import ThresholdHC.StoppingProgram.Model
import ThresholdHC.StoppingProgram.FlowBasics
import ThresholdHC.StoppingProgram.FlowBounds
import ThresholdHC.StoppingProgram.FullCapFlow
import ThresholdHC.StoppingProgram.MomentImage
import ThresholdHC.StoppingProgram.RobustRarity
import ThresholdHC.StoppingProgram.FiniteProgram

open MeasureTheory Polynomial
open scoped ENNReal BigOperators
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)
example : ∀ {I : Type} [Fintype I] (μ : Measure Gap) (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 ≤ w i) → (μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)) →
    ∀ (ρ : ℝ) (P : ℝ[X]) (z : ℝ),
    (∃ (ell : ℝ) (u : I → ℝ), 0 ≤ ell ∧ (∀ i, 0 ≤ u i ∧ P.eval (d i:ℝ)-ell ≤ u i) ∧
      ρ*ell+∑ i, w i*u i ≤ z) ↔
    ∃ ell, 0 ≤ ell ∧ ρ*ell+(∫ x : Gap, max (P.eval (x:ℝ)-ell) 0 ∂μ) ≤ z :=
  by
    intro I inst μ w d hw hμ ρ P z
    exact finiteTailBound_iff μ w d hw hμ ρ P z
example : ∀ {I : Type} [Fintype I] {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap), (∀ i, 0 ≤ w i) →
    (μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)) →
    ∀ ρ B, 0 < ρ → ∀ C : Certificate N,
    Feasible μ ρ B C ↔ FlowCone C.flow ∧ 0 ≤ C.bias ∧ 0 ≤ C.variance ∧
      FiniteTailBound w d ρ (biasPolynomial C)
        (C.bias-(C.offset+finiteNullMean w d C.flow.outputWeight)) ∧
      FiniteTailBound w d ρ (-biasPolynomial C)
        (C.bias+(C.offset+finiteNullMean w d C.flow.outputWeight)) ∧
      FiniteTailBound w d ρ (countMeanPolynomial C.flow.momentWeight)
        (C.variance-finiteNullMean w d C.flow.momentWeight) ∧
      FiniteTailBound w d ρ (countMeanPolynomial C.flow.continueWeight)
        (B-finiteNullMean w d C.flow.continueWeight) :=
  by
    intro I inst N μ prob w d hw hμ ρ B hρ C
    exact feasible_iff_finite_program μ w d hw hμ hρ C

#print axioms ThresholdHC.StoppingProgram.Admissible
#print axioms ThresholdHC.StoppingProgram.Certificate
#print axioms ThresholdHC.StoppingProgram.CountState
#print axioms ThresholdHC.StoppingProgram.Feasible
#print axioms ThresholdHC.StoppingProgram.FiniteTailBound
#print axioms ThresholdHC.StoppingProgram.Flow
#print axioms ThresholdHC.StoppingProgram.FlowCone
#print axioms ThresholdHC.StoppingProgram.FourPriors
#print axioms ThresholdHC.StoppingProgram.arrayAt
#print axioms ThresholdHC.StoppingProgram.arrayAt_le_of
#print axioms ThresholdHC.StoppingProgram.arrayAt_zero
#print axioms ThresholdHC.StoppingProgram.biasPolynomial
#print axioms ThresholdHC.StoppingProgram.bounded_rarity_support_formula
#print axioms ThresholdHC.StoppingProgram.certificateSquared
#print axioms ThresholdHC.StoppingProgram.certificate_bias_affine
#print axioms ThresholdHC.StoppingProgram.compactMaximum
#print axioms ThresholdHC.StoppingProgram.compactMaximum_attained
#print axioms ThresholdHC.StoppingProgram.compactMaximum_convex
#print axioms ThresholdHC.StoppingProgram.compactMaximum_le_iff
#print axioms ThresholdHC.StoppingProgram.constantCertificate
#print axioms ThresholdHC.StoppingProgram.constantCertificate_feasible
#print axioms ThresholdHC.StoppingProgram.countCoefficient
#print axioms ThresholdHC.StoppingProgram.countCoefficient_affine
#print axioms ThresholdHC.StoppingProgram.countCoefficient_nonneg
#print axioms ThresholdHC.StoppingProgram.countCoefficient_root
#print axioms ThresholdHC.StoppingProgram.countContrastPolynomial
#print axioms ThresholdHC.StoppingProgram.countContrastPolynomial_eval
#print axioms ThresholdHC.StoppingProgram.countMean
#print axioms ThresholdHC.StoppingProgram.countMeanPolynomial
#print axioms ThresholdHC.StoppingProgram.countMeanPolynomial_eval
#print axioms ThresholdHC.StoppingProgram.countMean_affine
#print axioms ThresholdHC.StoppingProgram.countMean_ge_root
#print axioms ThresholdHC.StoppingProgram.countMean_nonneg
#print axioms ThresholdHC.StoppingProgram.cutoff_prior_decomposition
#print axioms ThresholdHC.StoppingProgram.dualRatio
#print axioms ThresholdHC.StoppingProgram.dualValue
#print axioms ThresholdHC.StoppingProgram.feasible_iff_finite_program
#print axioms ThresholdHC.StoppingProgram.feasible_iff_four_cutoffs
#print axioms ThresholdHC.StoppingProgram.finiteNullMean
#print axioms ThresholdHC.StoppingProgram.finiteNullMean_eq
#print axioms ThresholdHC.StoppingProgram.finiteTailBound_iff
#print axioms ThresholdHC.StoppingProgram.finite_law_integral
#print axioms ThresholdHC.StoppingProgram.finite_law_tail
#print axioms ThresholdHC.StoppingProgram.finite_slater_multipliers
#print axioms ThresholdHC.StoppingProgram.flowInformation
#print axioms ThresholdHC.StoppingProgram.flow_continue_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_output_zero_of_stop_zero
#print axioms ThresholdHC.StoppingProgram.flow_stop_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_total_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_work_ge_intensity
#print axioms ThresholdHC.StoppingProgram.flow_zero_intensity
#print axioms ThresholdHC.StoppingProgram.fractionalUpperPrior
#print axioms ThresholdHC.StoppingProgram.fractionalUpperPrior_decomposition
#print axioms ThresholdHC.StoppingProgram.fractional_cutoff_preserves
#print axioms ThresholdHC.StoppingProgram.fractional_rarity_support
#print axioms ThresholdHC.StoppingProgram.fractional_rarity_support_explicit
#print axioms ThresholdHC.StoppingProgram.fractional_rarity_support_of_memLp
#print axioms ThresholdHC.StoppingProgram.fullCapFlow
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_cone
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_intensity
#print axioms ThresholdHC.StoppingProgram.fullCap_arrayAt
#print axioms ThresholdHC.StoppingProgram.functionMomentImage
#print axioms ThresholdHC.StoppingProgram.functionMomentImage_compact_convex
#print axioms ThresholdHC.StoppingProgram.functionMomentImage_nonempty
#print axioms ThresholdHC.StoppingProgram.informationRatio
#print axioms ThresholdHC.StoppingProgram.integrable_prior_function
#print axioms ThresholdHC.StoppingProgram.integrable_sign_prior
#print axioms ThresholdHC.StoppingProgram.intensity
#print axioms ThresholdHC.StoppingProgram.le_compactMaximum
#print axioms ThresholdHC.StoppingProgram.levelAverage
#print axioms ThresholdHC.StoppingProgram.levelAverage_properties
#print axioms ThresholdHC.StoppingProgram.levelPriorMass
#print axioms ThresholdHC.StoppingProgram.levelPriorMass_bounds
#print axioms ThresholdHC.StoppingProgram.linear_pi_expansion
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
#print axioms ThresholdHC.StoppingProgram.polynomialTail
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood_nonneg
#print axioms ThresholdHC.StoppingProgram.priorCoordinates
#print axioms ThresholdHC.StoppingProgram.priorMomentImage
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_compact_convex
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_mem
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_nonempty
#print axioms ThresholdHC.StoppingProgram.prior_excess_integral
#print axioms ThresholdHC.StoppingProgram.prior_excess_le_positive
#print axioms ThresholdHC.StoppingProgram.prior_function_le_rareFunctional
#print axioms ThresholdHC.StoppingProgram.prior_function_upper_tail
#print axioms ThresholdHC.StoppingProgram.programSquared
#print axioms ThresholdHC.StoppingProgram.programSquared_finite
#print axioms ThresholdHC.StoppingProgram.programSquared_le_constant
#print axioms ThresholdHC.StoppingProgram.programValue
#print axioms ThresholdHC.StoppingProgram.quadratic_div_add_le
#print axioms ThresholdHC.StoppingProgram.rareFunctional
#print axioms ThresholdHC.StoppingProgram.rareFunctional_attained
#print axioms ThresholdHC.StoppingProgram.rareFunctional_eq_sSup
#print axioms ThresholdHC.StoppingProgram.rareFunctional_upper_tail
#print axioms ThresholdHC.StoppingProgram.rareMomentSet
#print axioms ThresholdHC.StoppingProgram.rareMomentSet_compact_convex
#print axioms ThresholdHC.StoppingProgram.rareMomentSet_eq_half_image
#print axioms ThresholdHC.StoppingProgram.rarity_function_multiplier
#print axioms ThresholdHC.StoppingProgram.rarity_support_formula
#print axioms ThresholdHC.StoppingProgram.rarity_support_formula_bounded_above
#print axioms ThresholdHC.StoppingProgram.robust_polynomial_bound_iff
#print axioms ThresholdHC.StoppingProgram.rootState
#print axioms ThresholdHC.StoppingProgram.state_eq_root
#print axioms ThresholdHC.StoppingProgram.upperLevelPrior
#print axioms ThresholdHC.StoppingProgram.upperLevelPrior_excess
#print axioms ThresholdHC.StoppingProgram.upper_tail_equality_cutoff
#print axioms ThresholdHC.StoppingProgram.zeroFlow
#print axioms ThresholdHC.StoppingProgram.zeroFlow_cone
