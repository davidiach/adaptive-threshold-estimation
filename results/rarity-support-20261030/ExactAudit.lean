import ThresholdHC.StoppingProgram.RareCompactness
import ThresholdHC.StoppingProgram.CompactMaximum
import ThresholdHC.StoppingProgram.FunctionMomentImage
import ThresholdHC.StoppingProgram.Slater
import ThresholdHC.StoppingProgram.RarityMultiplier
import ThresholdHC.StoppingProgram.RaritySupport
import ThresholdHC.StoppingProgram.RarityOptimality
import ThresholdHC.StoppingProgram.FractionalCutoff
import ThresholdHC.StoppingProgram.RarityTheorem

open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
example : ∀ (μ : Measure Gap) (ρ : ℝ) (f : Gap → ℝ),
    rareFunctional μ ρ f = sSup {r : ℝ | ∃ q : SignLaw,
      ThresholdHC.RareAboveTwo.RarePrior μ ρ q ∧ r = ∫ d, q.val d*f d ∂μ} := rareFunctional_eq_sSup
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ M : ℝ), 0 < ρ → 0 ≤ M →
    ∀ f : Gap → ℝ, Measurable f → MemLp f 2 μ → (∀ᵐ d ∂μ, f d ≤ M) →
    ∃ (ell c : ℝ) (q : SignLaw), 0 ≤ ell ∧ ell ≤ M ∧ 0 ≤ c ∧ c ≤ 1 ∧
      (∀ d, q.val d = if ell < f d then 1 else if f d = ell then c else 0) ∧
      signMean μ q.val ≤ ρ ∧
      sSup {r : ℝ | ∃ p : SignLaw, signMean μ p.val ≤ ρ ∧ r = ∫ d, p.val d*f d ∂μ} =
        ∫ d, q.val d*f d ∂μ ∧
      (∫ d, q.val d*f d ∂μ) = ρ*ell+∫ d, max (f d-ell) 0 ∂μ ∧
      (∀ t : ℝ, 0 ≤ t → ρ*ell+(∫ d, max (f d-ell) 0 ∂μ) ≤
        ρ*t+∫ d, max (f d-t) 0 ∂μ) ∧
      (0 < ell → signMean μ q.val = ρ) :=
  fun μ _ ρ M hρ hM f hf hLp hb => fractional_rarity_support_explicit μ hρ hM f hf hLp hb

#print axioms ThresholdHC.StoppingProgram.bounded_rarity_support_formula
#print axioms ThresholdHC.StoppingProgram.compactMaximum
#print axioms ThresholdHC.StoppingProgram.compactMaximum_attained
#print axioms ThresholdHC.StoppingProgram.compactMaximum_convex
#print axioms ThresholdHC.StoppingProgram.compactMaximum_le_iff
#print axioms ThresholdHC.StoppingProgram.cutoff_prior_decomposition
#print axioms ThresholdHC.StoppingProgram.finite_slater_multipliers
#print axioms ThresholdHC.StoppingProgram.fractionalUpperPrior
#print axioms ThresholdHC.StoppingProgram.fractionalUpperPrior_decomposition
#print axioms ThresholdHC.StoppingProgram.fractional_cutoff_preserves
#print axioms ThresholdHC.StoppingProgram.fractional_rarity_support
#print axioms ThresholdHC.StoppingProgram.fractional_rarity_support_explicit
#print axioms ThresholdHC.StoppingProgram.fractional_rarity_support_of_memLp
#print axioms ThresholdHC.StoppingProgram.functionMomentImage
#print axioms ThresholdHC.StoppingProgram.functionMomentImage_compact_convex
#print axioms ThresholdHC.StoppingProgram.functionMomentImage_nonempty
#print axioms ThresholdHC.StoppingProgram.integrable_prior_function
#print axioms ThresholdHC.StoppingProgram.integrable_sign_prior
#print axioms ThresholdHC.StoppingProgram.le_compactMaximum
#print axioms ThresholdHC.StoppingProgram.levelAverage
#print axioms ThresholdHC.StoppingProgram.levelAverage_properties
#print axioms ThresholdHC.StoppingProgram.levelPriorMass
#print axioms ThresholdHC.StoppingProgram.levelPriorMass_bounds
#print axioms ThresholdHC.StoppingProgram.linear_pi_expansion
#print axioms ThresholdHC.StoppingProgram.prior_excess_integral
#print axioms ThresholdHC.StoppingProgram.prior_excess_le_positive
#print axioms ThresholdHC.StoppingProgram.prior_function_le_rareFunctional
#print axioms ThresholdHC.StoppingProgram.prior_function_upper_tail
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
#print axioms ThresholdHC.StoppingProgram.upperLevelPrior
#print axioms ThresholdHC.StoppingProgram.upperLevelPrior_excess
#print axioms ThresholdHC.StoppingProgram.upper_tail_equality_cutoff
