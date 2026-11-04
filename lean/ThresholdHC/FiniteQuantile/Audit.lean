import ThresholdHC.FiniteQuantile.FiniteInformation
import ThresholdHC.FiniteQuantile.PosteriorEnergy
import ThresholdHC.FiniteQuantile.SmallBudget
import ThresholdHC.FiniteQuantile.Specification
import ThresholdHC.FiniteQuantile.TailPair

/-! Exact types and transitive axioms for the verified direct-proof components. -/

open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile
open ThresholdHC.FiniteQuantile

example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hB : 0 < B) (hsmall : B * ρ ≤ 1) :
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) * closedQuantileValue μ ρ B ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ 30001 * closedQuantileValue μ ρ B :=
  small_budget_explicit_bounds μ hρ hρ4 hB hsmall

example (g : Gap) (cap : ℕ) (a : ThresholdHC.StoppingProgram.StopTree cap) :
    ThresholdHC.StoppingProgram.treeInformation (prefixEnergy g) cap 0 0 a ≤
      4*(g:ℝ)^2 * ThresholdHC.StoppingProgram.treeWork (midpointMass g) cap 0 0 a :=
  stopped_posterior_energy g cap a

example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ h : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hh : 0 ≤ h) (s : Bool) :
    signMean μ (tailEndpoint μ hρ hρ1 hh s).val =
      ρ/2 + (if s then tailModulus (quantileTail μ ρ) h else -tailModulus (quantileTail μ ρ) h)/16 :=
  tailEndpoint_mean μ hρ hρ1 hh s

#print axioms ThresholdHC.FiniteQuantile.DirectFiniteLawStatement
#print axioms ThresholdHC.FiniteQuantile.ExplicitBounds
#print axioms ThresholdHC.FiniteQuantile.cutWeight
#print axioms ThresholdHC.FiniteQuantile.cutWeight_range
#print axioms ThresholdHC.FiniteQuantile.fractional_word_bound
#print axioms ThresholdHC.FiniteQuantile.informationRatio_of_potential
#print axioms ThresholdHC.FiniteQuantile.integrable_of_finite_gap_support
#print axioms ThresholdHC.FiniteQuantile.integral_cutWeight
#print axioms ThresholdHC.FiniteQuantile.measurable_cutWeight
#print axioms ThresholdHC.FiniteQuantile.midpointMass
#print axioms ThresholdHC.FiniteQuantile.mixture_quadratic_bound
#print axioms ThresholdHC.FiniteQuantile.posteriorEnergy
#print axioms ThresholdHC.FiniteQuantile.posteriorEnergy_step
#print axioms ThresholdHC.FiniteQuantile.prefixEnergy
#print axioms ThresholdHC.FiniteQuantile.prefixEnergy_step
#print axioms ThresholdHC.FiniteQuantile.small_budget_explicit_bounds
#print axioms ThresholdHC.FiniteQuantile.small_budget_lower
#print axioms ThresholdHC.FiniteQuantile.stopped_posterior_energy
#print axioms ThresholdHC.FiniteQuantile.tailEndpoint
#print axioms ThresholdHC.FiniteQuantile.tailEndpoint_mean
#print axioms ThresholdHC.FiniteQuantile.tailEndpoint_rare
#print axioms ThresholdHC.FiniteQuantile.tailEpsilon
#print axioms ThresholdHC.FiniteQuantile.tailEpsilon_bounds
