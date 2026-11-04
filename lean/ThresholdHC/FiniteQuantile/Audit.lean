import ThresholdHC.FiniteQuantile.Allocation
import ThresholdHC.FiniteQuantile.Core
import ThresholdHC.FiniteQuantile.CoreRisk
import ThresholdHC.FiniteQuantile.CoreValue
import ThresholdHC.FiniteQuantile.Filter
import ThresholdHC.FiniteQuantile.FilteredPacking
import ThresholdHC.FiniteQuantile.FiniteInformation
import ThresholdHC.FiniteQuantile.Full
import ThresholdHC.FiniteQuantile.Operational
import ThresholdHC.FiniteQuantile.PosteriorEnergy
import ThresholdHC.FiniteQuantile.SmallBudget
import ThresholdHC.FiniteQuantile.Specification
import ThresholdHC.FiniteQuantile.TailInformation
import ThresholdHC.FiniteQuantile.TailPair
import ThresholdHC.FiniteQuantile.TailRisk

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

example (μ : Measure Gap) [IsProbabilityMeasure μ] (hs : μ.support.Finite)
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal (tailModulus (quantileTail μ ρ) (ThresholdHC.EntropyTailQuantile.budgetScale B)/32) ≤
      rareMinimaxRisk μ ρ B :=
  quantile_tail_lower μ hs hρ hρ4 hB

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ.support.Finite →
    ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
      ENNReal.ofReal ((10:ℝ)⁻¹^20) * closedQuantileValue μ ρ B ≤ rareMinimaxRisk μ ρ B ∧
        rareMinimaxRisk μ ρ B ≤ 30001 * closedQuantileValue μ ρ B :=
  direct_finite_law

example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ (S : Type) (_ : MeasurableSpace S) (A : AdaptiveEstimator S),
      RareBudget μ A ρ B ∧ rareRisk μ A ρ ≤ 30001 * closedQuantileValue μ ρ B :=
  observable_estimator μ hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (hs : μ.support.Finite)
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    {S : Type} [MeasurableSpace S] (A : AdaptiveEstimator S) (hb : RareBudget μ A ρ B) :
    ENNReal.ofReal ((10:ℝ)⁻¹^20) * closedQuantileValue μ ρ B ≤ rareRisk μ A ρ :=
  every_estimator_lower μ hs hρ hρ4 hB A hb

#print axioms ThresholdHC.FiniteQuantile.DirectFiniteLawStatement
#print axioms ThresholdHC.FiniteQuantile.ExplicitBounds
#print axioms ThresholdHC.FiniteQuantile.above_threshold_lower
#print axioms ThresholdHC.FiniteQuantile.annular_root_constant
#print axioms ThresholdHC.FiniteQuantile.certificate_root_bound
#print axioms ThresholdHC.FiniteQuantile.closedQuantile_le_tail_core
#print axioms ThresholdHC.FiniteQuantile.core_entropy_le_prefix
#print axioms ThresholdHC.FiniteQuantile.core_observable_bound
#print axioms ThresholdHC.FiniteQuantile.cutWeight
#print axioms ThresholdHC.FiniteQuantile.cutWeight_range
#print axioms ThresholdHC.FiniteQuantile.direct_finite_law
#print axioms ThresholdHC.FiniteQuantile.discardedBand
#print axioms ThresholdHC.FiniteQuantile.discarded_entropy
#print axioms ThresholdHC.FiniteQuantile.every_estimator_lower
#print axioms ThresholdHC.FiniteQuantile.filtered_core_certificate_bound
#print axioms ThresholdHC.FiniteQuantile.filtered_prefix_certificate
#print axioms ThresholdHC.FiniteQuantile.fractional_word_bound
#print axioms ThresholdHC.FiniteQuantile.full_rarity_allocation
#print axioms ThresholdHC.FiniteQuantile.informationRatio_of_potential
#print axioms ThresholdHC.FiniteQuantile.integrable_of_finite_gap_support
#print axioms ThresholdHC.FiniteQuantile.integral_cutWeight
#print axioms ThresholdHC.FiniteQuantile.measurable_cutWeight
#print axioms ThresholdHC.FiniteQuantile.midpointMass
#print axioms ThresholdHC.FiniteQuantile.mixture_quadratic_bound
#print axioms ThresholdHC.FiniteQuantile.observable_estimator
#print axioms ThresholdHC.FiniteQuantile.posteriorEnergy
#print axioms ThresholdHC.FiniteQuantile.posteriorEnergy_step
#print axioms ThresholdHC.FiniteQuantile.prefixCoreEntropy
#print axioms ThresholdHC.FiniteQuantile.prefixCoreEntropy_nonneg
#print axioms ThresholdHC.FiniteQuantile.prefixEnergy
#print axioms ThresholdHC.FiniteQuantile.prefixEnergy_step
#print axioms ThresholdHC.FiniteQuantile.quantileTail_threshold_floor
#print axioms ThresholdHC.FiniteQuantile.quantile_tail_lower
#print axioms ThresholdHC.FiniteQuantile.relative_log_square
#print axioms ThresholdHC.FiniteQuantile.small_budget_explicit_bounds
#print axioms ThresholdHC.FiniteQuantile.small_budget_lower
#print axioms ThresholdHC.FiniteQuantile.stopped_posterior_energy
#print axioms ThresholdHC.FiniteQuantile.tailEndpoint
#print axioms ThresholdHC.FiniteQuantile.tailEndpoint_mean
#print axioms ThresholdHC.FiniteQuantile.tailEndpoint_rare
#print axioms ThresholdHC.FiniteQuantile.tailEpsilon
#print axioms ThresholdHC.FiniteQuantile.tailEpsilon_bounds
#print axioms ThresholdHC.FiniteQuantile.tail_information_ratio
