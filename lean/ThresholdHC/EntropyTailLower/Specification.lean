import ThresholdHC.CriticalAllSizes.SingleGap
import ThresholdHC.EntropyTailQuantile.CostEntropy

/-! Supporting statistical target for the entropy-tail lower bound.
This target does not assert the population minimax lower bound. It charges
actual negative-sign work of a single observable test with a common seed.
The coefficient is deliberately weaker than the paper's 214. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.CriticalEntropy

def WeightedSignEntropyStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
    (A : SignTest R) (K : ℕ) (d : Fin K → EntropyGap),
    (∀ i j, j.val = i.val + 1 → 2 * (d j : ℝ) ≤ (d i : ℝ)) →
    (∀ i, expectedSignTestWork ν (signParameter (d i) false) A ≠ ∞) →
    (∀ i b, (ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).real
      {z | A.output z ≠ b} ≤ 1 / 10) →
    ∀ a : Fin K → ℝ, (∀ i, 0 ≤ a i) →
      ThresholdHC.EntropyTailQuantile.costEntropy a ≤
        4096 * ∑ i, a i * ((d i : ℝ)^2 *
          (expectedSignTestWork ν (signParameter (d i) false) A).toReal)

end ThresholdHC.EntropyTailLower
