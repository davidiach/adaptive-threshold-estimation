import ThresholdHC.EntropyTail.Model

/-! Theorem 5 of the certified-selection note, for the original entropy-tail objective. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.BandwiseSuffix
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- On the given support, membership is upward closed inside each canonical band. -/
def IsBandSuffix (support chosen : Set Gap) : Prop :=
  ∀ (j : ℕ) ⦃x y : Gap⦄, x ∈ chosen → y ∈ support → x ∈ band j → y ∈ band j →
    (x : ℝ) < (y : ℝ) → y ∈ chosen

/-- A hard suffix attains the uncapped minimum against every submeasure and gives the capped K. -/
def BandwiseSuffixStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ.support.Finite →
    ∀ {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/4 → 0 < B →
      ∃ S : Finset Gap, (S : Set Gap) ⊆ μ.support ∧ IsBandSuffix μ.support S ∧
        (∀ σ : Measure Gap, σ ≤ μ →
          selectionObjective μ ρ B (μ.restrict S) ≤ selectionObjective μ ρ B σ) ∧
        selection μ ρ B = min (ENNReal.ofReal ρ) (selectionObjective μ ρ B (μ.restrict S))

end ThresholdHC.BandwiseSuffix
