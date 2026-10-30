import ThresholdHC.EntropyTail.Model

/-! Full target types for the entropy–tail law (v6 Theorem 13.2) in the
unchanged observable rare-event experiment of `ThresholdHC.RareAboveTwo`.
Every probability law on `(0,1/2]`, `0 < ρ ≤ 1/4` and every positive budget.
Budgets count actual flips, rarity is global and magnitudes and signs stay
hidden. The constants are universal; the paper's explicit constants are not
targets. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- Theorem 13.2: `c K ≤ R ≤ C K` with universal constants. -/
def EntropyTailLawStatement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      ENNReal.ofReal c * selection μ ρ B ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal C * selection μ ρ B

/-- Theorem 13.3, the three-piece observable upper bound. -/
def EntropyTailUpperStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal C * selection μ ρ B

/-- Theorem E.1, the matching lower bound. -/
def EntropyTailLowerStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      ENNReal.ofReal c * selection μ ρ B ≤ rareMinimaxRisk μ ρ B

/-- Lemma 13.1: hard measurable assignments `σ = μ|S` attain the same infimum. -/
def HardSelectionStatement : Prop :=
  ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    (⨅ (σ : Measure Gap) (_ : σ ≤ μ), selectionObjective μ ρ B σ) =
      ⨅ (S : Set Gap) (_ : MeasurableSet S), selectionObjective μ ρ B (μ.restrict S)

/-- The display after Lemma 13.1: `K ≤ min{ρ, ω_μ(B^{-1/2}), √(ρΓ_μ/B)}`. -/
def SelectionBoundsStatement : Prop :=
  ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    selection μ ρ B ≤ ENNReal.ofReal ρ ∧
    selection μ ρ B ≤ tailCost μ (1 / Real.sqrt B) ∧
    selection μ ρ B ≤ ENNReal.ofReal (1 / Real.sqrt B) * (ENNReal.ofReal ρ * gamma μ) ^ (1/2 : ℝ)

/-- On a single magnitude the functional is exactly the single-gap rate
`min{ρ, √ρ/(d√B)}`, the rate of the above-two theorem at `a = d`. -/
def SingleAtomStatement : Prop :=
  ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → ∀ d : Gap,
    selection (Measure.dirac d) ρ B = ENNReal.ofReal (aboveTwoRate (d : ℝ) ρ B)

/-- Budgets up to one flip leave only the trivial rate `ρ`. -/
def SmallBudgetStatement : Prop :=
  ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → B ≤ 1 →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], selection μ ρ B = ENNReal.ofReal ρ

/-- The functional is finite, positive and not identically the trivial rate. -/
def EntropyTailNonvacuityStatement : Prop :=
  (∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    0 < selection μ ρ B ∧ selection μ ρ B < ∞) ∧
  ∃ (μ : Measure Gap) (_ : IsProbabilityMeasure μ) (ρ B : ℝ),
    0 < ρ ∧ ρ ≤ 1/4 ∧ 0 < B ∧ selection μ ρ B < ENNReal.ofReal ρ

end ThresholdHC.EntropyTail
