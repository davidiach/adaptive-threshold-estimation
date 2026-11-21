import ThresholdHC.EntropyTail.Model
import ThresholdHC.EntropyTailQuantile.Model

/-! Corollary 6 of the certified-selection note
(`research/2026-10-30-certified-selection/NOTE.md`, "A cheaper global-cut
approximation"; summary table in that package's `README.md`): the best global
upper-gap cut `V` satisfies `K ≤ V ≤ Q ≤ (8/5) K`, and it is not exact in
general. Here `K` is the original capped selection functional
`EntropyTail.selection` and `Q` the closed quantile functional
`EntropyTailQuantile.closedQuantileValue`.

A cut at threshold `t` selects the gaps above `t` as the entropy core `σ` of
`EntropyTail.selectionObjective` and leaves the smaller gaps in the
remainder `μ - σ`. For a general law both the open cut `μ|{t < d}` and the
closed cut `μ|{t ≤ d}` are allowed. For a law on `n` atoms in increasing gap
order these are exactly the `n+1` selections of the top `k` atoms scanned by
the toolkit's `threshold_certificate`. The counterexample is the law with
masses `9999/10000` at `1/4` and `1/10000` at `1/2`, with `ρ = 1/4` and
`B = 10^8` (`evidence/not_one_global_threshold.json`). -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.GlobalCut
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- The global-cut value `V`: the objective minimized over the open and closed
upper cuts `μ|{t < d}` and `μ|{t ≤ d}`, `t ∈ ℝ`, capped at `ρ` like `selection`. -/
def globalCutValue (μ : Measure Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  min (ENNReal.ofReal ρ) (⨅ t : ℝ,
    min (selectionObjective μ ρ B (μ.restrict {d : Gap | t < (d : ℝ)}))
      (selectionObjective μ ρ B (μ.restrict {d : Gap | t ≤ (d : ℝ)})))

/-- Corollary 6: `K ≤ V ≤ Q ≤ (8/5) K` for every probability law on the gaps. -/
def GlobalCutStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    selection μ ρ B ≤ globalCutValue μ ρ B ∧
    globalCutValue μ ρ B ≤ EntropyTailQuantile.closedQuantileValue μ ρ B ∧
    EntropyTailQuantile.closedQuantileValue μ ρ B ≤ ENNReal.ofReal (8/5) * selection μ ρ B

/-- On `n` atoms in strictly increasing gap order, `V` is the capped minimum over
the `n+1` selections of the `k` largest atoms, `k = 0, …, n`. -/
def FiniteCutStatement : Prop :=
  ∀ {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℝ≥0∞), StrictMono d → ∀ ρ B : ℝ,
    globalCutValue (∑ i, w i • Measure.dirac (d i)) ρ B =
      min (ENNReal.ofReal ρ) (⨅ k : Fin (n+1),
        selectionObjective (∑ i, w i • Measure.dirac (d i)) ρ B
          (∑ i : Fin n, (if n ≤ i.val + k.val then w i else 0) • Measure.dirac (d i)))

/-- The global cut is not exact: on the two-atom law of the note, `K < V`. -/
def NotExactStatement : Prop :=
  ∃ a b : Gap, (a : ℝ) = 1/4 ∧ (b : ℝ) = 1/2 ∧
    let μ := ENNReal.ofReal (9999/10000) • Measure.dirac a +
      ENNReal.ofReal (1/10000) • Measure.dirac b
    IsProbabilityMeasure μ ∧ selection μ (1/4) (10^8) < globalCutValue μ (1/4) (10^8)

end ThresholdHC.GlobalCut
