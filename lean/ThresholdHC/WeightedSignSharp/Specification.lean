import ThresholdHC.CriticalAllSizes.SingleGap
import ThresholdHC.EntropyTailQuantile.CostEntropy

/-! Weighted sign entropy with the paper's coefficient 214.

Source: `paper/v6/appendix-lower-foundations.tex`, Lemma `lem:weighted-sign`
(display `eq:sc-weighted-sign`). The three targets are the per-gap floor
`c_j > 3/40` stated in its proof, the pathwise weighted overlap
`∑_j 1_{E_j}/(1+c_j) ≤ 25/3` of the stopping windows `E_j`, and the lemma
itself, `1 + Ent(π) ≤ 214 ∑_j π_j c_j`, in homogeneous form for arbitrary
nonnegative weights. Here `c_j = d_j² E_{-d_j} τ` is the actual negative-sign
work of one observable test with a common seed law. The windows are the
existing library windows with lower time `⌊(1/1024)/d²⌋` and upper time
`⌈4 E τ⌉ + 1`. Only finite negative-sign work is assumed, and nothing is
assumed under the fair coin. The same binders as
`ThresholdHC.EntropyTailLower.WeightedSignEntropyStatement` are used; that
locked target carries the weaker coefficient 4096. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.WeightedSignSharp
open ThresholdHC.CriticalEntropy

/-- Stopped change-of-measure floor `c = d² E₋τ > 3/40` (proof of
`lem:weighted-sign`). -/
def SignWorkFloorStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
    (A : SignTest R) (d : EntropyGap),
    expectedSignTestWork ν (signParameter d false) A ≠ ∞ →
    (ν.prod (Tier2.tapeMeasure (signParameter d false))).real {z | A.output z = true} ≤ 1/10 →
    (ν.prod (Tier2.tapeMeasure (signParameter d true))).real {z | A.output z = false} ≤ 1/10 →
    (3/40 : ℝ) < (d : ℝ)^2 * (expectedSignTestWork ν (signParameter d false) A).toReal

/-- Pathwise weighted overlap `∑ⱼ 1_{Eⱼ}/(1+cⱼ) ≤ 25/3` of the stopping
windows (proof of `lem:weighted-sign`), on every path. -/
def WindowOverlapStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (ν : Measure R) (A : SignTest R) (K : ℕ)
    (d : Fin K → EntropyGap),
    (∀ i j, j.val = i.val + 1 → 2 * (d j : ℝ) ≤ (d i : ℝ)) →
    ∀ z : R × (ℕ → Bool),
      (∑ i, (signTestWindow A (entropyLowerTime (d i))
        (entropyUpperTime (expectedSignTestWork ν (signParameter (d i) false) A).toReal)).indicator
          (fun _ => 1 / (1 + (d i : ℝ)^2 *
            (expectedSignTestWork ν (signParameter (d i) false) A).toReal)) z) ≤ 25/3

/-- Weighted sign entropy with the paper's coefficient 214 (`eq:sc-weighted-sign`),
with the same binders as `EntropyTailLower.WeightedSignEntropyStatement`. -/
def WeightedSignEntropy214Statement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
    (A : SignTest R) (K : ℕ) (d : Fin K → EntropyGap),
    (∀ i j, j.val = i.val + 1 → 2 * (d j : ℝ) ≤ (d i : ℝ)) →
    (∀ i, expectedSignTestWork ν (signParameter (d i) false) A ≠ ∞) →
    (∀ i b, (ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).real
      {z | A.output z ≠ b} ≤ 1 / 10) →
    ∀ a : Fin K → ℝ, (∀ i, 0 ≤ a i) →
      ThresholdHC.EntropyTailQuantile.costEntropy a ≤
        214 * ∑ i, a i * ((d i : ℝ)^2 *
          (expectedSignTestWork ν (signParameter (d i) false) A).toReal)

end ThresholdHC.WeightedSignSharp
