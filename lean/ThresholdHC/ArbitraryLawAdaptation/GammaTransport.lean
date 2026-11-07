import ThresholdHC.ArbitraryLawAdaptation.CountableTransport
import ThresholdHC.EntropyTail.Bridge

/-! Identify the countable transport entropy with the canonical extended-valued
Gamma functional. This transfers a band-cell decomposition to finite measures;
constructing that decomposition from an increasing-gap coupling is separate. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)

theorem countableEntropy_bandCosts_eq_gamma (σ : Measure Gap) [IsFiniteMeasure σ] :
    countableEntropy (fun j => (ThresholdHC.EntropyTail.bandCost σ j).toReal) =
      ThresholdHC.EntropyTail.gamma σ := by
  have he : countableEntropy (fun j => (ThresholdHC.EntropyTail.bandCost σ j).toReal) =
      ThresholdHC.EntropyTailQuantile.measureCostEntropy σ := by
    simp only [countableEntropy,ThresholdHC.EntropyTailQuantile.measureCostEntropy,
      ThresholdHC.EntropyTail.quantile_bandCost_eq]
  rw [he]
  exact le_antisymm (ThresholdHC.EntropyTail.quantile_measureCostEntropy_le σ)
    (ThresholdHC.EntropyTail.gamma_le_quantile_measureCostEntropy σ)

/-- A countable band-cell decomposition controls the canonical entropy, even
when the old full-law entropy is infinite. No finite inverse moment is assumed. -/
theorem gamma_le_three_of_band_transport (σ τ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] {f b : ℕ × ℕ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hb : ∀ x, 0 ≤ b x)
    (hrow : ∀ i n, (∑ k : Fin n, f (i,k.val)) ≤
      (ThresholdHC.EntropyTail.bandCost τ i).toReal)
    (hcost : ∀ x, b x ≤ bandContraction x.2 * f x)
    (dest : ℕ × ℕ → ℕ)
    (hcol : ∀ j, Summable (fun x => if dest x = j then b x else 0))
    (hband : ∀ j, (ThresholdHC.EntropyTail.bandCost σ j).toReal =
      ∑' x, if dest x = j then b x else 0) :
    ThresholdHC.EntropyTail.gamma σ ≤ 3*ThresholdHC.EntropyTail.gamma τ := by
  rw [← countableEntropy_bandCosts_eq_gamma σ,← countableEntropy_bandCosts_eq_gamma τ]
  simp_rw [hband]
  exact countable_band_transport_three (fun _ => ENNReal.toReal_nonneg)
    hf hb hrow hcost dest hcol

end ThresholdHC.ArbitraryLawAdaptation
