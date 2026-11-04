import ThresholdHC.BandwiseSuffix.Attainment
import ThresholdHC.BandwiseSuffix.Exchange

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.BandwiseSuffix
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- Strict packet gain rules out every inversion in an uncapped hard optimizer on the support. -/
theorem optimal_is_suffix (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite)
    {ρ B : ℝ} (hB : 0 < B) (S : Finset Gap) (hS : (S : Set Gap) ⊆ μ.support)
    (hmin : ∀ σ : Measure Gap, σ ≤ μ →
      selectionObjective μ ρ B (μ.restrict S) ≤ selectionObjective μ ρ B σ) :
    IsBandSuffix μ.support S := by
  have hzero := hmin 0 bot_le
  rw [selectionObjective_zero] at hzero
  have hfinite := ne_top_of_le_ne_top (measure_ne_top μ univ) (hzero.trans (tailCost_le_mass _ _))
  intro j x y hx hy hxj hyj hxy
  by_contra hmiss
  obtain ⟨τ,hτ,hgain⟩ := improve_inversion μ S hB hxy hx hmiss hxj hyj
    (support_atom_pos hF (hS hx)) (support_atom_pos hF hy) hfinite
  exact (not_lt_of_ge (hmin τ hτ)) hgain

/-- Theorem 5. The same hard selection minimizes the raw objective and realizes the capped value. -/
theorem bandwise_suffix : BandwiseSuffixStatement := by
  intro μ _ hF ρ B hρ hr hB
  obtain ⟨S,hS,hmin⟩ := exists_optimal_hard μ hF hρ hr hB
  refine ⟨S, hS, optimal_is_suffix μ hF (ρ := ρ) hB S hS hmin, hmin, ?_⟩
  apply le_antisymm
  · exact le_min (selection_le_rho μ ρ B) (selection_le_objective Measure.restrict_le_self ρ B)
  · exact min_le_min le_rfl (le_iInf₂ hmin)

end ThresholdHC.BandwiseSuffix
