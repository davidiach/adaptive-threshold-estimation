import ThresholdHC.EntropyTailQuantile.CutDecomposition
import ThresholdHC.EntropyTailQuantile.EntropyMoment
import ThresholdHC.EntropyTailQuantile.QuantileFeasible

/-! The quantile tail is a lower bound for every selection objective. This is
a deterministic comparison, not the separately assigned statistical lower bound. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6

theorem quantileTail_real_mass (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : (quantileTail μ ρ).real univ = ρ := by
  rw [measureReal_def, quantileTail_mass μ hρ hρ1, ENNReal.toReal_ofReal hρ.le]

theorem quantileTail_le_selectionCost (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ h : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hh : 0 ≤ h)
    (σ : Measure Gap) (hσ : σ ≤ μ) :
    ENNReal.ofReal (tailModulus (quantileTail μ ρ) h) ≤ selectionCost μ σ ρ h := by
  let t := quantileThreshold μ ρ
  let r := quantileBoundaryFraction μ ρ
  have hr := quantileBoundaryFraction_properties μ hρ hρ1
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  have : IsFiniteMeasure (lowerCut t r σ) := isFiniteMeasure_of_le σ (lowerCut_le t hr.1 hr.2.1 σ)
  have : IsFiniteMeasure (lowerCut t r (μ-σ)) :=
    isFiniteMeasure_of_le (μ-σ) (lowerCut_le t hr.1 hr.2.1 (μ-σ))
  have hd : quantileTail μ ρ = lowerCut t r σ + lowerCut t r (μ-σ) := by
    rw [← lowerCut_add, add_comm σ, Measure.sub_add_cancel_of_le hσ]
    rfl
  have hm : (lowerCut t r σ) univ ≤ ENNReal.ofReal ρ := by
    calc
      _ ≤ (quantileTail μ ρ) univ := lowerCut_mono t r hσ univ
      _ = _ := quantileTail_mass μ hρ hρ1
  rw [hd, tailModulus_add _ _ hh,
    ENNReal.ofReal_add (tailModulus_nonneg _ hh) (tailModulus_nonneg _ hh)]
  exact add_le_add (tailModulus_le_sqrt_entropy (lowerCut_le t hr.1 hr.2.1 σ) hm hh)
    (ENNReal.ofReal_le_ofReal (tailModulus_mono (lowerCut_le t hr.1 hr.2.1 (μ-σ)) hh))

theorem budgetScale_nonneg (B : ℝ) : 0 ≤ budgetScale B := inv_nonneg.mpr (sqrt_nonneg B)

theorem budgetScale_pos {B : ℝ} (hB : 0 < B) : 0 < budgetScale B :=
  inv_pos.mpr (sqrt_pos.mpr hB)

theorem quantileTail_le_selectionValue (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    ENNReal.ofReal (tailModulus (quantileTail μ ρ) (budgetScale B)) ≤ selectionValue μ ρ B := by
  have : IsFiniteMeasure (quantileTail μ ρ) := isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  apply le_min
  · apply ENNReal.ofReal_le_ofReal
    exact (tailModulus_le_mass _ (budgetScale_nonneg B)).trans_eq (quantileTail_real_mass μ hρ hρ1)
  · apply le_iInf
    intro σ
    apply le_iInf
    exact quantileTail_le_selectionCost μ hρ hρ1 (budgetScale_nonneg B) σ

theorem quantile_saturation (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (ht : quantileThreshold μ ρ ≤ budgetScale B) :
    selectionValue μ ρ B = ENNReal.ofReal ρ ∧ closedQuantileValue μ ρ B = ENNReal.ofReal ρ := by
  have htail : tailModulus (quantileTail μ ρ) (budgetScale B) = ρ := by
    rw [tailModulus_eq_mass _ ((quantileTail_support μ ρ).mono (fun _ hd => hd.trans ht))]
    exact quantileTail_real_mass μ hρ hρ1
  have hK : selectionValue μ ρ B = ENNReal.ofReal ρ := by
    apply le_antisymm (min_le_left _ _)
    simpa only [htail, selectionValue] using quantileTail_le_selectionValue μ hρ hρ1 B
  refine ⟨hK, le_antisymm (min_le_left _ _) ?_⟩
  rw [← hK]
  exact selectionValue_le_closedQuantileValue μ hρ hρ1 B

end ThresholdHC.EntropyTailQuantile
