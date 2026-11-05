import ThresholdHC.ObservedState.Mean

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ObservedState
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6

/-- The finite-cell observed-state proposition, including its measurable
uniform-state realization, envelope, separation and all selected-state policies. -/
theorem finite_observed_state_lower (μ : Measure Gap) [IsProbabilityMeasure μ]
    (h : Gap) {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1 / 8) :
    ∃ D : CellDesign μ h δ,
      0 < cellDelta D.cap D.cell h ∧
      modulus μ h / 8 ≤ cellDelta D.cap D.cell h ∧
      (∀ x : ℝ, volume {u : unitInterval | (D.cap (D.cell u) : ℝ) ≤ x} ≤
        μ {d : Gap | (d : ℝ) ≤ x}) ∧
      (∀ (R : Type) [MeasurableSpace R] (A : StateEstimator R) (B : ℝ), 0 ≤ B →
        (∀ s, (∫⁻ z, totalProcessWork z.2 ∂stateLaw A D.cap D.cell D.cell_measurable s) ≤ ENNReal.ofReal B) →
        (∀ s, stateLaw A D.cap D.cell D.cell_measurable s
          {z | cellDelta D.cap D.cell h / 4 < |A.output z - stateTarget D.cell s|} ≤ ENNReal.ofReal δ) →
        (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B) := by
  obtain ⟨D⟩ := cell_design_exists μ h hδ
  refine ⟨D,design_delta_pos μ h δ D,design_separation μ h δ D,design_cdf μ h δ D,?_⟩
  intro R _ A B hB hw hc
  exact design_confidence_lower μ h hδ hd D A hB hw hc

end ThresholdHC.ObservedState
