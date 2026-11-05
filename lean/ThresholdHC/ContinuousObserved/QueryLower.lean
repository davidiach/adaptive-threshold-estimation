import ThresholdHC.ContinuousObserved.QueryPrefix
import ThresholdHC.ContinuousObserved.LowerReduction

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState

/-- The lower bound holds for every physical experiment with the ordinary
fresh Bernoulli prefix law, including arbitrary selected-state queries. -/
theorem query_confidence_lower (μ : Measure Gap) [IsProbabilityMeasure μ]
    (h : Gap) {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1 / 8) (D : CellDesign μ h δ)
    {R : Type} [MeasurableSpace R] (A : StateEstimator R)
    (P : (Fin D.count → Bool) → Measure (R × ProcessTape))
    [∀ s, IsProbabilityMeasure (P s)]
    (hl : ∀ s, RealizesQueryPrefixes (CellDesign.queryDesign μ h δ D) A s (P s))
    {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ s, (∫⁻ z, totalProcessWork z.2 ∂P s) ≤ ENNReal.ofReal B)
    (hc : ∀ s, P s {z | cellDelta D.cap D.cell h / 4 < |A.output z - stateTarget D.cell s|} ≤ ENNReal.ofReal δ) :
    (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B := by
  let Q := CellDesign.queryDesign μ h δ D
  have he (s : Fin D.count → Bool) : P s = queryLaw Q A s :=
    query_prefix_unique Q A s (P s) (queryLaw Q A s) (hl s) (queryLaw_realizes Q A s)
  apply simulated_confidence_lower μ h hδ hd D A hB
  · intro s
    rw [← he s]
    exact hw s
  · intro s
    rw [← he s]
    exact hc s

/-- The construction keeps the prescribed gap law exactly while allowing
different query magnitudes to share one cell sign. -/
theorem variable_gap_observed_lower (μ : Measure Gap) [IsProbabilityMeasure μ]
    (h : Gap) {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1 / 8) :
    ∃ D : CellDesign μ h δ,
      volume.map D.gap = μ ∧
      0 < cellDelta D.cap D.cell h ∧
      modulus μ h / 8 ≤ cellDelta D.cap D.cell h ∧
      (∀ (R : Type) [MeasurableSpace R] (A : StateEstimator R)
        (P : (Fin D.count → Bool) → Measure (R × ProcessTape))
        [∀ s, IsProbabilityMeasure (P s)],
        (∀ s, RealizesQueryPrefixes (CellDesign.queryDesign μ h δ D) A s (P s)) →
        ∀ (B : ℝ), 0 ≤ B →
        (∀ s, (∫⁻ z, totalProcessWork z.2 ∂P s) ≤ ENNReal.ofReal B) →
        (∀ s, P s {z | cellDelta D.cap D.cell h / 4 < |A.output z - stateTarget D.cell s|} ≤ ENNReal.ofReal δ) →
        (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B) := by
  obtain ⟨D⟩ := cell_design_exists μ h hδ
  refine ⟨D,D.gap_law,design_delta_pos μ h δ D,design_separation μ h δ D,?_⟩
  intro R _ A P _ hl B hB hw hc
  exact query_confidence_lower μ h hδ hd D A P hl hB hw hc

end ThresholdHC.ContinuousObserved
