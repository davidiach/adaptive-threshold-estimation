import ThresholdHC.ContinuousObserved.Reduction

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState

def CellDesign.queryDesign (μ : Measure Gap) (h : Gap) (δ : ℝ) (D : CellDesign μ h δ) :
    QueryDesign D.count where
  cap := D.cap
  gap := D.gap
  cell := D.cell
  gap_measurable := D.gap_measurable
  cell_measurable := D.cell_measurable
  bound := D.cap_bound

/-- The exact finite-cell bound transfers to the simulated variable-gap law.
The observation-law identification is supplied separately. -/
theorem simulated_confidence_lower (μ : Measure Gap) [IsProbabilityMeasure μ]
    (h : Gap) {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1 / 8) (D : CellDesign μ h δ)
    {R : Type} [MeasurableSpace R] (A : StateEstimator R) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ s, (∫⁻ z, totalProcessWork z.2 ∂queryLaw (CellDesign.queryDesign μ h δ D) A s) ≤ ENNReal.ofReal B)
    (hc : ∀ s, queryLaw (CellDesign.queryDesign μ h δ D) A s
      {z | cellDelta D.cap D.cell h / 4 < |A.output z - stateTarget D.cell s|} ≤ ENNReal.ofReal δ) :
    (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B := by
  let Q := CellDesign.queryDesign μ h δ D
  let E := reduction Q A
  let hv := hard_pair_validity (h : ℝ) h.property.1
  let qp (i : Fin D.count) : unitInterval := ⟨hardPlus h (D.cap i),(hv.2.2.2 (D.cap i)).2.2.1⟩
  let qm (i : Fin D.count) : unitInterval := ⟨hardMinus h (D.cap i),(hv.2.2.2 (D.cap i)).2.2.2⟩
  have hsep : (∑ i, cellWeight D.cell i * (qp i : ℝ)) -
      (∑ i, cellWeight D.cell i * (qm i : ℝ)) = cellDelta D.cap D.cell h := by
    rw [← Finset.sum_sub_distrib]
    unfold cellDelta
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [qp,qm,hardPlus,hardMinus,hardEta]
    ring
  apply finite_confidence_lower E D.cap (cellWeight D.cell)
    (fun i => hardEta h (D.cap i)) qp qm (fun _ => rfl) (fun _ => rfl)
    hB h.property.1 (design_delta_pos μ h δ D) hδ hd
    (fun i => hardEta_bounds h.property.1.le (D.cap i)) (fun i => gap_mul_hardEta_le (D.cap i))
    hsep D.concentration
  · intro s
    simpa only [reduction_work,E,Q,CellDesign.queryDesign] using hw s
  · intro s
    have he := reduction_error Q A s (cellDelta D.cap D.cell h / 4) (stateTarget D.cell s)
    have ht := hc s
    rw [he,stateTarget_eq D.cell D.cell_measurable s] at ht
    exact ht

end ThresholdHC.ContinuousObserved
