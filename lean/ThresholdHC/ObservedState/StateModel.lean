import ThresholdHC.ObservedState.Construction

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ObservedState
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation

/-- A selected-state algorithm. Its seed may include all free outer samples.
At each active step it chooses any observed state in the unit interval. -/
structure StateEstimator (R : Type) [MeasurableSpace R] where
  randomLaw : Measure R
  probability : IsProbabilityMeasure randomLaw
  continues : R → List Bool → Bool
  continues_measurable : ∀ xs, Measurable (fun r => continues r xs)
  query : R → List Bool → unitInterval
  query_measurable : ∀ xs, Measurable (fun r => query r xs)
  output : R × ProcessTape → ℝ
  output_measurable : Measurable output

instance stateEstimator_probability {R : Type} [MeasurableSpace R] (A : StateEstimator R) :
    IsProbabilityMeasure A.randomLaw := A.probability

local instance (N : ℕ) : MeasurableSpace (Option (Fin N)) := ⊤

def onCells {N : ℕ} {R : Type} [MeasurableSpace R] (A : StateEstimator R)
    (cell : unitInterval → Fin N) (hc : Measurable cell) : Estimator N R where
  randomLaw := A.randomLaw
  probability := A.probability
  policy := fun r xs => if A.continues r xs then some (cell (A.query r xs)) else none
  policy_measurable := by
    intro xs a
    have hm : Measurable (fun r => if A.continues r xs then some (cell (A.query r xs)) else none) :=
      Measurable.ite (measurableSet_eq_fun (A.continues_measurable xs) measurable_const)
        ((measurable_of_countable (fun i : Fin N => some i)).comp (hc.comp (A.query_measurable xs)))
        measurable_const
    exact measurableSet_eq_fun hm measurable_const
  output := A.output
  output_measurable := A.output_measurable

/-- Constant magnitude within each cell gives a concrete independent-tape
experiment for every selected-state algorithm and deterministic sign array. -/
def stateLaw {N : ℕ} {R : Type} [MeasurableSpace R] (A : StateEstimator R)
    (cap : Fin N → Gap) (cell : unitInterval → Fin N) (hc : Measurable cell)
    (s : Fin N → Bool) : Measure (R × ProcessTape) :=
  modelLaw (onCells A cell hc) cap s

def stateTarget {N : ℕ} (cell : unitInterval → Fin N) (s : Fin N → Bool) : ℝ :=
  volume.real {u | s (cell u) = true}

theorem stateTarget_eq {N : ℕ} (cell : unitInterval → Fin N) (hc : Measurable cell) (s : Fin N → Bool) :
    stateTarget cell s = target (cellWeight cell) s := by
  have hs : MeasurableSet {u : unitInterval | s (cell u) = true} :=
    measurableSet_eq_fun ((measurable_of_countable s).comp hc) measurable_const
  have h := cell_moment cell hc (fun i => if s i then (1 : ℝ) else 0)
  have he : (∫ u : unitInterval, if s (cell u) then (1 : ℝ) else 0) = stateTarget cell s := by
    simpa [Set.indicator,stateTarget] using (integral_indicator_const (μ := volume) (1 : ℝ) hs)
  rw [he] at h
  exact h

def conditionalMean {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N)
    (s : Fin N → Bool) (u : unitInterval) : ℝ :=
  2 * (gapParameter (s (cell u)) (cap (cell u)) : ℝ) - 1

theorem conditional_mean_positive {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N)
    (s : Fin N → Bool) (u : unitInterval) :
    0 < conditionalMean cap cell s u ↔ s (cell u) = true := by
  have hp := (cap (cell u)).property.1
  cases h : s (cell u) <;> simp [conditionalMean,gapParameter,h] <;> linarith

theorem threshold_target {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N)
    (s : Fin N → Bool) :
    volume.real {u | 0 < conditionalMean cap cell s u} = stateTarget cell s := by
  simp only [conditional_mean_positive,stateTarget]

/-- Every point query consumes exactly one observation of its selected cell. -/
theorem onCells_policy {N : ℕ} {R : Type} [MeasurableSpace R] (A : StateEstimator R)
    (cell : unitInterval → Fin N) (hc : Measurable cell) (r : R) (xs : List Bool) :
    (onCells A cell hc).policy r xs =
      if A.continues r xs then some (cell (A.query r xs)) else none := rfl

theorem design_confidence_lower (μ : Measure Gap) [IsProbabilityMeasure μ]
    (h : Gap) {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1 / 8) (D : CellDesign μ h δ)
    {R : Type} [MeasurableSpace R] (A : StateEstimator R) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ s, (∫⁻ z, totalProcessWork z.2 ∂stateLaw A D.cap D.cell D.cell_measurable s) ≤ ENNReal.ofReal B)
    (hc : ∀ s, stateLaw A D.cap D.cell D.cell_measurable s
      {z | cellDelta D.cap D.cell h / 4 < |A.output z - stateTarget D.cell s|} ≤ ENNReal.ofReal δ) :
    (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B := by
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
  apply finite_confidence_lower (onCells A D.cell D.cell_measurable) D.cap (cellWeight D.cell)
    (fun i => hardEta h (D.cap i)) qp qm (fun _ => rfl) (fun _ => rfl)
    hB h.property.1 (design_delta_pos μ h δ D) hδ hd
    (fun i => hardEta_bounds h.property.1.le (D.cap i)) (fun i => gap_mul_hardEta_le (D.cap i))
    hsep D.concentration hw
  intro s
  simpa only [stateTarget_eq D.cell D.cell_measurable s,stateLaw,onCells] using hc s

end ThresholdHC.ObservedState
