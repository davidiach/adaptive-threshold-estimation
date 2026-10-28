import ThresholdHC.OracleLower.Specification

noncomputable section
open MeasureTheory
namespace ThresholdHC.OracleLower

theorem selected_gap_at_history {R : Type} [MeasurableSpace R]
    (A : SelectedEstimator R) (r : R) (xs : List Bool) :
    (selectedOracle A).gap r (Encodable.encode xs) = A.newGap r xs := by
  simp [selectedOracle]

theorem selected_label_prefix {R : Type} [MeasurableSpace R]
    (A : SelectedEstimator R) (r : R) (xs : List Bool) (i : ℕ)
    (h : (selectedOracle A).policy r xs = some i) :
    ∃ ys : List Bool, i = Encodable.encode ys ∧ ys.length ≤ xs.length := by
  change selectedLabel xs (A.request r xs) = some i at h
  cases ha : A.request r xs with
  | none => simp [ha,selectedLabel] at h
  | some a =>
    cases a with
    | none =>
      simp only [ha,selectedLabel,Option.some.injEq] at h
      exact ⟨xs,h.symm,le_rfl⟩
    | some j =>
      simp only [ha,selectedLabel,Option.some.injEq] at h
      exact ⟨xs.take j,h.symm,List.length_take_le' _ _⟩

/-- Every fresh request uses a label absent at all earlier observations.
Revisits address exactly the earlier creation and retain its magnitude. -/
theorem selected_semantics : SelectedSemanticsStatement := by
  intro R _ A
  constructor
  · intro r xs hcreate
    refine ⟨by simp [selectedOracle,selectedLabel,hcreate],selected_gap_at_history A r xs,?_⟩
    intro k hk he
    obtain ⟨ys,hy,hlen⟩ := selected_label_prefix A r (xs.take k) _ he
    have hys : xs = ys := Encodable.encode_injective hy
    have htake : (xs.take k).length ≤ k := List.length_take_le _ _
    rw [← hys] at hlen
    omega
  · intro r xs j hj
    obtain ⟨hbefore,hcreate⟩ := A.reuse_valid r xs j hj
    refine ⟨hbefore,hcreate,?_,selected_gap_at_history A r (xs.take j)⟩
    simp [selectedOracle,selectedLabel,hj,hcreate]

end ThresholdHC.OracleLower
