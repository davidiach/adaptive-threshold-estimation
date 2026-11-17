import ThresholdHC.EnvelopeTransferCertificates.Envelope
import ThresholdHC.SelectionStability.Approximation

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical
namespace ThresholdHC.EnvelopeTransferCertificates
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates

/-- A finite transport, extended by the identity away from the supplied atoms. -/
def pointMap : List (Gap × Gap) → Gap → Gap
  | [] => id
  | (d,e)::rest => fun x => if x=d then e else pointMap rest x

theorem pointMap_measurable (pairs : List (Gap × Gap)) : Measurable (pointMap pairs) := by
  induction pairs with
  | nil => exact measurable_id
  | cons p rest ih => exact Measurable.ite (measurableSet_singleton p.1) measurable_const ih

theorem pointMap_bounds (pairs : List (Gap × Gap)) {r : ℝ} (hr : 1 ≤ r)
    (hp : ∀ p ∈ pairs, (p.1:ℝ) ≤ (p.2:ℝ) ∧ (p.2:ℝ) ≤ r*(p.1:ℝ)) :
    ∀ x : Gap, (x:ℝ) ≤ (pointMap pairs x:ℝ) ∧ (pointMap pairs x:ℝ) ≤ r*(x:ℝ) := by
  induction pairs with
  | nil =>
    intro x
    change (x:ℝ) ≤ (x:ℝ) ∧ (x:ℝ) ≤ r*(x:ℝ)
    exact ⟨le_rfl, by nlinarith [x.property.1]⟩
  | cons p rest ih =>
    intro x
    by_cases hx : x=p.1
    · simpa [pointMap, hx] using hp p (by simp)
    · simpa [pointMap, hx] using ih (fun q hq => hp q (by simp [hq])) x

theorem common_band {d e : Gap} {j : ℕ} (hd : d ∈ ThresholdHC.EntropyTail.band j)
    (he : e ∈ ThresholdHC.EntropyTail.band j) (k : ℕ) :
    d ∈ ThresholdHC.EntropyTail.band k ↔ e ∈ ThresholdHC.EntropyTail.band k := by
  by_cases h : k=j
  · simpa [h] using iff_of_true hd he
  · have hnotd := fun hx => Set.disjoint_left.mp (ThresholdHC.EntropyTail.band_disjoint h) hx hd
    have hnote := fun hx => Set.disjoint_left.mp (ThresholdHC.EntropyTail.band_disjoint h) hx he
    exact iff_of_false hnotd hnote

theorem pointMap_bands (pairs : List (Gap × Gap))
    (hp : ∀ p ∈ pairs, ∃ j, p.1 ∈ ThresholdHC.EntropyTail.band j ∧ p.2 ∈ ThresholdHC.EntropyTail.band j) :
    ∀ j, pointMap pairs ⁻¹' ThresholdHC.EntropyTail.band j = ThresholdHC.EntropyTail.band j := by
  intro j
  ext x
  induction pairs with
  | nil => rfl
  | cons p rest ih =>
    by_cases hx : x=p.1
    · obtain ⟨k,hd,he⟩ := hp p (by simp)
      simpa [pointMap, hx] using (common_band hd he j).symm
    · simpa [pointMap, hx] using ih (fun q hq => hp q (by simp [hq]))

theorem map_atomic_gap {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (f : Gap → Gap) (hf : Measurable f) :
    (atomicMeasure d w).map f = atomicMeasure (fun i => f (d i)) w :=
  map_atomic d w f hf

/-- Duplicate destinations carry the sum of the source weights, with no injectivity premise. -/
theorem atomic_group {n m : ℕ} (e : Fin m → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (route : Fin n → Fin m) :
    atomicMeasure (fun i => e (route i)) w =
      atomicMeasure e (fun j => ∑ i, if route i=j then w i else 0) := by
  unfold atomicMeasure
  have hn (j : Fin m) (i : Fin n) : 0 ≤ (if route i=j then (w i:ℝ) else 0) := by
    split_ifs
    · exact_mod_cast hw i
    · exact le_rfl
  simp only [Rat.cast_sum, apply_ite, Rat.cast_zero,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hn _ i), Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_smul]

end ThresholdHC.EnvelopeTransferCertificates
