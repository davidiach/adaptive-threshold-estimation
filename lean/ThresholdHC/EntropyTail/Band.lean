import ThresholdHC.EntropyTail.Model

/-! The canonical bands are measurable, pairwise disjoint and cover `(0,1/2]`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6

theorem measurableSet_band (j : ℕ) : MeasurableSet (band j) := by
  have h1 : MeasurableSet {d : Gap | (1/2 : ℝ)^(j+2) < (d : ℝ)} :=
    measurableSet_lt measurable_const measurable_subtype_coe
  have h2 : MeasurableSet {d : Gap | (d : ℝ) ≤ (1/2 : ℝ)^(j+1)} :=
    measurableSet_le measurable_subtype_coe measurable_const
  exact h1.inter h2

theorem band_disjoint {i j : ℕ} (hij : i ≠ j) : Disjoint (band i) (band j) := by
  rw [Set.disjoint_left]
  intro d hi hj
  simp only [band, Set.mem_ofPred_eq] at hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have : (1/2 : ℝ)^(j+1) ≤ (1/2 : ℝ)^(i+2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith [hi.1, hj.2]
  · have : (1/2 : ℝ)^(i+1) ≤ (1/2 : ℝ)^(j+2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith [hi.2, hj.1]

theorem exists_band (d : Gap) : ∃ j, d ∈ band j := by
  classical
  have hd := d.2
  have hex : ∃ n : ℕ, (1/2 : ℝ)^(n+2) < (d : ℝ) := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hd.1 (by norm_num : (1/2 : ℝ) < 1)
    exact ⟨n, lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hn⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | k
  · norm_num
    exact hd.2
  · have hk := Nat.find_min hex (show k < Nat.find hex by omega)
    push Not at hk
    exact hk

end ThresholdHC.EntropyTail
