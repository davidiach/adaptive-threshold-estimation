import ThresholdHC.BandCostExample.Optimal
import ThresholdHC.BandCostExample.Frontier
import ThresholdHC.GapLawMenus.Atoms

/-! The formal solver run on the actual support menus of the 64-band law. Each
occupied band holds one atom, so its menu is `{∅, {atom}}`, with costs `0` and
`c`: all nonempty suffixes cost the same. The frontier after `L` menus therefore
has `L + 1` states, the 64 menus take `64 · 65 = 4160` transitions, and 65
terminal states remain. The trace the solver retains for the optimum selects
exactly the two largest gaps, by the strict uniqueness of the hard minimum. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Classical
namespace ThresholdHC.BandCostExample
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix
open ThresholdHC.BandCostSelection ThresholdHC.GapLawMenus

theorem bandIndex_atoms (i : Fin 64) : bandIndex (atoms i) = i.val :=
  bandIndex_eq_of_mem (atoms_mem_band i)

theorem mem_atomSet {d : Gap} : d ∈ atomSet ↔ ∃ i, atoms i = d := by
  simp [atomSet]

theorem atoms_band_iff (i : Fin 64) (j : ℕ) : atoms i ∈ band j ↔ i.val = j := by
  constructor
  · intro h
    rw [← bandIndex_atoms]
    exact bandIndex_eq_of_mem h
  · rintro rfl
    exact atoms_mem_band i

theorem atomSet_card : atomSet.card = 64 := by
  rw [atomSet, Finset.card_image_of_injective _ atoms_injective, Finset.card_univ,
    Fintype.card_fin]

/-- Each atom is alone in its band. -/
theorem slice_atomSet (i : Fin 64) : slice atomSet i.val = {atoms i} := by
  ext d
  simp only [slice, Finset.mem_filter, mem_atomSet, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨k, rfl⟩, hk⟩
    rw [atoms_band_iff] at hk
    rw [Fin.ext hk]
  · rintro rfl
    exact ⟨⟨i, rfl⟩, atoms_mem_band i⟩

/-- A one-atom band has the two suffixes `∅` and `{a}`. -/
theorem suffixChoices_singleton (a : Gap) : suffixChoices {a} = {∅, {a}} := by
  ext S
  rw [mem_suffixChoices, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hS, -⟩
    exact Finset.subset_singleton_iff.mp hS
  · intro h
    refine ⟨Finset.subset_singleton_iff.mpr h, ?_⟩
    intro j x y hx hy _ _ hxy
    have hxa : x = a := by
      rcases h with rfl | rfl
      · simp at hx
      · simpa using hx
    have hya : y = a := by simpa using hy
    rw [hxa, hya] at hxy
    exact absurd hxy (lt_irrefl _)

/-- With one atom per band every subset is a bandwise suffix. -/
theorem suffixChoices_atomSet : suffixChoices atomSet = atomSet.powerset := by
  ext S
  rw [mem_suffixChoices, Finset.mem_powerset]
  constructor
  · exact fun h => h.1
  · intro hS
    refine ⟨hS, ?_⟩
    intro j x y hx hy hxj hyj hxy
    obtain ⟨i, rfl⟩ := mem_atomSet.mp (hS (Finset.mem_coe.mp hx))
    obtain ⟨k, rfl⟩ := mem_atomSet.mp (Finset.mem_coe.mp hy)
    rw [atoms_band_iff] at hxj hyj
    have hik : i = k := Fin.ext (hxj.trans hyj.symm)
    subst hik
    exact absurd hxy (lt_irrefl _)

theorem suffixChoices_card : (suffixChoices atomSet).card = 2^64 := by
  rw [suffixChoices_atomSet, Finset.card_powerset, atomSet_card]

theorem occupiedBands_card : (atomSet.image bandIndex).card = 64 := by
  rw [atomSet, Finset.image_image, Finset.card_image_of_injective, Finset.card_univ,
    Fintype.card_fin]
  intro i j h
  have h' : bandIndex (atoms i) = bandIndex (atoms j) := h
  rw [bandIndex_atoms, bandIndex_atoms] at h'
  exact Fin.ext h'

theorem menus_length : (menus atomSet (occupiedBands atomSet)).length = 64 := by
  unfold menus occupiedBands
  rw [List.length_map, Finset.length_toList, occupiedBands_card]

theorem mem_menus {M : Finset (Finset Gap)} (hM : M ∈ menus atomSet (occupiedBands atomSet)) :
    ∃ i : Fin 64, M = {∅, {atoms i}} := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hM
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hj)
  obtain ⟨i, rfl⟩ := mem_atomSet.mp hd
  exact ⟨i, by rw [bandIndex_atoms, slice_atomSet, suffixChoices_singleton]⟩

theorem menus_card : ∀ M ∈ menus atomSet (occupiedBands atomSet), M.card = 2 := by
  intro M hM
  obtain ⟨i, rfl⟩ := mem_menus hM
  exact Finset.card_pair (Finset.singleton_ne_empty _).symm

theorem cost_empty : GapLawMenus.cost law ∅ = 0 := by
  have := law_probability
  rw [cost_atomic]
  simp

/-- The one-atom suffix `{atoms i}` costs `c`. -/
theorem cost_atom (i : Fin 64) : GapLawMenus.cost law {atoms i} = cc := by
  have := law_probability
  rw [cost_atomic, Finset.sum_singleton]
  have hm : (law {atoms i}).toReal = (weights i : ℝ) := by
    change law.real {atoms i} = _
    rw [law_eq, ThresholdHC.FiniteLawCertificates.atomicMeasure_real _ _ weights_nonneg, ← atoms_eq, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [ite_eq_right]
      intro h
      exact hji (atoms_injective (Set.mem_singleton_iff.mp h))
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hm, weights_div]
  have := (atoms i).property.1.ne'
  field_simp

theorem menus_tags : ∀ M ∈ menus atomSet (occupiedBands atomSet), ∀ y : ℝ,
    (∃ x ∈ M, GapLawMenus.cost law x = y) ↔ (y = 0 ∨ y = cc) := by
  intro M hM y
  obtain ⟨i, rfl⟩ := mem_menus hM
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h, cost_empty]
      exact Or.inl rfl
    · rw [Finset.mem_singleton.mp h, cost_atom]
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨∅, Finset.mem_insert_self _ _, cost_empty⟩
    · exact ⟨{atoms i}, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), cost_atom i⟩

theorem solve_card :
    (solve (GapLawMenus.cost law) (GapLawMenus.saving law (1 / Real.sqrt 4294967296))
      (menus atomSet (occupiedBands atomSet))).card = 65 := by
  rw [two_tag_solve_card _ _ cc_pos.ne _ menus_tags, menus_length]

theorem transitions :
    transitionCount (GapLawMenus.cost law) (GapLawMenus.saving law (1 / Real.sqrt 4294967296))
      (menus atomSet (occupiedBands atomSet)) = 4160 := by
  rw [two_tag_transitions _ _ cc_pos.ne _ menus_tags menus_card, menus_length]

theorem support_finite : law.support.Finite := by
  rw [law_support]
  exact Set.finite_range _

theorem toFinset_eq (hF : law.support.Finite) : hF.toFinset = atomSet := by
  ext d
  rw [Set.Finite.mem_toFinset, law_support, mem_atomSet, Set.mem_range]

/-- The solver retains a trace of value `K`, and that trace selects `{1/2, 1/4}`. -/
theorem solver_trace :
    ∃ xs ∈ solve (GapLawMenus.cost law) (GapLawMenus.saving law (1 / Real.sqrt 4294967296))
        (menus atomSet (occupiedBands atomSet)),
      (traceSet xs : Set Gap) = {d : Gap | (d : ℝ) = 1/2 ∨ (d : ℝ) = 1/4} ∧
      selection law (1/4) 4294967296 =
        ENNReal.ofReal (menuObjective law (1/4) 4294967296 xs) := by
  have := law_probability
  have hF := support_finite
  obtain ⟨xs, hxs, hsuf, hsel⟩ := finite_law_solver law hF (ρ := 1/4) (B := 4294967296)
    (by norm_num) le_rfl (by norm_num)
  rw [toFinset_eq hF] at hxs hsuf
  refine ⟨xs, hxs, ?_, hsel⟩
  have hx := solve_subset _ _ _ hxs
  have hobj := menuObjective_eq law atomSet (occupiedBands atomSet) (Finset.nodup_toList _) hx
    (by norm_num : (0:ℝ) ≤ 1/4) 4294967296
  obtain ⟨m, hm, hmi⟩ := restrict_eq (traceSet xs : Set Gap)
  rw [hm] at hobj
  have hmt : m = topTwo := by
    by_contra hne
    have h3 : selectionObjective law (1/4) 4294967296 (retained topTwo) <
        min (ENNReal.ofReal (1/4)) (selectionObjective law (1/4) 4294967296 (retained m)) :=
      lt_min objective_topTwo_lt_cap (objective_topTwo_lt m hne)
    rw [← hobj, ← hsel, selection_eq_topTwo] at h3
    exact lt_irrefl _ h3
  subst hmt
  ext d
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hd
    obtain ⟨i, rfl⟩ := mem_atomSet.mp ((mem_suffixChoices.mp hsuf).1 (Finset.mem_coe.mp hd))
    have h := (hmi i).mpr hd
    rw [atoms_top_iff]
    simpa [topTwo] using h
  · rintro (h | h)
    · have he : atoms 0 = d := Subtype.ext (by rw [atoms_val, h]; norm_num)
      rw [← he]
      exact (hmi 0).mp (by decide)
    · have he : atoms 1 = d := Subtype.ext (by rw [atoms_val, h]; norm_num)
      rw [← he]
      exact (hmi 1).mp (by decide)

end ThresholdHC.BandCostExample
