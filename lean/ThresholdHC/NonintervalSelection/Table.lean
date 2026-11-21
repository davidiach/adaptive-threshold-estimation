import ThresholdHC.NonintervalSelection.Certificates

/-! The paper's table from the eight kernel-checked enclosures: every hard mask
is below the cap, every row's interval shrunk by `10⁻⁷` and scaled by `h`
contains the capped checker value `J`, and the mask `{1/2, 1/8}` is the strict
minimum. The inner-cost form of the table follows in `Full.lean`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.NonintervalSelection
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail ThresholdHC.FiniteLawCertificates
open ThresholdHC.GlobalSelectionCertificates ThresholdHC.DeterministicCertificates

/-- Case analysis over the eight hard masks. -/
theorem mask_cases (P : (Fin 3 → Bool) → Prop)
    (h0 : P ![false, false, false]) (h1 : P ![true, false, false])
    (h2 : P ![false, true, false]) (h3 : P ![true, true, false])
    (h4 : P ![false, false, true]) (h5 : P ![true, false, true])
    (h6 : P ![false, true, true]) (h7 : P ![true, true, true]) : ∀ s, P s := by
  intro s
  have he : s = ![s 0, s 1, s 2] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  generalize s 0 = a
  generalize s 1 = b
  generalize s 2 = c
  cases a <;> cases b <;> cases c <;> assumption

/-- The table lists every hard mask. -/
theorem enclosures_complete : ∀ s, ∃ e ∈ enclosures, e.1 = s := by
  intro s
  have hs : s ∈ enclosures.map Prod.fst := by
    revert s
    refine mask_cases _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [enclosures]
  exact List.mem_map.1 hs

/-- Each row's enclosure of `J`, shrunk by `10⁻⁷` in units of `h`. -/
theorem enclosures_bounds : ∀ e ∈ enclosures,
    ((e.2.1 : ℝ) + 1/10^7)/1024 ≤ J e.1 ∧ J e.1 ≤ ((e.2.2 : ℝ) - 1/10^7)/1024 := by
  intro e he
  simp only [enclosures, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := cert0
    dsimp [Contains] at h ⊢
    norm_num at h ⊢
    exact h
  · have h := cert1
    dsimp [Contains] at h ⊢
    norm_num at h ⊢
    exact h
  · have h := cert2
    dsimp [Contains] at h ⊢
    norm_num at h ⊢
    exact h
  · have h := cert3
    dsimp [Contains] at h ⊢
    norm_num at h ⊢
    exact h
  · have h := cert4
    dsimp [Contains] at h ⊢
    norm_num at h ⊢
    exact h
  · have h := cert5
    dsimp [Contains] at h ⊢
    norm_num at h ⊢
    exact h
  · have h := cert6
    dsimp [Contains] at h ⊢
    norm_num at h ⊢
    exact h
  · have h := cert7
    dsimp [Contains] at h ⊢
    norm_num at h ⊢
    exact h

theorem enclosures_upper_le : ∀ e ∈ enclosures, (e.2.2 : ℝ) ≤ 6 := by
  intro e he
  simp only [enclosures, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Every row other than the optimal one lies above the optimal row. -/
theorem enclosures_separated : ∀ e ∈ enclosures, e.1 ≠ optimalMask →
    (322749/100000 : ℝ) < e.2.1 := by
  intro e he hne
  simp only [enclosures, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  exact hne rfl

/-- Every hard mask is below the cap `ρ = 1/4`. -/
theorem J_lt_cap (s : Fin 3 → Bool) : J s < 1/4 := by
  obtain ⟨e, he, rfl⟩ := enclosures_complete s
  have h := (enclosures_bounds e he).2
  have hu := enclosures_upper_le e he
  linarith

theorem J_optimal_le : J optimalMask ≤ (322749/100000 - 1/10^7)/1024 := by
  have h := (enclosures_bounds (optimalMask, 322748/100000, 322749/100000)
    (by simp [enclosures, optimalMask])).2
  norm_num at h ⊢
  exact h

/-- The mask `{1/2, 1/8}` is the strict minimum of `J` over the hard masks. -/
theorem J_optimal_lt (s : Fin 3 → Bool) (hs : s ≠ optimalMask) : J optimalMask < J s := by
  obtain ⟨e, he, rfl⟩ := enclosures_complete s
  have h := (enclosures_bounds e he).1
  have hl := enclosures_separated e he hs
  have ho := J_optimal_le
  linarith

theorem J_optimal_min (s : Fin 3 → Bool) : J optimalMask ≤ J s := by
  by_cases hs : s = optimalMask
  · rw [hs]
  · exact (J_optimal_lt s hs).le

/-- The original functional equals the inner cost of the optimal hard mask. -/
theorem selection_eq_optimal :
    selection law (1/4) 1048576 = selectionObjective law (1/4) 1048576 (retained optimalMask) := by
  have hle : selection law (1/4) 1048576 ≤
      selectionObjective law (1/4) 1048576 (retained optimalMask) :=
    selection_le_objective (retained_le optimalMask) _ _
  have hfin : selection law (1/4) 1048576 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (selection_le_rho _ _ _)
  obtain ⟨s, hs⟩ := selection_attained
  refine le_antisymm hle ?_
  rw [objective_eq optimalMask (J_lt_cap _), ← ENNReal.ofReal_toReal hfin, hs]
  exact ENNReal.ofReal_le_ofReal (J_optimal_min s)

/-- Distinct hard masks other than the optimal one have larger inner cost. -/
theorem objective_optimal_lt (s : Fin 3 → Bool) (hs : s ≠ optimalMask) :
    selectionObjective law (1/4) 1048576 (retained optimalMask) <
      selectionObjective law (1/4) 1048576 (retained s) := by
  rw [objective_eq optimalMask (J_lt_cap _), objective_eq s (J_lt_cap _)]
  exact (ENNReal.ofReal_lt_ofReal_iff ((J_nonneg _).trans_lt (J_optimal_lt s hs))).2
    (J_optimal_lt s hs)

end ThresholdHC.NonintervalSelection
