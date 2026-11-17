import ThresholdHC.FiniteSelectionApproximation.States

noncomputable section
open scoped Classical
namespace ThresholdHC.FiniteSelectionApproximation
open ThresholdHC.SelectionApproximation ThresholdHC.BandCostSelection

variable {α : Type*}

def frontier (a saving : α → ℝ) (menus : List (Finset α)) (ε : ℝ) : Finset (List α) :=
  trimSolve (binKey (minCost a menus) (cellCount menus.length (maxCost a menus/minCost a menus) ε))
    a (summary a (minCost a menus) ε) saving menus

/-- A partial trace can be completed by empty options without changing either
summary. This puts every intermediate stage in the same input-derived box. -/
theorem complete_trace (a h : α → ℝ) (z : α) (haz : a z = 0) (hhz : h z = 0)
    (pre rest : List (Finset α)) (hzero : ∀ menu ∈ pre, z ∈ menu)
    {xs : List α} (hx : xs ∈ enumerate rest) :
    ∃ ys ∈ enumerate (pre++rest), traceSaved a ys = traceSaved a xs ∧
      traceSaved h ys = traceSaved h xs := by
  induction pre with
  | nil => exact ⟨xs,hx,rfl,rfl⟩
  | cons menu pre ih =>
    obtain ⟨ys,hy,ha,hh⟩ := ih (fun m hm => hzero m (List.mem_cons_of_mem _ hm))
    refine ⟨z::ys,mem_extend.mpr ⟨ys,hy,z,hzero menu List.mem_cons_self,rfl⟩,?_,?_⟩
    · simpa [traceSaved,haz] using ha
    · simpa [traceSaved,hhz] using hh

theorem feasible_key_bound (a : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (menus : List (Finset α)) (hm : 0 < menus.length)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 1 ≤ maxCost a menus/minCost a menus)
    {xs : List α} (hx : xs ∈ enumerate menus) :
    let r := minCost a menus
    let U := maxCost a menus
    let L := logScale (U/r)
    let M := cellCount menus.length (U/r) ε
    summaryKey (binKey r M) a (summary a r ε) xs ∈ stateKeys r U L M := by
  dsimp
  have hb := trace_summary_bounds ha hx hε hε1 hR
  exact summaryKey_mem (minCost_pos a menus) (cellCount_pos hm hε)
    (by have := logScale_ge_four (maxCost a menus/minCost a menus); linarith)
    (trace_nonneg ha xs) (trace_zero_or_lower ha hx) (trace_le_maxCost hx)
    hb.2.2.1 hb.2.2.2

/-- The exact bound `S` holds for every intermediate retained frontier. -/
theorem every_stage_card (a saving : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (menus : List (Finset α)) (hm : 0 < menus.length)
    (z : α) (haz : a z = 0) (hz : ∀ menu ∈ menus, z ∈ menu)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 1 ≤ maxCost a menus/minCost a menus)
    (rest : List (Finset α)) (ht : rest.IsSuffix menus) :
    let r := minCost a menus
    let R := maxCost a menus/r
    let M := cellCount menus.length R ε
    (trimSolve (binKey r M) a (summary a r ε) saving rest).card ≤ stateCount R (logScale R) M := by
  dsimp
  apply trimSolve_card_bound
  intro xs hx
  obtain ⟨pre,hpre⟩ := ht
  obtain ⟨ys,hy,ha',hh'⟩ := complete_trace a (summary a (minCost a menus) ε) z haz
    (by simp [summary,haz]) pre rest
    (fun menu hmenu => hz menu (hpre ▸ List.mem_append_left rest hmenu)) hx
  have hf : ys ∈ enumerate menus := hpre ▸ hy
  have hk := feasible_key_bound a ha menus hm hε hε1 hR hf
  dsimp only [summaryKey] at hk ⊢
  rw [ha',hh'] at hk
  exact hk

/-- Candidate-extension bound before trimming; arithmetic bit complexity is
deliberately not part of this combinatorial count. -/
theorem all_extensions_bound (a saving : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (menus : List (Finset α)) (hm : 0 < menus.length)
    (z : α) (haz : a z = 0) (hz : ∀ menu ∈ menus, z ∈ menu)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 1 ≤ maxCost a menus/minCost a menus) :
    let r := minCost a menus
    let R := maxCost a menus/r
    let M := cellCount menus.length R ε
    extensionCount (binKey r M) a (summary a r ε) saving menus ≤
      (menus.map Finset.card).sum*stateCount R (logScale R) M := by
  dsimp
  apply extensionCount_bound
  exact every_stage_card a saving ha menus hm z haz hz hε hε1 hR

end ThresholdHC.FiniteSelectionApproximation
