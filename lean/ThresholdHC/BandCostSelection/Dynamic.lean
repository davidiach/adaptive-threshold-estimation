import ThresholdHC.BandCostSelection.Compression
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Union

noncomputable section
open scoped Classical
namespace ThresholdHC.BandCostSelection

variable {α κ : Type*}

def traceKey (tag : α → κ) (xs : List α) : Multiset κ := ↑(xs.map tag)

def traceSaved (saving : α → ℝ) (xs : List α) : ℝ := (xs.map saving).sum

def extend (F : Finset (List α)) (menu : Finset α) : Finset (List α) :=
  F.biUnion fun xs => menu.image fun x => x :: xs

theorem mem_extend {F : Finset (List α)} {menu : Finset α} {ys : List α} :
    ys ∈ extend F menu ↔ ∃ xs ∈ F, ∃ x ∈ menu, x :: xs = ys := by
  simp [extend]

def enumerate : List (Finset α) → Finset (List α)
  | [] => {[]}
  | menu :: rest => extend (enumerate rest) menu

def solve (tag : α → κ) (saving : α → ℝ) : List (Finset α) → Finset (List α)
  | [] => {[]}
  | menu :: rest =>
      compress (traceKey tag) (traceSaved saving) (extend (solve tag saving rest) menu)

/-- Every retained trace uses one actual option from each menu. -/
theorem solve_subset (tag : α → κ) (saving : α → ℝ) (menus : List (Finset α)) :
    solve tag saving menus ⊆ enumerate menus := by
  induction menus with
  | nil => exact fun _ hx => hx
  | cons menu rest ih =>
    intro ys hy
    obtain ⟨xs, hx, x, hm, rfl⟩ := mem_extend.mp
      (compress_subset _ _ _ hy)
    exact mem_extend.mpr ⟨xs, ih hx, x, hm, rfl⟩

/-- Discarding dominated traces preserves a feasible representative with the same cost
multiset and at least as much saving, at every stage. -/
theorem solve_dominates (tag : α → κ) (saving : α → ℝ) (menus : List (Finset α))
    {xs : List α} (hx : xs ∈ enumerate menus) :
    ∃ ys ∈ solve tag saving menus,
      traceKey tag ys = traceKey tag xs ∧ traceSaved saving xs ≤ traceSaved saving ys := by
  induction menus generalizing xs with
  | nil =>
    exact ⟨xs, hx, rfl, le_refl _⟩
  | cons menu rest ih =>
    obtain ⟨tail, ht, x, hm, rfl⟩ := mem_extend.mp hx
    obtain ⟨kept, hk, he, hs⟩ := ih ht
    obtain ⟨ys, hy, hkey, hsaved⟩ := compress_dominates (traceKey tag) (traceSaved saving)
      (extend (solve tag saving rest) menu) (mem_extend.mpr ⟨kept, hk, x, hm, rfl⟩)
    refine ⟨ys, hy, hkey.trans ?_, le_trans ?_ hsaved⟩
    · change tag x ::ₘ traceKey tag kept = tag x ::ₘ traceKey tag tail
      rw [he]
    · change saving x + traceSaved saving tail ≤ saving x + traceSaved saving kept
      exact add_le_add (le_refl _) hs

theorem enumerate_length (menus : List (Finset α)) {xs : List α}
    (hx : xs ∈ enumerate menus) : xs.length = menus.length := by
  induction menus generalizing xs with
  | nil =>
    have : xs = [] := Finset.mem_singleton.mp hx
    simp [this]
  | cons menu rest ih =>
    obtain ⟨tail, ht, x, _, rfl⟩ := mem_extend.mp hx
    simpa using ih ht

/-- Clipping preserves the objective ordering established by equal-key dominance. -/
theorem solve_objective_dominates (tag : α → κ) (saving : α → ℝ)
    (menus : List (Finset α)) (price : Multiset κ → ℝ) (ordinary cap : ℝ)
    {xs : List α} (hx : xs ∈ enumerate menus) :
    ∃ ys ∈ solve tag saving menus,
      min cap (price (traceKey tag ys) + ordinary - traceSaved saving ys) ≤
        min cap (price (traceKey tag xs) + ordinary - traceSaved saving xs) := by
  obtain ⟨ys, hy, he, hs⟩ := solve_dominates tag saving menus hx
  refine ⟨ys, hy, ?_⟩
  rw [he]
  exact min_le_min_left _ (sub_le_sub_left hs _)

/-- The compressed frontier contains a global minimizer of the full finite menu
problem, for any cost-multiset price and any real clipping level. -/
theorem solve_attains (tag : α → κ) (saving : α → ℝ) (menus : List (Finset α))
    (hne : (enumerate menus).Nonempty) (price : Multiset κ → ℝ) (ordinary cap : ℝ) :
    ∃ ys ∈ solve tag saving menus, ∀ xs ∈ enumerate menus,
      min cap (price (traceKey tag ys) + ordinary - traceSaved saving ys) ≤
        min cap (price (traceKey tag xs) + ordinary - traceSaved saving xs) := by
  let objective := fun xs => min cap
    (price (traceKey tag xs) + ordinary - traceSaved saving xs)
  obtain ⟨xs, hx, hmin⟩ := (enumerate menus).exists_min_image objective hne
  obtain ⟨ys, hy, hdom⟩ := solve_objective_dominates tag saving menus price ordinary cap hx
  exact ⟨ys, hy, fun zs hz => hdom.trans (hmin zs hz)⟩

end ThresholdHC.BandCostSelection

