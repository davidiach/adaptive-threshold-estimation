import ThresholdHC.BandCostSelection.Dynamic
import Mathlib.Data.Sym.Card

noncomputable section
open scoped Classical
namespace ThresholdHC.BandCostSelection

variable {α κ : Type*}

theorem solve_key_injective (tag : α → κ) (saving : α → ℝ) (menus : List (Finset α)) :
    Set.InjOn (traceKey tag) (solve tag saving menus : Set (List α)) := by
  cases menus with
  | nil =>
    intro xs hx ys hy _
    have hx' : xs = [] := Finset.mem_singleton.mp hx
    have hy' : ys = [] := Finset.mem_singleton.mp hy
    exact hx'.trans hy'.symm
  | cons menu rest => exact key_injective_on_compress _ _ _

/-- Include the zero/empty option as one tag. A length-m trace is then a size-m
multiset over r+1 tags, giving the weak-composition state bound. -/
theorem solve_card_le (r : ℕ) (tag : α → Fin (r+1)) (saving : α → ℝ)
    (menus : List (Finset α)) :
    (solve tag saving menus).card ≤ (menus.length+r).choose r := by
  let code (xs : ↥(solve tag saving menus)) : Sym (Fin (r+1)) menus.length :=
    ⟨traceKey tag xs.val, by
      simpa [traceKey] using enumerate_length menus (solve_subset tag saving menus xs.property)⟩
  have hinj : Function.Injective code := by
    intro xs ys he
    apply Subtype.ext
    apply solve_key_injective tag saving menus xs.property ys.property
    exact congrArg (fun s : Sym (Fin (r+1)) menus.length => s.val) he
  have hcard := Fintype.card_le_of_injective code hinj
  rw [Fintype.card_coe, Sym.card_sym_eq_choose, Fintype.card_fin] at hcard
  have hindex : r + 1 + menus.length - 1 = menus.length + r := by omega
  rw [hindex, Nat.choose_symm_add] at hcard
  exact hcard

/-- Number of candidate extensions examined before grouping, counting each pair
of a retained prefix and an option once. The recursion processes the tail first. -/
def transitionCount (tag : α → κ) (saving : α → ℝ) : List (Finset α) → ℕ
  | [] => 0
  | menu :: rest =>
      (solve tag saving rest).card * menu.card + transitionCount tag saving rest

def transitionBound (r : ℕ) : List (Finset α) → ℕ
  | [] => 0
  | menu :: rest =>
      (rest.length+r).choose r * menu.card + transitionBound r rest

theorem transitionCount_le (r : ℕ) (tag : α → Fin (r+1)) (saving : α → ℝ)
    (menus : List (Finset α)) :
    transitionCount tag saving menus ≤ transitionBound r menus := by
  induction menus with
  | nil => exact le_refl _
  | cons menu rest ih =>
    exact Nat.add_le_add (Nat.mul_le_mul_right menu.card (solve_card_le r tag saving rest)) ih

end ThresholdHC.BandCostSelection

