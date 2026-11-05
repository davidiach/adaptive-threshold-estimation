
import ThresholdHC.BandCostSelection.Entropy
import ThresholdHC.BandCostSelection.Comparison
import ThresholdHC.BandCostSelection.Certificates
noncomputable section
set_option linter.unusedVariables false
open scoped BigOperators Classical
open ThresholdHC.BandCostSelection

example : ∀ {α κ : Type*} (key : α → κ) (saved : α → ℝ) (F : Finset α)
    {x : α} (hx : x ∈ F),
    ∃ y ∈ compress key saved F, key y = key x ∧ saved x ≤ saved y :=
  @compress_dominates

example : ∀ {α κ : Type*} (key : α → κ) (saved : α → ℝ) (F : Finset α),
    (compress key saved F).card = (F.image key).card := @compress_card

example : ∀ {α κ : Type*} (tag : α → κ) (saving : α → ℝ) (menus : List (Finset α)),
    solve tag saving menus ⊆ enumerate menus := @solve_subset

example : ∀ {α κ : Type*} (tag : α → κ) (saving : α → ℝ) (menus : List (Finset α))
    {xs : List α} (hx : xs ∈ enumerate menus),
    ∃ ys ∈ solve tag saving menus,
      traceKey tag ys = traceKey tag xs ∧ traceSaved saving xs ≤ traceSaved saving ys :=
  @solve_dominates

example : ∀ {α κ : Type*} (tag : α → κ) (saving : α → ℝ) (menus : List (Finset α))
    (hne : (enumerate menus).Nonempty) (price : Multiset κ → ℝ) (ordinary cap : ℝ),
    ∃ ys ∈ solve tag saving menus, ∀ xs ∈ enumerate menus,
      min cap (price (traceKey tag ys) + ordinary - traceSaved saving ys) ≤
        min cap (price (traceKey tag xs) + ordinary - traceSaved saving xs) :=
  @solve_attains

example : ∀ {α : Type*} (r : ℕ) (tag : α → Fin (r+1)) (saving : α → ℝ)
    (menus : List (Finset α)),
    (solve tag saving menus).card ≤ (menus.length+r).choose r := @solve_card_le

example : ∀ {α : Type*} (r : ℕ) (tag : α → Fin (r+1)) (saving : α → ℝ)
    (menus : List (Finset α)),
    transitionCount tag saving menus ≤ transitionBound r menus := @transitionCount_le

example : ∀ a : Multiset ℝ, multisetEntropy (0 ::ₘ a) = multisetEntropy a :=
  @multisetEntropy_zero_cons

example : ∀ {n : ℕ} (a : Fin n → ℝ), multisetEntropy (↑(List.ofFn a)) =
    ThresholdHC.EntropyTailQuantile.costEntropy a := @multisetEntropy_ofFn

example : ∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i),
    multisetEntropy (↑(List.ofFn a)) =
      (∑ i, a i) + ∑ i, a i * Real.log ((∑ j, a j) / a i) :=
  @multisetEntropy_log_formula

example : ∀ {α κ : Type*} (tag : α → κ) (cost : κ → ℝ) (saving : α → ℝ)
    (menus : List (Finset α)) (hne : (enumerate menus).Nonempty) (ρ B ordinary : ℝ),
    ∃ ys ∈ solve tag saving menus, ∀ xs ∈ enumerate menus,
      min ρ (Real.sqrt (ρ * multisetEntropy ((traceKey tag ys).map cost) / B) +
        ordinary - traceSaved saving ys) ≤
      min ρ (Real.sqrt (ρ * multisetEntropy ((traceKey tag xs).map cost) / B) +
        ordinary - traceSaved saving xs) := @entropy_solve_attains

example : ∀ (x y : ℝ) {B : ℝ} (hB : 0 < B),
    savingPositive x y B ↔ 0 < x + y / Real.sqrt B := @savingPositive_iff

example : ∀ {α : Type*} (F : Finset α) (value lower upper : α → ℝ)
    (hb : ∀ x ∈ F, lower x ≤ value x ∧ value x ≤ upper x)
    {chosen : α} (hc : chosen ∈ F)
    (hsep : ∀ x ∈ F, x ≠ chosen → upper chosen ≤ lower x),
    ∀ x ∈ F, value chosen ≤ value x := @interval_certificate

example : ∀ {α : Type*} (F : Finset α) (value lower upper : α → ℝ)
    (hb : ∀ x ∈ F, lower x ≤ value x ∧ value x ≤ upper x)
    {lo chosen optimum : α} (hc : chosen ∈ F) (ho : optimum ∈ F)
    (hlo : ∀ x ∈ F, lower lo ≤ lower x)
    (hopt : ∀ x ∈ F, value optimum ≤ value x),
    lower lo ≤ value optimum ∧ value optimum ≤ upper chosen := @interval_enclosure
#print axioms ThresholdHC.BandCostSelection.compress_card
#print axioms ThresholdHC.BandCostSelection.compress_dominates
#print axioms ThresholdHC.BandCostSelection.entropy_solve_attains
#print axioms ThresholdHC.BandCostSelection.interval_certificate
#print axioms ThresholdHC.BandCostSelection.interval_enclosure
#print axioms ThresholdHC.BandCostSelection.multisetEntropy_log_formula
#print axioms ThresholdHC.BandCostSelection.multisetEntropy_ofFn
#print axioms ThresholdHC.BandCostSelection.multisetEntropy_zero_cons
#print axioms ThresholdHC.BandCostSelection.savingPositive_iff
#print axioms ThresholdHC.BandCostSelection.solve_attains
#print axioms ThresholdHC.BandCostSelection.solve_card_le
#print axioms ThresholdHC.BandCostSelection.solve_dominates
#print axioms ThresholdHC.BandCostSelection.solve_subset
#print axioms ThresholdHC.BandCostSelection.transitionCount_le
