import Mathlib

/-! Actual attained robust maxima over a compact moment set, with their
convexity in the program variable. -/

noncomputable section
open Set

namespace ThresholdHC.StoppingProgram

def compactMaximum {E : Type} (K : Set E) (f : E → ℝ) : ℝ := sSup (f '' K)

theorem compactMaximum_attained {E : Type} [TopologicalSpace E]
    (K : Set E) (hne : K.Nonempty) (hc : IsCompact K) (f : E → ℝ) (hf : ContinuousOn f K) :
    ∃ u ∈ K, compactMaximum K f = f u := by
  obtain ⟨u,hu,hmax⟩ := hc.exists_isMaxOn hne hf
  refine ⟨u,hu,le_antisymm ?_ ?_⟩
  · exact csSup_le (hne.image f) (by rintro z ⟨v,hv,rfl⟩; exact hmax hv)
  · exact le_csSup (hc.bddAbove_image hf) (mem_image_of_mem f hu)

theorem le_compactMaximum {E : Type} [TopologicalSpace E]
    (K : Set E) (hc : IsCompact K) (f : E → ℝ) (hf : ContinuousOn f K)
    {u : E} (hu : u ∈ K) : f u ≤ compactMaximum K f :=
  le_csSup (hc.bddAbove_image hf) (mem_image_of_mem f hu)

theorem compactMaximum_le_iff {E : Type} [TopologicalSpace E]
    (K : Set E) (hne : K.Nonempty) (hc : IsCompact K) (f : E → ℝ) (hf : ContinuousOn f K) (c : ℝ) :
    compactMaximum K f ≤ c ↔ ∀ u ∈ K, f u ≤ c := by
  constructor
  · intro hh u hu
    exact (le_compactMaximum K hc f hf hu).trans hh
  · intro hh
    exact csSup_le (hne.image f) (by rintro z ⟨u,hu,rfl⟩; exact hh u hu)

theorem compactMaximum_convex {E F : Type} [TopologicalSpace E] [AddCommGroup F] [Module ℝ F]
    (K : Set E) (hne : K.Nonempty) (hc : IsCompact K)
    (S : Set F) (hS : Convex ℝ S) (f : E → F → ℝ)
    (hfc : ∀ x, ContinuousOn (fun u => f u x) K)
    (hfv : ∀ u ∈ K, ConvexOn ℝ S (f u)) :
    ConvexOn ℝ S (fun x => compactMaximum K (fun u => f u x)) := by
  refine ⟨hS,?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨u,hu,he⟩ := compactMaximum_attained K hne hc _ (hfc (a • x+b • y))
  dsimp only
  rw [he]
  exact ((hfv u hu).2 hx hy ha hb hab).trans (add_le_add
    (mul_le_mul_of_nonneg_left (le_compactMaximum K hc _ (hfc x) hu) ha)
    (mul_le_mul_of_nonneg_left (le_compactMaximum K hc _ (hfc y) hu) hb))

end ThresholdHC.StoppingProgram
