import Mathlib

/-! A compact maximizing player supplies one common certificate against an
arbitrary convex minimizing domain. This is a direct consequence of Sion's
finite-cover theorem, including attainment at the stated threshold. -/

noncomputable section
open Set

namespace ThresholdHC.StoppingProgram

theorem compact_minimax_selection {E F : Type}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (X : Set E) (Y : Set F) (hne : X.Nonempty) (hc : IsCompact X)
    (hX : Convex ℝ X) (hY : Convex ℝ Y) (L : E → F → ℝ)
    (hxc : ∀ y, Continuous (fun x => L x y)) (hyc : ∀ x, Continuous (L x))
    (hconc : ∀ y ∈ Y, ConcaveOn ℝ X (fun x => L x y))
    (hconv : ∀ x ∈ X, ConvexOn ℝ Y (L x))
    (p : ℝ) (hpoint : ∀ y ∈ Y, ∃ x ∈ X, p ≤ L x y) :
    ∃ x ∈ X, ∀ y ∈ Y, p ≤ L x y := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨s,hs⟩ := hc.elim_finite_subcover
    (fun y : Y => {x | -p < -L x y.val})
    (fun y => isOpen_lt continuous_const (hxc y.val).neg) (by
      intro x hx
      obtain ⟨y,hy,hh⟩ := hn x hx
      exact mem_iUnion.mpr ⟨⟨y,hy⟩,by change -p < -L x y; linarith⟩)
  let t : Set F := Subtype.val '' (s:Set Y)
  have ht : t.Finite := s.finite_toSet.image _
  have htY : t ⊆ Y := by
    rintro y ⟨z,hz,rfl⟩
    exact z.property
  have hfinite : ∀ x ∈ X, ∃ y ∈ t, -p < -L x y := by
    intro x hx
    obtain ⟨y,hy⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hys,hh⟩ := mem_iUnion.mp hy
    exact ⟨y.val,⟨y,hys,rfl⟩,hh⟩
  obtain ⟨y,hy,hh⟩ := Sion.exists_lt_iInf_of_lt_iInf_of_finite hne hc
    (fun y _ => (hxc y).neg.continuousOn.lowerSemicontinuousOn)
    (fun y hy => (hconc y hy).neg.quasiconvexOn) hY
    (fun x _ => (hyc x).neg.continuousOn.upperSemicontinuousOn)
    (fun x hx => (hconv x hx).neg.quasiconcaveOn) hX ht htY hfinite
  obtain ⟨x,hx,hxy⟩ := hpoint y hy
  have hh' := hh x hx
  change -p < -L x y at hh'
  linarith

end ThresholdHC.StoppingProgram
