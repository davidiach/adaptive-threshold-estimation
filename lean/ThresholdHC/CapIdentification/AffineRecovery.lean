import Mathlib

/-! Approximate affine recovery of a target coordinate from finitely many
features on a compact convex set. Sion's theorem removes the point-dependent
choice of coefficients; no duality assumption is added. -/

noncomputable section
open Set
open scoped BigOperators

namespace ThresholdHC.CapIdentification

theorem compact_affine_recovery {I : Type} [Fintype I]
    (X : Set (Option I → ℝ)) (hne : X.Nonempty) (hc : IsCompact X) (hv : Convex ℝ X)
    (δ : ℝ) (hδ : ∀ x ∈ X, (∀ i, x (some i) = 0) → x none ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : I → ℝ, ∀ x ∈ X, x none-(∑ i, w i*x (some i)) < δ+ε := by
  classical
  let F : (Option I → ℝ) → (I → ℝ) → ℝ := fun x w => (∑ i, w i*x (some i))-x none
  have hxc (w : I → ℝ) : Continuous (fun x => F x w) := by
    dsimp only [F]
    fun_prop
  have hwc (x : Option I → ℝ) : Continuous (F x) := by
    dsimp only [F]
    fun_prop
  have hconv (w : I → ℝ) : ConvexOn ℝ X (fun x => F x w) := by
    refine ⟨hv,?_⟩
    intro x hx y hy a b ha hb hab
    apply le_of_eq
    simp only [F,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    have he : (∑ i, w i*(a*x (some i)+b*y (some i))) =
        a*(∑ i, w i*x (some i))+b*(∑ i, w i*y (some i)) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    ring
  have hconc (x : Option I → ℝ) : ConcaveOn ℝ univ (F x) := by
    refine ⟨convex_univ,?_⟩
    intro w hw v hV a b ha hb hab
    simp only [F,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    have he : (∑ i, (a*w i+b*v i)*x (some i)) =
        a*(∑ i, w i*x (some i))+b*(∑ i, v i*x (some i)) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    have htarget := congrArg (fun r : ℝ => r*x none) hab
    nlinarith [htarget]
  let t := -(δ+ε)
  have hpoint (x : Option I → ℝ) (hx : x ∈ X) : ∃ w : I → ℝ, t < F x w := by
    by_cases hz : ∀ i, x (some i) = 0
    · refine ⟨0,?_⟩
      have hb := hδ x hx hz
      simp only [F,Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_sub]
      dsimp only [t]
      linarith
    · push Not at hz
      obtain ⟨i,hi⟩ := hz
      let a := (t+x none+1)/x (some i)
      refine ⟨Pi.single i a,?_⟩
      have he : (∑ j, (Pi.single i a : I → ℝ) j*x (some j)) = a*x (some i) := by
        simp [Pi.single_apply,ite_mul]
      rw [show F x (Pi.single i a) = a*x (some i)-x none by exact congrArg (fun z => z-x none) he]
      dsimp only [a]
      rw [div_mul_cancel₀ _ hi]
      linarith
  obtain ⟨s,hs⟩ := hc.elim_finite_subcover (fun w : I → ℝ => {x | t < F x w})
    (fun w => isOpen_lt continuous_const (hxc w)) (by
      intro x hx
      obtain ⟨w,hw⟩ := hpoint x hx
      exact mem_iUnion.mpr ⟨w,hw⟩)
  have hfinite : ∀ x ∈ X, ∃ w ∈ (s:Set (I → ℝ)), t < F x w := by
    intro x hx
    obtain ⟨w,hw⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hws,hwval⟩ := mem_iUnion.mp hw
    exact ⟨w,hws,hwval⟩
  obtain ⟨w,_,hw⟩ := Sion.exists_lt_iInf_of_lt_iInf_of_finite hne hc
    (fun w _ => (hxc w).continuousOn.lowerSemicontinuousOn)
    (fun w _ => (hconv w).quasiconvexOn) convex_univ
    (fun x _ => (hwc x).continuousOn.upperSemicontinuousOn)
    (fun x _ => (hconc x).quasiconcaveOn) hv s.finite_toSet (subset_univ _) hfinite
  refine ⟨w,?_⟩
  intro x hx
  have hh := hw x hx
  dsimp only [F,t] at hh
  linarith

end ThresholdHC.CapIdentification
