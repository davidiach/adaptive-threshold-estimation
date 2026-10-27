import Mathlib

/-!
The minimax and compactness step behind the common-hard-pair argument.
The input is a bound for every revealed finite mixture of constraints.
The conclusion is one point satisfying every individual constraint.

Applying this to statistical experiments still requires a compact convex
population-pair set, continuous convex Hellinger constraints, and the
policy-wise bound for every mixture. Those are not asserted by this module.
-/

noncomputable section
open Set

namespace ThresholdHC.CriticalEntropy

theorem finite_common_point {E ι : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [Fintype ι] [Nonempty ι]
    (X : Set E) (hne : X.Nonempty) (hcompact : IsCompact X) (hconvex : Convex ℝ X)
    (f : ι → E → ℝ) (hcont : ∀ i, Continuous (f i))
    (hconv : ∀ i, ConvexOn ℝ X (f i))
    (hmix : ∀ p : ι → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
      ∃ x ∈ X, (∑ i, p i * f i x) ≤ 0) :
    ∃ x ∈ X, ∀ i, f i x ≤ 0 := by
  classical
  let Y := stdSimplex ℝ ι
  let F : E → (ι → ℝ) → ℝ := fun x p => ∑ i, p i * f i x
  have hY : Convex ℝ Y := convex_stdSimplex ℝ ι
  have hYc : IsCompact Y := isCompact_stdSimplex ℝ ι
  have hYn : Y.Nonempty :=
    ⟨Pi.single (Classical.arbitrary ι) 1, single_mem_stdSimplex ℝ _⟩
  have hcx (p : ι → ℝ) (hp : p ∈ Y) : ConvexOn ℝ X (fun x => F x p) := by
    refine ⟨hconvex, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [F, smul_eq_mul]
    calc
      _ ≤ ∑ i, p i * (a * f i x + b * f i y) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left ((hconv i).2 hx hy ha hb hab) (hp.1 i)
      _ = _ := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hcy (x : E) : ConcaveOn ℝ Y (F x) := by
    refine ⟨hY, ?_⟩
    intro p hp q hq a b ha hb hab
    apply le_of_eq
    simp only [F, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hxc (p : ι → ℝ) : Continuous (fun x => F x p) := by
    exact continuous_finsetSum _ (fun i _ => (hcont i).const_mul (p i))
  have hyc (x : E) : Continuous (F x) := by
    dsimp [F]
    apply continuous_finsetSum
    intro i _
    exact (continuous_apply i).mul (continuous_const : Continuous (fun _ : ι → ℝ => f i x))
  obtain ⟨x, hx, p, hp, hsaddle⟩ := Sion.exists_isSaddlePointOn hne hconvex hcompact
    (fun p _ => (hxc p).continuousOn.lowerSemicontinuousOn)
    (fun p hp => (hcx p hp).quasiconvexOn)
    hY hYn hYc
    (fun x _ => (hyc x).continuousOn.upperSemicontinuousOn)
    (fun x _ => (hcy x).quasiconcaveOn)
  obtain ⟨z, hz, hzero⟩ := hmix p hp.1 hp.2
  refine ⟨x, hx, fun i => ?_⟩
  have hi := (hsaddle z hz (Pi.single i 1) (single_mem_stdSimplex ℝ i)).trans hzero
  simpa [F, Pi.single_apply] using hi

/-- Quantifier interchange for an arbitrary family of continuous convex
constraints. Compactness upgrades finite revealed-mixture feasibility to one
point satisfying all constraints, without a topology on the index type. -/
theorem common_point_of_finite_mixtures {E ι : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (X : Set E) (hne : X.Nonempty) (hcompact : IsCompact X) (hconvex : Convex ℝ X)
    (f : ι → E → ℝ) (hcont : ∀ i, Continuous (f i))
    (hconv : ∀ i, ConvexOn ℝ X (f i))
    (hmix : ∀ (s : Finset ι) (p : s → ℝ), (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
      ∃ x ∈ X, (∑ i : s, p i * f i x) ≤ 0) :
    ∃ x ∈ X, ∀ i, f i x ≤ 0 := by
  classical
  have hfinite (s : Finset ι) :
      (X ∩ ⋂ i ∈ s, {x | f i x ≤ 0}).Nonempty := by
    by_cases hs : s.Nonempty
    · let : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
      obtain ⟨x, hx, hall⟩ := finite_common_point X hne hcompact hconvex
        (fun i : s => f i) (fun i => hcont i) (fun i => hconv i) (hmix s)
      refine ⟨x, hx, ?_⟩
      simp only [mem_iInter, mem_ofPred_eq]
      exact fun i hi => hall ⟨i, hi⟩
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hs
      simpa using hne
  obtain ⟨x, hx, hall⟩ := hcompact.inter_iInter_nonempty
    (fun i => {x | f i x ≤ 0})
    (fun i => isClosed_le (hcont i) continuous_const) hfinite
  exact ⟨x, hx, fun i => Set.mem_iInter.mp hall i⟩

end ThresholdHC.CriticalEntropy
