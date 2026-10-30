import Mathlib

/-! Finite convex inequality multipliers, derived from geometric separation.
The strict feasibility premise concerns the actual finite inequalities; no
duality or attainment theorem is assumed. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace ThresholdHC.StoppingProgram

theorem linear_pi_expansion {I : Type} [Fintype I] [DecidableEq I] (l : (I → ℝ) →ₗ[ℝ] ℝ)
    (u : I → ℝ) : l u = ∑ i, l (Pi.single i 1)*u i := by
  classical
  have hu : u = ∑ i, u i • (Pi.single i 1 : I → ℝ) := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  calc
    l u = l (∑ i, u i • (Pi.single i 1 : I → ℝ)) := congrArg l hu
    _ = ∑ i, l (u i • (Pi.single i 1 : I → ℝ)) := map_sum l _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      simp only [smul_eq_mul]
      ring

theorem finite_slater_multipliers {E I : Type} [AddCommGroup E] [Module ℝ E]
    [Fintype I] (S : Set E) (hS : Convex ℝ S) (g : Option I → E → ℝ)
    (hg : ∀ i, ConvexOn ℝ S (g i)) (p : ℝ)
    (hlower : ∀ x ∈ S, (∀ i, g (some i) x ≤ 0) → p ≤ g none x)
    (hstrict : ∃ x ∈ S, ∀ i, g (some i) x < 0) :
    ∃ weights : I → ℝ, (∀ i, 0 ≤ weights i) ∧
      ∀ x ∈ S, p ≤ g none x+∑ i, weights i*g (some i) x := by
  classical
  let A : Set (Option I → ℝ) := {u | ∃ x ∈ S, ∀ i, g i x < u i}
  let v : Option I → ℝ := Pi.single none p
  have hAopen : IsOpen A := by
    have heq : A = ⋃ x ∈ S, {u : Option I → ℝ | ∀ i, g i x < u i} := by
      ext u
      simp [A]
    rw [heq]
    apply isOpen_iUnion
    intro x
    apply isOpen_iUnion
    intro hx
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const
      (show Continuous (fun u : Option I → ℝ => u i) from continuous_apply i))
  have hAconvex : Convex ℝ A := by
    intro u hu w hw a b ha hb hab
    obtain ⟨x,hx,hxu⟩ := hu
    obtain ⟨y,hy,hyw⟩ := hw
    refine ⟨a • x+b • y,hS hx hy ha hb hab,?_⟩
    intro i
    have h := (hg i).2 hx hy ha hb hab
    change g i (a • x+b • y) ≤ a*g i x+b*g i y at h
    change g i (a • x+b • y) < a*u i+b*w i
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa [hb0,ha1] using h.trans_lt (by simpa [hb0,ha1] using hxu i)
    · exact h.trans_lt (add_lt_add_of_le_of_lt
        (mul_le_mul_of_nonneg_left (hxu i).le ha)
        (mul_lt_mul_of_pos_left (hyw i) (lt_of_le_of_ne hb (Ne.symm hb0))))
  have hv : v ∉ A := by
    rintro ⟨x,hx,h⟩
    have hh := hlower x hx (fun i => by simpa [v,Pi.single_apply] using (h (some i)).le)
    have hh' := h none
    simp only [v,Pi.single_eq_same] at hh'
    linarith
  obtain ⟨l,hl⟩ := geometric_hahn_banach_point_open hAconvex hAopen hv
  let a : Option I → ℝ := fun i => l (Pi.single i 1)
  have hexpand (u : Option I → ℝ) : l u = ∑ i, a i*u i :=
    linear_pi_expansion l.toLinearMap u
  obtain ⟨x0,hx0,hs0⟩ := hstrict
  let u0 : Option I → ℝ := fun i => g i x0+1
  have hu0 : u0 ∈ A := ⟨x0,hx0,fun i => by dsimp [u0]; linarith⟩
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    by_contra hn
    have hn' : a i < 0 := lt_of_not_ge hn
    let t := (l u0-l v+1)/(-a i)
    have ht : 0 ≤ t := by
      have hh := hl u0 hu0
      dsimp [t]
      exact div_nonneg (by linarith) (by linarith)
    have hmem : u0+t • Pi.single i 1 ∈ A := by
      refine ⟨x0,hx0,?_⟩
      intro j
      change g j x0 < u0 j+t*(Pi.single i 1 : Option I → ℝ) j
      have he : 0 ≤ t*(Pi.single i 1 : Option I → ℝ) j := by
        apply mul_nonneg ht
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      dsimp [u0]
      linarith
    have hh := hl _ hmem
    rw [map_add,map_smul] at hh
    change l v < l u0+t*a i at hh
    have he : t*a i = -(l u0-l v+1) := by
      dsimp [t]
      field_simp [ne_of_lt hn']
    rw [he] at hh
    linarith
  have ha0 : 0 < a none := by
    have hmem : Pi.single none (g none x0+1) ∈ A := by
      refine ⟨x0,hx0,?_⟩
      intro i
      cases i with
      | none => simp
      | some i => simpa using hs0 i
    have hh := hl _ hmem
    rw [hexpand,hexpand] at hh
    simp only [v,Pi.single_apply,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hh
    have hne : a none ≠ 0 := by intro he; rw [he,zero_mul,zero_mul] at hh; exact lt_irrefl _ hh
    exact lt_of_le_of_ne (ha none) (Ne.symm hne)
  have hbound (x : E) (hx : x ∈ S) : l v ≤ l (fun i => g i x) := by
    have hlim : Tendsto (fun n : ℕ => fun i => g i x+1/((n:ℝ)+1)) atTop
        (𝓝 (fun i => g i x)) := by
      apply tendsto_pi_nhds.mpr
      intro i
      simpa only [add_zero] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_add (g i x)
    apply ge_of_tendsto (l.continuous.tendsto _ |>.comp hlim)
    exact Filter.Eventually.of_forall (fun n => (hl _ ⟨x,hx,fun i => by
      have : 0 < 1/((n:ℝ)+1) := by positivity
      linarith⟩).le)
  refine ⟨fun i => a (some i)/a none,fun i => div_nonneg (ha _) ha0.le,?_⟩
  intro x hx
  have hh := hbound x hx
  rw [hexpand,hexpand] at hh
  simp only [v,Pi.single_apply,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hh
  rw [Fintype.sum_option] at hh
  apply (mul_le_mul_iff_right₀ ha0).mp
  have heach (i : I) : (a (some i)/a none*g (some i) x)*a none = a (some i)*g (some i) x := by
    field_simp
  have he : (g none x+∑ i, a (some i)/a none*g (some i) x)*a none =
      a none*g none x+∑ i, a (some i)*g (some i) x := by
    rw [add_mul,Finset.sum_mul]
    simp only [heach]
    ring
  change a none*p ≤ a none*(g none x+∑ i, a (some i)/a none*g (some i) x)
  rw [mul_comm (a none) (g none x+_),he]
  exact hh

end ThresholdHC.StoppingProgram
