import ThresholdHC.CapIdentification.OddPolynomials

/-! Exact finite-dimensional identifiability by odd moments. When there are
too few moments, linear separation gives an actual moment-matching contrast
with a nonzero target sum. -/

noncomputable section
open Set Polynomial
open scoped BigOperators

namespace ThresholdHC.CapIdentification

def oddVector {m : ℕ} (d : Fin m → ℝ) (j : ℕ) : Fin m → ℝ := fun i => (d i)^(2*j+1)

theorem constant_not_in_odd_span {m L : ℕ} (d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (hi : Function.Injective d) (hLm : L < m) :
    (fun _ : Fin m => (1:ℝ)) ∉ Submodule.span ℝ (Set.range (fun j : Fin L => oddVector d j.val)) := by
  classical
  intro h
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp h
  have hval (i : Fin m) : (oddPolynomial a).eval (d i) = 1 := by
    have he := congrFun ha i
    simpa only [oddPolynomial_eval,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,oddVector] using he
  have hcard := odd_level_card_le a (Finset.univ.image d)
    (fun x hx => by obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx; exact hd i)
    (fun x hx => by obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx; exact hval i)
  rw [Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin] at hcard
  omega

theorem functional_eq_coordinate_sum {m : ℕ} (f : (Fin m → ℝ) →ₗ[ℝ] ℝ) (v : Fin m → ℝ) :
    f v = ∑ i : Fin m, v i*f (Pi.single i 1) := by
  classical
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum,map_smul,smul_eq_mul]

theorem exists_odd_moment_contrast {m L : ℕ} (d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (hi : Function.Injective d) (hLm : L < m) :
    ∃ g : Fin m → ℝ, (∑ i, g i) ≠ 0 ∧
      ∀ j : Fin L, (∑ i, g i*(d i)^(2*j.val+1)) = 0 := by
  classical
  obtain ⟨f,hf,hker⟩ := Submodule.exists_le_ker_of_notMem (constant_not_in_odd_span d hd hi hLm)
  refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
  · rw [functional_eq_coordinate_sum] at hf
    simpa only [one_mul] using hf
  · intro j
    have hmem : oddVector d j.val ∈ Submodule.span ℝ (Set.range (fun j : Fin L => oddVector d j.val)) :=
      Submodule.subset_span ⟨j,rfl⟩
    have he : f (oddVector d j.val) = 0 := hker hmem
    rw [functional_eq_coordinate_sum] at he
    simpa only [oddVector,mul_comm] using he

def MomentsDetermineTarget {m : ℕ} (d : Fin m → ℝ) (L : ℕ) : Prop :=
  ∀ g : Fin m → ℝ, (∀ j : Fin L, (∑ i, g i*(d i)^(2*j.val+1)) = 0) → (∑ i, g i) = 0

theorem moments_determine_target_iff {m L : ℕ} (d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (hi : Function.Injective d) : MomentsDetermineTarget d L ↔ m ≤ L := by
  constructor
  · intro h
    by_contra h'
    obtain ⟨g,hg,hm⟩ := exists_odd_moment_contrast d hd hi (lt_of_not_ge h')
    exact hg (h g hm)
  · intro h g hg
    have hm (j : Fin m) : (∑ i : Fin m, (1:ℝ)*g i*(d i)^(2*j.val+1)) = 0 := by
      simpa only [one_mul] using hg ⟨j.val,lt_of_lt_of_le j.isLt h⟩
    simpa only [one_mul] using finite_moment_target_identified d (fun _ => 1) g hd hi hm

theorem moments_cap_threshold {m : ℕ} (d : Fin m → ℝ) (N : ℕ)
    (hd : ∀ i, 0 < d i) (hi : Function.Injective d) (hm : 0 < m) :
    MomentsDetermineTarget d ((N+1)/2) ↔ 2*m-1 ≤ N :=
  (moments_determine_target_iff d hd hi).trans (cap_threshold_equivalence N m hm)

end ThresholdHC.CapIdentification
