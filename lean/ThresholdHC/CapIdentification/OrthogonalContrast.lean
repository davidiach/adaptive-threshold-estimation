import ThresholdHC.CapIdentification.PolynomialL2

/-! A support with more than L points supplies a nonzero bounded polynomial
contrast orthogonal to the first L odd moments. Its integral equals its
strictly positive squared L2 norm. -/

noncomputable section
open MeasureTheory Polynomial Set
open scoped BigOperators

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap)

theorem constant_not_in_oddL2Span (μ : Measure Gap) [IsFiniteMeasure μ] (L : ℕ)
    (S : Finset Gap) (hS : (S:Set Gap) ⊆ μ.support) (hcard : L < S.card) :
    polynomialL2 μ 1 ∉ oddL2Span μ L := by
  classical
  intro h
  obtain ⟨a,ha⟩ := (mem_oddL2Span μ _).mp h
  have he : (fun d : Gap => (oddPolynomial a).eval (d:ℝ)) =ᵐ[μ] (fun _ => (1:ℝ)) := by
    filter_upwards [polynomialL2_ae μ (oddPolynomial a),polynomialL2_ae μ 1] with d hP h1
    rw [← hP,ha,h1,eval_one]
  have hclosed : IsClosed {d : Gap | (oddPolynomial a).eval (d:ℝ) = 1} :=
    isClosed_eq ((oddPolynomial a).continuous.comp continuous_subtype_val) continuous_const
  have hs := μ.support_subset_of_isClosed hclosed he
  have hc := odd_level_card_le a (S.image (fun d : Gap => (d:ℝ)))
    (fun x hx => by obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hx; exact d.property.1)
    (fun x hx => by obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hx; exact hs (hS hd))
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
  omega

theorem constant_not_in_oddL2Span_infinite (μ : Measure Gap) [IsFiniteMeasure μ]
    (hμ : μ.support.Infinite) (L : ℕ) : polynomialL2 μ 1 ∉ oddL2Span μ L := by
  obtain ⟨S,hS,hcard⟩ := hμ.exists_subset_card_eq (L+1)
  exact constant_not_in_oddL2Span μ L S hS (by omega)

theorem exists_polynomial_moment_contrast (μ : Measure Gap) [IsFiniteMeasure μ] (L : ℕ)
    (hnot : polynomialL2 μ 1 ∉ oddL2Span μ L) :
    ∃ a : Fin L → ℝ,
      (∀ j : Fin L, ∫ d : Gap, (1-(oddPolynomial a).eval (d:ℝ))*(d:ℝ)^(2*j.val+1) ∂μ = 0) ∧
      (∫ d : Gap, 1-(oddPolynomial a).eval (d:ℝ) ∂μ) =
        (∫ d : Gap, (1-(oddPolynomial a).eval (d:ℝ))^2 ∂μ) ∧
      0 < ∫ d : Gap, (1-(oddPolynomial a).eval (d:ℝ))^2 ∂μ := by
  let V := oddL2Span μ L
  let u := polynomialL2 μ 1
  let p := V.starProjection u
  have hp : p ∈ V := V.starProjection_apply_mem u
  obtain ⟨a,ha⟩ := (mem_oddL2Span μ p).mp hp
  let H : ℝ[X] := 1-oddPolynomial a
  have hres : polynomialL2 μ H = u-p := by
    dsimp only [H,u]
    rw [map_sub,ha]
  have hne : u-p ≠ 0 := by
    intro hzero
    have hu : u = p := sub_eq_zero.mp hzero
    apply hnot
    change u ∈ V
    rw [hu]
    exact hp
  have hort : inner ℝ (u-p) p = 0 := V.starProjection_inner_eq_zero u p hp
  refine ⟨a,?_,?_,?_⟩
  · intro j
    have hj : polynomialL2 μ (X^(2*j.val+1)) ∈ V := Submodule.subset_span ⟨j,rfl⟩
    have ho := V.starProjection_inner_eq_zero u _ hj
    rw [← hres,polynomialL2_inner] at ho
    simpa only [H,eval_sub,eval_one,eval_pow,eval_X] using ho
  · have he : inner ℝ (polynomialL2 μ H) (polynomialL2 μ H) =
        inner ℝ (polynomialL2 μ H) (polynomialL2 μ 1) := by
      rw [hres,inner_sub_right,hort,sub_zero]
    simp only [polynomialL2_inner,H,eval_sub,eval_one,mul_one,← sq] at he
    exact he.symm
  · have hpos := real_inner_self_pos.mpr hne
    rw [← hres,polynomialL2_inner] at hpos
    simpa only [H,eval_sub,eval_one,← sq] using hpos

end ThresholdHC.CapIdentification
