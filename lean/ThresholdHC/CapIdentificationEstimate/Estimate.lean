import ThresholdHC.CapIdentificationEstimate.Specification
import ThresholdHC.CapIdentification.RareContrast
import ThresholdHC.CapIdentification.OrthogonalContrast

/-! The proof of `ExplicitCapEstimateStatement`.

The residual `h = 1 - proj_{V_L} 1` is the L²(μ) class of a polynomial, so it
is bounded on the gap interval and its `L^∞(μ)` norm `M` is finite; it is
nonzero because `1 ∉ V_L`, so `M > 0`. Orthogonality of the residual gives the
odd-moment identities and `∫ h = ⟪h, 1⟫ = ⟪h, h⟫ = ‖h‖²`. A pointwise
truncation of the polynomial at level `M` agrees with `h` almost everywhere
and is bounded by `M` everywhere, so `rare_priors_of_bounded_contrast` builds
the rare sign laws `ρ/2 ± ρ/(4M) h`. They match the odd moments and have target
gap `ρ/(2M) ∫ h = ρ‖h‖²/(2M)`, which is at most the attained diameter `Δ_N`.

The last theorem checks that the hypothesis `1 ∉ V_L` is satisfiable for every
`L`: it holds for the uniform law on `L+1` distinct gaps. -/

noncomputable section
namespace ThresholdHC.CapIdentificationEstimate
open MeasureTheory Polynomial
open scoped ENNReal RealInnerProductSpace
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.CapIdentification

/-- The orthogonal residual of the constant `1` against `V_L` is the L²(μ)
class of a polynomial. -/
theorem residual_polynomial (μ : Measure Gap) [IsFiniteMeasure μ] (L : ℕ) :
    ∃ H : ℝ[X], polynomialL2 μ H =
      polynomialL2 μ 1 - (oddL2Span μ L).starProjection (polynomialL2 μ 1) := by
  obtain ⟨a,ha⟩ := (mem_oddL2Span μ _).mp
    ((oddL2Span μ L).starProjection_apply_mem (polynomialL2 μ 1))
  exact ⟨1-oddPolynomial a,by rw [map_sub,ha]⟩

/-- The residual of `1` is nonzero exactly when `1 ∉ V_L`; here the needed
direction. -/
theorem residual_ne_zero (μ : Measure Gap) [IsFiniteMeasure μ] (L : ℕ)
    (hnot : polynomialL2 μ 1 ∉ oddL2Span μ L) :
    polynomialL2 μ 1 - (oddL2Span μ L).starProjection (polynomialL2 μ 1) ≠ 0 := by
  intro hzero
  apply hnot
  rw [sub_eq_zero.mp hzero]
  exact (oddL2Span μ L).starProjection_apply_mem _

/-- Inner product against the class of a polynomial, as an integral of the
representative. -/
theorem inner_polynomialL2_right (μ : Measure Gap) [IsFiniteMeasure μ]
    (f : Lp ℝ 2 μ) (Q : ℝ[X]) :
    ⟪f, polynomialL2 μ Q⟫ = ∫ d, f d * Q.eval (d:ℝ) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [polynomialL2_ae μ Q] with d hQ
  simp only [hQ,Real.inner_apply]

/-- The squared L²(μ) norm as the integral of the square of the representative. -/
theorem norm_sq_eq_integral_sq (μ : Measure Gap) (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ d, (f d) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards with d
  simp only [Real.inner_apply,sq]

/-- The residual is orthogonal to every required odd monomial. -/
theorem residual_odd_moment (μ : Measure Gap) [IsFiniteMeasure μ] (L : ℕ) (j : Fin L) :
    ∫ d, (polynomialL2 μ 1 - (oddL2Span μ L).starProjection (polynomialL2 μ 1)) d *
      (d:ℝ) ^ (2*j.val+1) ∂μ = 0 := by
  have hj : polynomialL2 μ (X^(2*j.val+1)) ∈ oddL2Span μ L := Submodule.subset_span ⟨j,rfl⟩
  have ho := (oddL2Span μ L).starProjection_inner_eq_zero (polynomialL2 μ 1) _ hj
  rw [inner_polynomialL2_right] at ho
  simpa only [eval_pow,eval_X] using ho

/-- The integral of the residual equals its squared L²(μ) norm. -/
theorem residual_integral_eq_norm_sq (μ : Measure Gap) [IsFiniteMeasure μ] (L : ℕ) :
    ∫ d, (polynomialL2 μ 1 - (oddL2Span μ L).starProjection (polynomialL2 μ 1)) d ∂μ =
      ‖polynomialL2 μ 1 - (oddL2Span μ L).starProjection (polynomialL2 μ 1)‖ ^ 2 := by
  have hort := (oddL2Span μ L).starProjection_inner_eq_zero (polynomialL2 μ 1) _
    ((oddL2Span μ L).starProjection_apply_mem (polynomialL2 μ 1))
  rw [← real_inner_self_eq_norm_sq,inner_sub_right _ (polynomialL2 μ 1),hort,sub_zero,
    inner_polynomialL2_right]
  simp only [eval_one,mul_one]

/-- An L²(μ) class with a polynomial representative has finite `L^∞(μ)` norm. -/
theorem eLpNorm_top_ne_top_of_polynomial (μ : Measure Gap) [IsFiniteMeasure μ]
    (f : Lp ℝ 2 μ) (H : ℝ[X]) (hH : polynomialL2 μ H = f) : eLpNorm (⇑f) ∞ μ ≠ ∞ := by
  obtain ⟨K,hK⟩ := polynomial_gap_bound H
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  apply ne_of_lt
  apply eLpNormEssSup_lt_top_of_ae_bound (C := K)
  filter_upwards [hH ▸ polynomialL2_ae μ H] with d hd
  rw [hd]
  exact hK d

/-- A nonzero L²(μ) class has nonzero `L^∞(μ)` norm. -/
theorem eLpNorm_top_ne_zero (μ : Measure Gap) (f : Lp ℝ 2 μ) (hf : f ≠ 0) :
    eLpNorm (⇑f) ∞ μ ≠ 0 := by
  intro hz
  apply hf
  exact Lp.eq_zero_iff_ae_eq_zero.mpr ((eLpNorm_eq_zero_iff ENNReal.top_ne_zero).mp hz)

/-- Truncation of an almost-everywhere bounded L²(μ) class with a polynomial
representative: a measurable function bounded everywhere by the `L^∞(μ)` norm
and equal to the class almost everywhere. -/
theorem exists_bounded_representative (μ : Measure Gap) [IsFiniteMeasure μ]
    (f : Lp ℝ 2 μ) (H : ℝ[X]) (hH : polynomialL2 μ H = f) :
    ∃ g : Gap → ℝ, Measurable g ∧ (∀ d, |g d| ≤ (eLpNorm (⇑f) ∞ μ).toReal) ∧ g =ᵐ[μ] ⇑f := by
  set M := (eLpNorm (⇑f) ∞ μ).toReal
  have hfin := eLpNorm_top_ne_top_of_polynomial μ f H hH
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hae : (⇑f) =ᵐ[μ] fun d : Gap => H.eval (d:ℝ) := hH ▸ polynomialL2_ae μ H
  have hbound : ∀ᵐ d ∂μ, |f d| ≤ M := by
    filter_upwards [ae_le_eLpNormEssSup (μ := μ) (f := ⇑f)] with d hd
    rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] at hd
    have ht := ENNReal.toReal_mono hfin hd
    rwa [toReal_enorm,Real.norm_eq_abs] at ht
  let g : Gap → ℝ := fun d => max (-M) (min M (H.eval (d:ℝ)))
  have hHm : Measurable fun d : Gap => H.eval (d:ℝ) :=
    H.continuous.measurable.comp measurable_subtype_coe
  refine ⟨g,measurable_const.max (measurable_const.min hHm),?_,?_⟩
  · intro d
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  · filter_upwards [hae,hbound] with d hd hb
    rw [hd] at hb ⊢
    have hb' := abs_le.mp hb
    simp only [g,min_eq_right hb'.2,max_eq_right hb'.1]

/-- The explicit lower estimate, with every conclusion of
`ExplicitCapEstimateStatement` for the residual `h = 1 - proj_{V_L} 1`. -/
theorem explicit_cap_estimate_of_not_mem (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ)
    (hnot : polynomialL2 μ 1 ∉ oddL2Span μ ((N+1)/2)) :
    let h : Lp ℝ 2 μ := polynomialL2 μ 1 -
      (oddL2Span μ ((N+1)/2)).starProjection (polynomialL2 μ 1)
    h ≠ 0 ∧ eLpNorm (⇑h) ∞ μ ≠ ∞ ∧ 0 < (eLpNorm (⇑h) ∞ μ).toReal ∧
      (∀ j : Fin ((N+1)/2), ∫ d, h d * (d : ℝ) ^ (2*j.val+1) ∂μ = 0) ∧
      (∫ d, h d ∂μ) = ∫ d, (h d) ^ 2 ∂μ ∧
      0 < ∫ d, (h d) ^ 2 ∂μ ∧
      ‖h‖ ^ 2 = ∫ d, (h d) ^ 2 ∂μ ∧
      ρ * ‖h‖ ^ 2 / (4 * (eLpNorm (⇑h) ∞ μ).toReal) ≤ capDiameter μ ρ N / 2 := by
  intro h
  set M := (eLpNorm (⇑h) ∞ μ).toReal
  obtain ⟨H,hH⟩ := residual_polynomial μ ((N+1)/2)
  have hne : h ≠ 0 := residual_ne_zero μ _ hnot
  have hfin : eLpNorm (⇑h) ∞ μ ≠ ∞ := eLpNorm_top_ne_top_of_polynomial μ h H hH
  have hMpos : 0 < M := ENNReal.toReal_pos (eLpNorm_top_ne_zero μ h hne) hfin
  have hmom : ∀ j : Fin ((N+1)/2), ∫ d, h d * (d : ℝ) ^ (2*j.val+1) ∂μ = 0 :=
    residual_odd_moment μ _
  have hint : (∫ d, h d ∂μ) = ‖h‖ ^ 2 := residual_integral_eq_norm_sq μ _
  have hsq : ‖h‖ ^ 2 = ∫ d, (h d) ^ 2 ∂μ := norm_sq_eq_integral_sq μ h
  have hpos : 0 < ‖h‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  obtain ⟨g,hgm,hgb,hgae⟩ := exists_bounded_representative μ h H hH
  have hmom_g : ∀ j : Fin ((N+1)/2), ∫ d, g d * (d : ℝ) ^ (2*j.val+1) ∂μ = 0 := by
    intro j
    refine (integral_congr_ae ?_).trans (hmom j)
    filter_upwards [hgae] with d hd
    rw [hd]
  have hint_g : (∫ d, g d ∂μ) = ‖h‖ ^ 2 := by
    rw [← hint]
    exact integral_congr_ae hgae
  obtain ⟨qH,qL,hHr,hLr,hm,hgap,_⟩ :=
    rare_priors_of_bounded_contrast μ ρ hρ hρ1 N g hgm M hMpos hgb hmom_g (hint_g ▸ hpos)
  obtain ⟨_,_,_,_,_,_,hmax⟩ := capDiameter_attained μ hρ.le N
  have hle := hmax qH qL hHr hLr hm
  rw [hgap,hint_g] at hle
  have heq : ρ * ‖h‖ ^ 2 / (4 * M) = ρ / (2 * M) * ‖h‖ ^ 2 / 2 := by
    field_simp
    ring
  refine ⟨hne,hfin,hMpos,hmom,hint.trans hsq,hsq ▸ hpos,hsq,?_⟩
  rw [heq]
  linarith

/-- Non-vacuity of the hypothesis `1 ∉ V_L`: for every `L`, the uniform law on
the `L+1` gaps `1/2, 1/3, …, 1/(L+2)` satisfies it. -/
theorem exists_law_constant_not_mem (L : ℕ) :
    ∃ μ : ProbabilityMeasure Gap,
      polynomialL2 (μ : Measure Gap) 1 ∉ oddL2Span (μ : Measure Gap) L := by
  classical
  let pt : ℕ → Gap := fun i => ⟨1/((i:ℝ)+2),by positivity,by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]⟩
  have hinj : Function.Injective pt := by
    intro i k hik
    have h := congrArg Subtype.val hik
    simp only [pt,one_div,inv_inj] at h
    exact_mod_cast add_right_cancel h
  let ν : Measure Gap := ((L+1 : ℝ≥0∞)⁻¹) • ∑ i : Fin (L+1), Measure.dirac (pt i)
  have hν : IsProbabilityMeasure ν := by
    constructor
    simp only [ν,Measure.smul_apply,Measure.finsetSum_apply,measure_univ,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,smul_eq_mul]
    push_cast
    exact ENNReal.inv_mul_cancel (by positivity) (by simp)
  have hsupp (i : Fin (L+1)) : pt i ∈ ν.support := by
    rw [Measure.mem_support_iff_forall]
    intro U hU
    have hle : Measure.dirac (pt i) U ≤ ∑ k : Fin (L+1), Measure.dirac (pt k) U :=
      Finset.single_le_sum (f := fun k : Fin (L+1) => Measure.dirac (pt k) U)
        (fun _ _ => zero_le) (Finset.mem_univ i)
    rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)] at hle
    simp only [ν,Measure.smul_apply,Measure.finsetSum_apply,smul_eq_mul]
    exact ENNReal.mul_pos (by simp) (ne_of_gt (lt_of_lt_of_le zero_lt_one hle))
  have hS : ((Finset.univ.image fun i : Fin (L+1) => pt i : Finset Gap) : Set Gap) ⊆
      ν.support := by
    intro d hd
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
    exact hsupp i
  have hcard : L < (Finset.univ.image fun i : Fin (L+1) => pt i).card := by
    rw [Finset.card_image_of_injective _ (fun i k h => Fin.val_injective (hinj h))]
    simp
  have hnot : polynomialL2 ν 1 ∉ oddL2Span ν L := constant_not_in_oddL2Span ν L _ hS hcard
  exact ⟨⟨ν,hν⟩,hnot⟩

end ThresholdHC.CapIdentificationEstimate
