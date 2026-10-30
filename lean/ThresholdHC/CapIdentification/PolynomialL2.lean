import ThresholdHC.CapIdentification.ContrastFunctional
import ThresholdHC.CapIdentification.OddPolynomials

/-! Bounded polynomials on the gap interval as actual L2 random variables,
and their finite-dimensional odd-moment span. -/

noncomputable section
open MeasureTheory Polynomial Set
open scoped BigOperators RealInnerProductSpace

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap)

theorem polynomial_gap_bound (P : ℝ[X]) : ∃ M : ℝ, ∀ d : Gap, ‖P.eval (d:ℝ)‖ ≤ M := by
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).bddAbove_image P.continuous.norm.continuousOn
  refine ⟨M,fun d => hM (mem_image_of_mem _ ?_)⟩
  exact ⟨d.property.1.le,by linarith [d.property.2]⟩

theorem polynomial_gap_memLp (μ : Measure Gap) [IsFiniteMeasure μ] (P : ℝ[X]) :
    MemLp (fun d : Gap => P.eval (d:ℝ)) 2 μ := by
  obtain ⟨M,hM⟩ := polynomial_gap_bound P
  exact MemLp.of_bound (P.continuous.measurable.comp measurable_subtype_coe).aestronglyMeasurable M
    (Filter.Eventually.of_forall hM)

def polynomialL2 (μ : Measure Gap) [IsFiniteMeasure μ] : ℝ[X] →ₗ[ℝ] Lp ℝ 2 μ where
  toFun P := (polynomial_gap_memLp μ P).toLp (fun d : Gap => P.eval (d:ℝ))
  map_add' P Q := by
    apply Lp.ext
    filter_upwards [(polynomial_gap_memLp μ (P+Q)).coeFn_toLp,
      Lp.coeFn_add ((polynomial_gap_memLp μ P).toLp _) ((polynomial_gap_memLp μ Q).toLp _),
      (polynomial_gap_memLp μ P).coeFn_toLp,(polynomial_gap_memLp μ Q).coeFn_toLp] with d hsum hadd hP hQ
    rw [hsum,hadd]
    simp only [Pi.add_apply,hP,hQ,eval_add]
  map_smul' a P := by
    apply Lp.ext
    filter_upwards [(polynomial_gap_memLp μ (a • P)).coeFn_toLp,
      Lp.coeFn_smul a ((polynomial_gap_memLp μ P).toLp _),
      (polynomial_gap_memLp μ P).coeFn_toLp] with d hsmul hmul hP
    rw [hsmul,RingHom.id_apply,hmul]
    simp only [Pi.smul_apply,hP,eval_smul]

theorem polynomialL2_ae (μ : Measure Gap) [IsFiniteMeasure μ] (P : ℝ[X]) :
    polynomialL2 μ P =ᵐ[μ] (fun d : Gap => P.eval (d:ℝ)) :=
  (polynomial_gap_memLp μ P).coeFn_toLp

theorem polynomialL2_inner (μ : Measure Gap) [IsFiniteMeasure μ] (P Q : ℝ[X]) :
    inner ℝ (polynomialL2 μ P) (polynomialL2 μ Q) = ∫ d : Gap, P.eval (d:ℝ)*Q.eval (d:ℝ) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [polynomialL2_ae μ P,polynomialL2_ae μ Q] with d hP hQ
  simp only [hP,hQ,Real.inner_apply]

def oddL2Span (μ : Measure Gap) [IsFiniteMeasure μ] (L : ℕ) : Submodule ℝ (Lp ℝ 2 μ) :=
  Submodule.span ℝ (range (fun j : Fin L => polynomialL2 μ (X^(2*j.val+1))))

instance oddL2Span_finite (μ : Measure Gap) [IsFiniteMeasure μ] (L : ℕ) :
    FiniteDimensional ℝ (oddL2Span μ L) :=
  FiniteDimensional.span_of_finite ℝ (finite_range _)

theorem polynomialL2_odd (μ : Measure Gap) [IsFiniteMeasure μ] {L : ℕ} (a : Fin L → ℝ) :
    polynomialL2 μ (oddPolynomial a) = ∑ j : Fin L, a j • polynomialL2 μ (X^(2*j.val+1)) := by
  simp only [oddPolynomial,C_mul',map_sum,map_smul]

theorem mem_oddL2Span (μ : Measure Gap) [IsFiniteMeasure μ] {L : ℕ} (v : Lp ℝ 2 μ) :
    v ∈ oddL2Span μ L ↔ ∃ a : Fin L → ℝ, polynomialL2 μ (oddPolynomial a) = v := by
  simp only [polynomialL2_odd,oddL2Span,Submodule.mem_span_range_iff_exists_fun ℝ]

end ThresholdHC.CapIdentification
