import ThresholdHC.CapIdentification.CenteredBasis
import ThresholdHC.StoppingProgram.FlowBasics

/-! Integration of sign contrasts gives a linear functional on likelihood
polynomials. Every integrability obligation is discharged on the bounded
probability interval; no moment assumption on the gap law is used. -/

noncomputable section
open Polynomial MeasureTheory Set
open scoped BigOperators

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.StoppingProgram

theorem integrable_polynomial_probability (μ : Measure Gap) [IsFiniteMeasure μ]
    (p : Gap → ℝ) (hp : Measurable p) (hr : ∀ d, p d ∈ Icc (0:ℝ) 1) (P : ℝ[X]) :
    Integrable (fun d => P.eval (p d)) μ := by
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image P.continuous.norm.continuousOn
  exact Integrable.of_bound (P.continuous.measurable.comp hp).aestronglyMeasurable M
    (Filter.Eventually.of_forall (fun d => hM (mem_image_of_mem _ (hr d))))

def weightedPolynomialIntegral (μ : Measure Gap) [IsFiniteMeasure μ]
    (g p : Gap → ℝ) (hg : Measurable g) (hp : Measurable p)
    (hb : ∀ d, ‖g d‖ ≤ 1) (hr : ∀ d, p d ∈ Icc (0:ℝ) 1) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun P := ∫ d, g d*P.eval (p d) ∂μ
  map_add' P Q := by
    simp only [eval_add,mul_add]
    exact integral_add
      ((integrable_polynomial_probability μ p hp hr P).bdd_mul hg.aestronglyMeasurable
        (Filter.Eventually.of_forall hb))
      ((integrable_polynomial_probability μ p hp hr Q).bdd_mul hg.aestronglyMeasurable
        (Filter.Eventually.of_forall hb))
  map_smul' a P := by
    simp only [eval_smul,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_left_comm (g _) a]
    exact integral_const_mul _ _

theorem signDifference_norm (qH qL : SignLaw) (d : Gap) : ‖qH.val d-qL.val d‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [(qH.property.2 d).1,(qL.property.2 d).2],
    by linarith [(qL.property.2 d).1,(qH.property.2 d).2]⟩

def signContrast (μ : Measure Gap) [IsFiniteMeasure μ] (qH qL : SignLaw) : ℝ[X] →ₗ[ℝ] ℝ :=
  weightedPolynomialIntegral μ (fun d => qH.val d-qL.val d) (fun d => 1/2+(d:ℝ))
    (qH.property.1.sub qL.property.1) (by fun_prop)
    (signDifference_norm qH qL)
    (fun d => ⟨by linarith [d.property.1],by linarith [d.property.2]⟩) -
  weightedPolynomialIntegral μ (fun d => qH.val d-qL.val d) (fun d => 1/2-(d:ℝ))
    (qH.property.1.sub qL.property.1) (by fun_prop)
    (signDifference_norm qH qL)
    (fun d => ⟨by linarith [d.property.2],by linarith [d.property.1]⟩)

theorem signContrast_apply (μ : Measure Gap) [IsFiniteMeasure μ] (qH qL : SignLaw) (P : ℝ[X]) :
    signContrast μ qH qL P =
      (∫ d, (qH.val d-qL.val d)*P.eval (1/2+(d:ℝ)) ∂μ)-
      (∫ d, (qH.val d-qL.val d)*P.eval (1/2-(d:ℝ)) ∂μ) := rfl

theorem centeredPower_eval_plus (k : ℕ) (d : ℝ) :
    (centeredPower (1/2) k).eval (1/2+d) = d^k := by
  simp [centeredPower]

theorem centeredPower_eval_minus (k : ℕ) (d : ℝ) :
    (centeredPower (1/2) k).eval (1/2-d) = (-d)^k := by
  simp only [centeredPower,eval_pow,eval_sub,eval_X,eval_C]
  congr 1
  ring

theorem signContrast_even (μ : Measure Gap) [IsFiniteMeasure μ] (qH qL : SignLaw)
    {k : ℕ} (hk : Even k) : signContrast μ qH qL (centeredPower (1/2) k) = 0 := by
  simp only [signContrast_apply,centeredPower_eval_plus,centeredPower_eval_minus,hk.neg_pow,sub_self]

theorem signContrast_odd (μ : Measure Gap) [IsFiniteMeasure μ] (qH qL : SignLaw) (j : ℕ) :
    signContrast μ qH qL (centeredPower (1/2) (2*j+1)) =
      2*∫ d, (qH.val d-qL.val d)*(d:ℝ)^(2*j+1) ∂μ := by
  have ho : Odd (2*j+1) := ⟨j,rfl⟩
  simp only [signContrast_apply,centeredPower_eval_plus,centeredPower_eval_minus,ho.neg_pow,
    mul_neg,integral_neg,sub_neg_eq_add]
  ring

theorem odd_moments_iff_prefix_contrast (μ : Measure Gap) [IsFiniteMeasure μ]
    (qH qL : SignLaw) (N : ℕ) :
    (∀ j : Fin ((N+1)/2), ∫ d, (qH.val d-qL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0) ↔
      ∀ k, k ≤ N → signContrast μ qH qL (prefixPolynomial N k) = 0 := by
  have he := odd_centered_prefix_equivalence (signContrast μ qH qL) N (1/2)
    (fun k _ hk => signContrast_even μ qH qL hk)
  simpa only [signContrast_odd,mul_eq_zero,show (2:ℝ) ≠ 0 by norm_num,false_or] using he

end ThresholdHC.CapIdentification
