import ThresholdHC.StoppingProgram.RarityTheorem
import ThresholdHC.StoppingProgram.MomentImage

/-! Elimination of robust prior constraints by four scalar rarity cutoffs.
The signed integrands are actual count-likelihood polynomials. -/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators ENNReal

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo ThresholdHC.CapIdentification

def countMeanPolynomial {N : ℕ} (u : CountState N → ℝ) : ℝ[X] :=
  ∑ s, u s • countContrastPolynomial s

theorem countMeanPolynomial_eval {N : ℕ} (u : CountState N → ℝ) (d : Gap) :
    (countMeanPolynomial u).eval (d:ℝ) = ∑ s, u s*(countContrastPolynomial s).eval (d:ℝ) := by
  simp [countMeanPolynomial,eval_finsetSum,smul_eq_mul]

theorem countMean_affine {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (u : CountState N → ℝ) :
    countMean μ q u = countMean μ nullSignLaw u+
      ∫ d, q.val d*(countMeanPolynomial u).eval (d:ℝ) ∂μ := by
  have hi (s : CountState N) : Integrable (fun d : Gap => q.val d*(countContrastPolynomial s).eval (d:ℝ)) μ :=
    integrable_prior_function μ q ((polynomial_gap_memLp μ _).integrable (by norm_num))
  have he : (∫ d, q.val d*(countMeanPolynomial u).eval (d:ℝ) ∂μ) =
      ∑ s, u s*(∫ d, q.val d*(countContrastPolynomial s).eval (d:ℝ) ∂μ) := by
    simp only [countMeanPolynomial_eval]
    simp_rw [Finset.mul_sum,show ∀ s d, q.val d*(u s*(countContrastPolynomial s).eval (d:ℝ)) =
      u s*(q.val d*(countContrastPolynomial s).eval (d:ℝ)) by intros; ring]
    rw [integral_finsetSum _ (fun s _ => (hi s).const_mul (u s))]
    simp only [integral_const_mul]
  rw [he]
  unfold countMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [countCoefficient_affine μ q s]
  ring

theorem robust_polynomial_bound_iff (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (P : ℝ[X]) (b z : ℝ) :
    (∀ q : SignLaw, RarePrior μ ρ q → b+(∫ d, q.val d*P.eval (d:ℝ) ∂μ) ≤ z) ↔
      ∃ ell : ℝ, 0 ≤ ell ∧ b+ρ*ell+(∫ d, max (P.eval (d:ℝ)-ell) 0 ∂μ) ≤ z := by
  obtain ⟨M,hM⟩ := polynomial_gap_bound P
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ⟨1/2,by norm_num,by norm_num⟩)
  have hf : Measurable (fun d : Gap => P.eval (d:ℝ)) := P.continuous.measurable.comp measurable_subtype_coe
  obtain ⟨ell,c,hell,_,hc,hq,hqe,he,hmin,_⟩ := fractional_rarity_support μ hρ hM0 _ hf hM
  constructor
  · intro h
    refine ⟨ell,hell,?_⟩
    have hbound := h (fractionalUpperPrior _ hf ell c hc) hq
    rw [← hqe,he] at hbound
    linarith
  · rintro ⟨t,ht,hbound⟩ q hq'
    have hi := (polynomial_gap_memLp μ P).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
    have hle := prior_function_upper_tail μ _ hi q hq' ht
    linarith

def biasPolynomial {N : ℕ} (C : Certificate N) : ℝ[X] := countMeanPolynomial C.flow.outputWeight-1

theorem certificate_bias_affine {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (C : Certificate N) (q : SignLaw) :
    C.offset+countMean μ q C.flow.outputWeight-signMean μ q.val =
      C.offset+countMean μ nullSignLaw C.flow.outputWeight+
        ∫ d, q.val d*(biasPolynomial C).eval (d:ℝ) ∂μ := by
  rw [countMean_affine]
  have hi := integrable_prior_function μ q
    ((polynomial_gap_memLp μ (countMeanPolynomial C.flow.outputWeight)).integrable (by norm_num))
  have he : (∫ d, q.val d*(biasPolynomial C).eval (d:ℝ) ∂μ) =
      (∫ d, q.val d*(countMeanPolynomial C.flow.outputWeight).eval (d:ℝ) ∂μ)-signMean μ q.val := by
    simp only [biasPolynomial,eval_sub,eval_one,mul_sub,mul_one]
    exact integral_sub hi (integrable_sign_prior μ q)
  rw [he]
  ring

def polynomialTail (μ : Measure Gap) (ρ : ℝ) (P : ℝ[X]) (ell : ℝ) : ℝ :=
  ρ*ell+∫ d : Gap, max (P.eval (d:ℝ)-ell) 0 ∂μ

theorem feasible_iff_four_cutoffs {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (C : Certificate N) :
    Feasible μ ρ B C ↔ FlowCone C.flow ∧ 0 ≤ C.bias ∧ 0 ≤ C.variance ∧
      ∃ ell : Fin 4 → ℝ, (∀ i, 0 ≤ ell i) ∧
        C.offset+countMean μ nullSignLaw C.flow.outputWeight+
          polynomialTail μ ρ (biasPolynomial C) (ell 0) ≤ C.bias ∧
        -(C.offset+countMean μ nullSignLaw C.flow.outputWeight)+
          polynomialTail μ ρ (-biasPolynomial C) (ell 1) ≤ C.bias ∧
        countMean μ nullSignLaw C.flow.momentWeight+
          polynomialTail μ ρ (countMeanPolynomial C.flow.momentWeight) (ell 2) ≤ C.variance ∧
        countMean μ nullSignLaw C.flow.continueWeight+
          polynomialTail μ ρ (countMeanPolynomial C.flow.continueWeight) (ell 3) ≤ B := by
  have hneg (q : SignLaw) : (∫ d, q.val d*(-biasPolynomial C).eval (d:ℝ) ∂μ) =
      -(∫ d, q.val d*(biasPolynomial C).eval (d:ℝ) ∂μ) := by
    simp only [eval_neg,mul_neg,integral_neg]
  have hb : (∀ q : SignLaw, RarePrior μ ρ q →
      |C.offset+countMean μ q C.flow.outputWeight-signMean μ q.val| ≤ C.bias) ↔
      (∃ t, 0 ≤ t ∧ C.offset+countMean μ nullSignLaw C.flow.outputWeight+
        polynomialTail μ ρ (biasPolynomial C) t ≤ C.bias) ∧
      (∃ t, 0 ≤ t ∧ -(C.offset+countMean μ nullSignLaw C.flow.outputWeight)+
        polynomialTail μ ρ (-biasPolynomial C) t ≤ C.bias) := by
    simp only [polynomialTail,← add_assoc,← robust_polynomial_bound_iff μ hρ]
    simp only [certificate_bias_affine,abs_le,hneg,neg_add_rev]
    constructor
    · intro h
      exact ⟨fun q hq => (h q hq).2,fun q hq => by linarith [(h q hq).1]⟩
    · rintro ⟨h1,h2⟩ q hq
      exact ⟨by linarith [h2 q hq],h1 q hq⟩
  have hw (u : CountState N → ℝ) (z : ℝ) :
      (∀ q : SignLaw, RarePrior μ ρ q → countMean μ q u ≤ z) ↔
      ∃ t, 0 ≤ t ∧ countMean μ nullSignLaw u+polynomialTail μ ρ (countMeanPolynomial u) t ≤ z := by
    have he : (∀ q : SignLaw, RarePrior μ ρ q → countMean μ q u ≤ z) ↔
        (∀ q : SignLaw, RarePrior μ ρ q → countMean μ nullSignLaw u+
          (∫ d, q.val d*(countMeanPolynomial u).eval (d:ℝ) ∂μ) ≤ z) := by
      apply forall_congr'
      intro q
      rw [countMean_affine μ q u]
    exact he.trans (by simpa only [polynomialTail,← add_assoc] using
      robust_polynomial_bound_iff μ hρ (countMeanPolynomial u) (countMean μ nullSignLaw u) z)
  constructor
  · intro h
    obtain ⟨⟨t0,h0,ht0⟩,⟨t1,h1,ht1⟩⟩ := hb.mp h.bias_bound
    obtain ⟨t2,h2,ht2⟩ := (hw _ _).mp h.variance_bound
    obtain ⟨t3,h3,ht3⟩ := (hw _ _).mp h.work_bound
    refine ⟨h.cone,h.bias_nonneg,h.variance_nonneg,![t0,t1,t2,t3],?_,ht0,ht1,ht2,ht3⟩
    intro i
    fin_cases i <;> assumption
  · rintro ⟨hf,hb0,hv0,t,ht,ht0,ht1,ht2,ht3⟩
    exact ⟨hf,hb0,hv0,hb.mpr ⟨⟨t 0,ht 0,ht0⟩,⟨t 1,ht 1,ht1⟩⟩,
      (hw _ _).mpr ⟨t 2,ht 2,ht2⟩,(hw _ _).mpr ⟨t 3,ht 3,ht3⟩⟩

end ThresholdHC.StoppingProgram
