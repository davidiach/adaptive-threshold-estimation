import ThresholdHC.CapIdentification.ContrastFunctional

/-! Exact equivalence between cap-N count-likelihood matching and the first
ceiling(N/2) odd gap moments, for arbitrary finite gap measures. -/

noncomputable section
open Polynomial MeasureTheory Set
open scoped BigOperators

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.StoppingProgram

theorem prefixPolynomial_eval_plus (n k : ℕ) (d : Gap) :
    (prefixPolynomial n k).eval (1/2+(d:ℝ)) = prefixLikelihood true n k d := by
  simp only [prefixPolynomial,eval_mul,eval_pow,eval_X,eval_sub,eval_one,
    prefixLikelihood,ite_true]
  congr 2
  ring

theorem prefixPolynomial_eval_minus (n k : ℕ) (d : Gap) :
    (prefixPolynomial n k).eval (1/2-(d:ℝ)) = prefixLikelihood false n k d := by
  simp only [prefixPolynomial,eval_mul,eval_pow,eval_X,eval_sub,eval_one,
    prefixLikelihood,Bool.false_eq_true,ite_false]
  congr 2
  ring

theorem integrable_prefixLikelihood (μ : Measure Gap) [IsFiniteMeasure μ] (s : Bool) (n k : ℕ) :
    Integrable (prefixLikelihood s n k) μ := by
  cases s
  · simpa only [prefixPolynomial_eval_minus] using
      integrable_polynomial_probability μ (fun d => 1/2-(d:ℝ)) (by fun_prop)
        (fun d => ⟨by linarith [d.property.2],by linarith [d.property.1]⟩) (prefixPolynomial n k)
  · simpa only [prefixPolynomial_eval_plus] using
      integrable_polynomial_probability μ (fun d => 1/2+(d:ℝ)) (by fun_prop)
        (fun d => ⟨by linarith [d.property.1],by linarith [d.property.2]⟩) (prefixPolynomial n k)

theorem integrable_weighted_prefix (μ : Measure Gap) [IsFiniteMeasure μ] (q : SignLaw)
    (s : Bool) (n k : ℕ) : Integrable (fun d => q.val d*prefixLikelihood s n k d) μ := by
  apply (integrable_prefixLikelihood μ s n k).bdd_mul q.property.1.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun d => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (q.property.2 d).1] using (q.property.2 d).2)

theorem countCoefficient_difference {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (qH qL : SignLaw) (s : CountState N) :
    countCoefficient μ qH s-countCoefficient μ qL s =
      (s.1.val.choose s.2.val:ℝ)*signContrast μ qH qL (prefixPolynomial s.1.val s.2.val) := by
  have integrable_mix (q : SignLaw) : Integrable (fun d =>
      q.val d*prefixLikelihood true s.1.val s.2.val d+
      (1-q.val d)*prefixLikelihood false s.1.val s.2.val d) μ := by
    convert (integrable_weighted_prefix μ q true s.1.val s.2.val).add
      ((integrable_prefixLikelihood μ false s.1.val s.2.val).sub
        (integrable_weighted_prefix μ q false s.1.val s.2.val)) using 1
    ext d
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  have integrable_diff (b : Bool) : Integrable (fun d =>
      (qH.val d-qL.val d)*prefixLikelihood b s.1.val s.2.val d) μ := by
    convert (integrable_weighted_prefix μ qH b s.1.val s.2.val).sub
      (integrable_weighted_prefix μ qL b s.1.val s.2.val) using 1
    ext d
    simp only [Pi.sub_apply]
    ring
  rw [countCoefficient,countCoefficient,← mul_sub,signContrast_apply]
  simp only [prefixPolynomial_eval_plus,prefixPolynomial_eval_minus]
  rw [← integral_sub (integrable_mix qH) (integrable_mix qL),
    ← integral_sub (integrable_diff true) (integrable_diff false)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun d => by ring)

theorem countCoefficient_eq_iff_contrast {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (qH qL : SignLaw) (s : CountState N) :
    countCoefficient μ qH s = countCoefficient μ qL s ↔
      signContrast μ qH qL (prefixPolynomial s.1.val s.2.val) = 0 := by
  have hc : (s.1.val.choose s.2.val:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by have hk := s.2.isLt; omega)))
  rw [← sub_eq_zero,countCoefficient_difference,mul_eq_zero]
  simp only [hc,false_or]

def OddMomentMatch (μ : Measure Gap) (qH qL : SignLaw) (N : ℕ) : Prop :=
  ∀ j : Fin ((N+1)/2), ∫ d, (qH.val d-qL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0

def CountMatch (μ : Measure Gap) (qH qL : SignLaw) (N : ℕ) : Prop :=
  ∀ s : CountState N, countCoefficient μ qH s = countCoefficient μ qL s

theorem odd_moments_iff_count_match (μ : Measure Gap) [IsFiniteMeasure μ]
    (qH qL : SignLaw) (N : ℕ) : OddMomentMatch μ qH qL N ↔ CountMatch μ qH qL N := by
  rw [OddMomentMatch,odd_moments_iff_prefix_contrast]
  constructor
  · intro h s
    apply (countCoefficient_eq_iff_contrast μ qH qL s).mpr
    exact annihilates_prefixes_below _ N h s.1.val (by have hn := s.1.isLt; omega)
      s.2.val (by have hk := s.2.isLt; omega)
  · intro h k hk
    exact (countCoefficient_eq_iff_contrast μ qH qL
      ⟨⟨N,by omega⟩,⟨k,by change k < N+1; omega⟩⟩).mp (h _)

theorem countMean_eq_of_count_match {N : ℕ} (μ : Measure Gap) (qH qL : SignLaw)
    (h : CountMatch μ qH qL N) (u : CountState N → ℝ) : countMean μ qH u = countMean μ qL u := by
  unfold CountMatch at h
  simp only [countMean,h]

end ThresholdHC.CapIdentification
