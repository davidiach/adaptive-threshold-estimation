import ThresholdHC.EntropyTailLower.ComponentPriors

/-! Normalized restrictions, attained prior optimizers, and actual feasible
component certificates with additive weighted budgets. -/

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Polynomial Real ProbabilityTheory
open scoped BigOperators ENNReal
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.CapIdentification

theorem component_integral_rescale (μ : Measure Gap) [IsFiniteMeasure μ]
    (S : Set Gap) (hS : μ S ≠ 0) (f : Gap → ℝ) :
    μ.real S * (∫ d, f d ∂ProbabilityTheory.cond μ S) = ∫ d in S, f d ∂μ := by
  rw [ProbabilityTheory.cond,integral_smul_measure,smul_eq_mul,ENNReal.toReal_inv]
  have hm : μ.real S ≠ 0 := (ENNReal.toReal_pos hS (measure_ne_top μ S)).ne'
  change μ.real S * ((μ.real S)⁻¹ * _) = _
  rw [← mul_assoc,mul_inv_cancel₀ hm,one_mul]

theorem component_countMean_rescale {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (S : Set Gap) (hS : μ S ≠ 0) (q : SignLaw) (u : CountState N → ℝ) :
    μ.real S * countMean (ProbabilityTheory.cond μ S) q u = countMean (μ.restrict S) q u := by
  unfold countMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold countCoefficient
  have he := component_integral_rescale μ S hS
    (fun d => q.val d*prefixLikelihood true s.1.val s.2.val d+
      (1-q.val d)*prefixLikelihood false s.1.val s.2.val d)
  calc
    _ = (s.1.val.choose s.2.val:ℝ) * (μ.real S * (∫ d,
      q.val d*prefixLikelihood true s.1.val s.2.val d+
      (1-q.val d)*prefixLikelihood false s.1.val s.2.val d ∂ProbabilityTheory.cond μ S)) * u s := by ring
    _ = _ := by rw [he]

theorem polynomial_abs_prior_maximizer (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (hρ : 0 ≤ ρ) (P : ℝ[X]) :
    ∃ q : SignLaw, RarePrior μ ρ q ∧ ∀ r : SignLaw, RarePrior μ ρ r →
      |∫ d, r.val d * P.eval (d:ℝ) ∂μ| ≤ |∫ d, q.val d * P.eval (d:ℝ) ∂μ| := by
  let f : Unit → Gap → ℝ := fun _ d => P.eval (d:ℝ)
  let K := functionMomentImage μ ρ f (fun _ => 0)
  have hc : IsCompact K := (functionMomentImage_compact_convex μ ρ f (fun _ => 0)
    (fun _ => polynomial_gap_memLp μ P)).1
  obtain ⟨u,⟨q,hq,he⟩,hmax⟩ := hc.exists_isMaxOn
    (functionMomentImage_nonempty μ hρ f (fun _ => 0))
    ((continuous_apply ()).abs.continuousOn)
  refine ⟨q,hq,?_⟩
  intro r hr
  have hh := hmax (show (fun _ : Unit => ∫ d, r.val d*P.eval (d:ℝ) ∂μ) ∈ K from
    ⟨r,hr,fun _ => by simp [f]⟩)
  change |∫ d, r.val d*P.eval (d:ℝ) ∂μ| ≤ |u ()| at hh
  simpa only [he (),f,add_zero] using hh

theorem countMean_prior_maximizer {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (hρ : 0 ≤ ρ) (u : CountState N → ℝ) :
    ∃ q : SignLaw, RarePrior μ ρ q ∧ ∀ r : SignLaw, RarePrior μ ρ r →
      countMean μ r u ≤ countMean μ q u := by
  let P := countMeanPolynomial u
  obtain ⟨q,hq,he⟩ := rareFunctional_attained μ hρ (fun d => P.eval (d:ℝ))
    (polynomial_gap_memLp μ P)
  refine ⟨q,hq,?_⟩
  intro r hr
  rw [countMean_affine μ r u,countMean_affine μ q u]
  exact add_le_add le_rfl
    ((prior_function_le_rareFunctional μ _ (polynomial_gap_memLp μ P) r hr).trans_eq he)

theorem component_certificate_optimizers {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (hρ : 0 ≤ ρ) (C : Certificate N) (hC : FlowCone C.flow) :
    ∃ (D : Certificate N) (w : ℝ) (qB qV qW : SignLaw),
      D.flow = C.flow ∧ Feasible μ ρ w D ∧ 0 ≤ w ∧
      RarePrior μ ρ qB ∧ RarePrior μ ρ qV ∧ RarePrior μ ρ qW ∧
      D.bias = |∫ d, qB.val d*(biasPolynomial C).eval (d:ℝ) ∂μ| ∧
      D.variance = countMean μ qV C.flow.momentWeight ∧
      w = countMean μ qW C.flow.continueWeight := by
  obtain ⟨qB,hB,hBmax⟩ := polynomial_abs_prior_maximizer μ ρ hρ (biasPolynomial C)
  obtain ⟨qV,hV,hVmax⟩ := countMean_prior_maximizer μ ρ hρ C.flow.momentWeight
  obtain ⟨qW,hW,hWmax⟩ := countMean_prior_maximizer μ ρ hρ C.flow.continueWeight
  let D : Certificate N := ⟨C.flow,-countMean μ nullSignLaw C.flow.outputWeight,
    |∫ d, qB.val d*(biasPolynomial C).eval (d:ℝ) ∂μ|,countMean μ qV C.flow.momentWeight⟩
  let w := countMean μ qW C.flow.continueWeight
  refine ⟨D,w,qB,qV,qW,rfl,?_,countMean_nonneg μ qW _ hC.continue_nonneg,
    hB,hV,hW,rfl,rfl,rfl⟩
  refine ⟨hC,abs_nonneg _,countMean_nonneg μ qV _ hC.moment_nonneg,?_,hVmax,hWmax⟩
  intro q hq
  rw [certificate_bias_affine]
  change |-countMean μ nullSignLaw C.flow.outputWeight + countMean μ nullSignLaw C.flow.outputWeight +
    (∫ d, q.val d*(biasPolynomial C).eval (d:ℝ) ∂μ)| ≤ _
  rw [neg_add_cancel,zero_add]
  exact hBmax q hq

theorem certificate_component_localization {I : Type} [Fintype I] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (S : I → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hm : ∀ i, μ (S i) ≠ 0)
    (r : I → ℝ) (hr : ∀ i, 0 ≤ r i) (hρ : ∑ i, μ.real (S i)*r i ≤ ρ) :
    ∃ (D : I → Certificate N) (w : I → ℝ),
      (∀ i, (D i).flow = C.flow ∧ 0 ≤ w i ∧ Feasible (ProbabilityTheory.cond μ (S i)) (r i) (w i) (D i)) ∧
      (∑ i, μ.real (S i)*(D i).bias) ≤ 2*C.bias ∧
      (∑ i, μ.real (S i)*(D i).variance) ≤ C.variance ∧
      (∑ i, μ.real (S i)*w i) ≤ B := by
  classical
  let (i : I) : IsProbabilityMeasure (ProbabilityTheory.cond μ (S i)) := cond_isProbabilityMeasure (hm i)
  choose D w qB qV qW hflow hfeas hw hB hV hW hb hv hwork using
    fun i => component_certificate_optimizers (ProbabilityTheory.cond μ (S i)) (r i) (hr i) C hC.cone
  have hmass (i : I) : 0 ≤ μ.real (S i) := ENNReal.toReal_nonneg
  have hbudget (q : I → SignLaw) (hq : ∀ i, RarePrior (ProbabilityTheory.cond μ (S i)) (r i) (q i)) :
      (∑ i, ∫ d in S i, (q i).val d ∂μ) ≤ ρ := by
    calc
      _ = ∑ i, μ.real (S i)*signMean (ProbabilityTheory.cond μ (S i)) (q i).val := by
        apply Finset.sum_congr rfl
        intro i _
        exact (component_integral_rescale μ (S i) (hm i) (q i).val).symm
      _ ≤ ∑ i, μ.real (S i)*r i := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hq i) (hmass i))
      _ ≤ ρ := hρ
  refine ⟨D,w,fun i => ⟨hflow i,hw i,hfeas i⟩,?_,?_,?_⟩
  · have he : (∑ i, μ.real (S i)*(D i).bias) =
        ∑ i, |∫ d in S i, (qB i).val d*(biasPolynomial C).eval (d:ℝ) ∂μ| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hb i, ← component_integral_rescale μ (S i) (hm i)
        (fun d => (qB i).val d*(biasPolynomial C).eval (d:ℝ)),abs_mul,abs_of_nonneg (hmass i)]
    rw [he]
    exact certificate_disjoint_component_bias_budget μ ρ B C hC S hS hd qB (hbudget qB hB)
  · have he : (∑ i, μ.real (S i)*(D i).variance) =
        ∑ i, countMean (μ.restrict (S i)) (qV i) C.flow.momentWeight := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hv i,component_countMean_rescale μ (S i) (hm i)]
    rw [he]
    exact certificate_disjoint_component_moment_budget μ ρ B C hC S hS hd qV (hbudget qV hV)
  · have he : (∑ i, μ.real (S i)*w i) =
        ∑ i, countMean (μ.restrict (S i)) (qW i) C.flow.continueWeight := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hwork i,component_countMean_rescale μ (S i) (hm i)]
    rw [he]
    exact certificate_disjoint_component_work_budget μ ρ B C hC S hS hd qW (hbudget qW hW)

end ThresholdHC.EntropyTailLower
