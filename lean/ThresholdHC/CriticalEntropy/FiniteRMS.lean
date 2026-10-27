import ThresholdHC.CriticalEntropy.FiniteCentering
import ThresholdHC.CriticalEntropy.ExponentialRisk

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem finite_function_memLp {I : Type} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (μ : Measure I) [IsFiniteMeasure μ] (f : I → ℝ) :
    MemLp f 2 μ := by
  apply MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable (∑ i, ‖f i‖)
  exact ae_of_all μ (fun i => Finset.single_le_sum (fun j hj => norm_nonneg (f j)) (Finset.mem_univ i))

theorem finite_function_integrable {I : Type} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (μ : Measure I) [IsFiniteMeasure μ] (f : I → ℝ) :
    Integrable f μ := (finite_function_memLp μ f).integrable (by norm_num)

theorem finite_integral_exp {I : Type} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (μ : Measure I) [IsFiniteMeasure μ] (u : I → ℝ) :
    (∫ i, Real.exp (u i) ∂μ) = finitePartition (fun i => μ.real {i}) u := by
  rw [integral_fintype (finite_function_integrable μ _)]
  rfl

theorem finite_iid_exponential {I : Type} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (μ : Measure I) [IsProbabilityMeasure μ]
    (n : ℕ) (u : I → ℝ) (c θ a : ℝ) :
    (∫ x : Fin n → I, Real.exp ((c+(∑ i, u (x i))-θ)/a) ∂Measure.pi (fun _ : Fin n => μ)) =
      Real.exp ((c-θ)/a)*(finitePartition (fun i => μ.real {i}) (fun i => u i/a))^n := by
  have he : (fun x : Fin n → I => Real.exp ((c+(∑ i, u (x i))-θ)/a)) =
      (fun x => Real.exp ((c-θ)/a)*∏ i, Real.exp (u (x i)/a)) := by
    funext x
    rw [← Real.exp_sum,← Real.exp_add]
    congr 1
    rw [← Finset.sum_div]
    ring
  rw [he,integral_const_mul,
    integral_fintype_prod_eq_pow (ι := Fin n) (μ := μ) (fun i : I => Real.exp (u i/a)),finite_integral_exp]
  simp

theorem radius_second_moment_le (R a : ℝ) (hR : 0 ≤ R) (ha : 0 < a)
    (haR : a ≤ R/Real.log 2) : R^2+2*R*a+2*a^2 ≤ 9*R^2 := by
  have hl : 2/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmul := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp haR
  have hshort : a ≤ 3*R/2 := by nlinarith
  have hsq : a^2 ≤ (3*R/2)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hshort) (by positivity : 0 ≤ 3*R/2+a)]
  have hlin := mul_le_mul_of_nonneg_left hshort (by positivity : 0 ≤ 2*R)
  nlinarith

theorem finite_iid_risk_of_log_bounds {I : Type} [Fintype I] [Nonempty I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ : Measure I) [IsProbabilityMeasure μ] (p : I → ℝ)
    (hp : ∀ i, 0 < p i) (hmass : ∀ i, μ.real {i} = p i)
    (n : ℕ) (u : I → ℝ) (c θ R a : ℝ) (hR : 0 ≤ R) (ha : 0 < a)
    (haR : a ≤ R/Real.log 2)
    (hplus : (c-θ)/a+(n : ℝ)*Real.log (finitePartition p (fun i => u i/a)) ≤ R/a-Real.log 2)
    (hminus : (θ-c)/a+(n : ℝ)*Real.log (finitePartition p (fun i => -u i/a)) ≤ R/a-Real.log 2) :
    (∫ x : Fin n → I, (c+(∑ i, u (x i))-θ)^2 ∂Measure.pi (fun _ : Fin n => μ)) ≤ 9*R^2 := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  let X : (Fin n → I) → ℝ := fun x => c+(∑ i, u (x i))-θ
  have hm : (fun i => μ.real {i}) = p := funext hmass
  have hpos : (∫ x, Real.exp (X x/a) ∂ν) ≤ Real.exp (R/a-Real.log 2) := by
    change (∫ x : Fin n → I, Real.exp ((c+(∑ i, u (x i))-θ)/a) ∂ν) ≤ _
    rw [finite_iid_exponential,hm]
    calc
      _ = Real.exp ((c-θ)/a+(n : ℝ)*Real.log (finitePartition p (fun i => u i/a))) := by
        rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log (finitePartition_pos p _ hp)]
      _ ≤ _ := Real.exp_le_exp.mpr hplus
  have hneg : (∫ x, Real.exp (-X x/a) ∂ν) ≤ Real.exp (R/a-Real.log 2) := by
    have he : (fun x : Fin n → I => Real.exp (-X x/a)) =
        (fun x => Real.exp ((-c+(∑ i, (-u) (x i))-(-θ))/a)) := by
      funext x
      simp only [X,Pi.neg_apply,Finset.sum_neg_distrib]
      congr 1
      ring
    rw [he,finite_iid_exponential,hm]
    have he' : -c-(-θ) = θ-c := by ring
    rw [he']
    change Real.exp ((θ-c)/a)*(finitePartition p (fun i => -u i/a))^n ≤ _
    calc
      _ = Real.exp ((θ-c)/a+(n : ℝ)*Real.log (finitePartition p (fun i => -u i/a))) := by
        rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log (finitePartition_pos p _ hp)]
      _ ≤ _ := Real.exp_le_exp.mpr hminus
  have hbound := (second_moment_of_exponential_bounds ν X (measurable_of_countable X).aestronglyMeasurable
    R a hR ha (finite_function_integrable ν _) (finite_function_integrable ν _) hpos hneg).2
  exact hbound.trans (radius_second_moment_le R a hR ha haR)

/-- A symmetric additive estimator with actual product-law RMS at most 3R,
derived from the affinity separation condition by minimax and moment bounds. -/
theorem finite_convex_rms_comparison {E I : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I] [Nonempty I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (X : Set E) (hXn : X.Nonempty) (hXc : IsCompact X) (hXv : Convex ℝ X)
    (p : E →ᵃ[ℝ] (I → ℝ)) (ell : E →ᵃ[ℝ] ℝ)
    (hpc : Continuous p) (helc : Continuous ell)
    (hp : ∀ x ∈ X, ∀ i, 0 < p x i) (hs : ∀ x ∈ X, ∑ i, p x i = 1)
    (n : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, 1/2 ≤ (realFiniteAffinity (p x) (p y))^n → ell x-ell y < 2*R) :
    ∃ (u : I → ℝ) (c : ℝ), ∀ x ∈ X, ∀ (μ : Measure I) [IsProbabilityMeasure μ],
      (∀ i, μ.real {i} = p x i) →
      (∫ z : Fin n → I, (c+(∑ i, u (z i))-ell x)^2 ∂Measure.pi (fun _ : Fin n => μ)) ≤ 9*R^2 := by
  obtain ⟨u,a,ha,hcert⟩ := finite_repeated_uniform_saddle X hXn hXc hXv p ell hpc helc hp n (2*R) hsep
  obtain ⟨haR,c,hc⟩ := finite_saddle_centering X hXn hXc p ell hpc helc hp hs n R u a ha hcert
  refine ⟨u,c,?_⟩
  intro x hx μ _ hm
  exact finite_iid_risk_of_log_bounds μ (p x) (hp x hx) hm n u c (ell x) R a hR ha haR
    (hc x hx).1 (hc x hx).2

end ThresholdHC.CriticalEntropy
