import ThresholdHC.ConfidenceLocalization.StatisticSupport
import ThresholdHC.ConfidenceLocalization.MixtureScore

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

/-- Restricting priors halfway toward a positive constant makes the finite
sufficient-statistic support fixed, including singular Bernoulli endpoints.
A constant recentering then gives a score for the entire original class. -/
theorem regularized_observation_score {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (c : unitInterval) (hc0 : 0 < (c : ℝ)) (hc : (c : ℝ) ≤ 1/2)
    (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ)
    (hsep : ∀ q r : D → unitInterval, CappedPrior μ (c : ℝ) q → CappedPrior μ (c : ℝ) r →
      1/2 ≤ ((hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior q (fun _ => c)) A m)
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior r (fun _ => c)) A m)).toReal)^n →
      (∫ d, (midpointPrior q (fun _ => c) d : ℝ) ∂μ)-
        (∫ d, (midpointPrior r (fun _ => c) d : ℝ) ∂μ) < 2*ε) :
    ∃ f : Fin (m+1) × Fin (m+1) → ℝ,
      ∀ q : D → unitInterval, CappedPrior μ (c : ℝ) q →
      |(∫ i, f i ∂cappedStatisticLaw μ ν p₀ p₁ q A m)-(∫ d, (q d : ℝ) ∂μ)| ≤ 6*ε ∧
      evariance f (cappedStatisticLaw μ ν p₀ p₁ q A m) ≤ ENNReal.ofReal (18*(n : ℝ)*ε^2) := by
  classical
  let I := Fin (m+1) × Fin (m+1)
  let X := cappedObservationImage μ ν p₀ p₁ A m (c : ℝ)
  let base := cappedStatisticLaw μ ν p₀ p₁ (fun _ => c) A m
  let : IsProbabilityMeasure base := cappedStatisticLaw_probability μ ν p₀ p₁ _ h₀ h₁ measurable_const A m
  let b := fun i : I => base.real {i}
  let select : (Option I → ℝ) →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun v i => v (some i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let target : (Option I → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => v none
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p : (Option I → ℝ) →ᵃ[ℝ] (I → ℝ) :=
    (1/2 : ℝ) • select.toAffineMap + AffineMap.const ℝ _ (fun i => b i/2)
  let ell : (Option I → ℝ) →ᵃ[ℝ] ℝ :=
    (1/2 : ℝ) • target.toAffineMap + AffineMap.const ℝ _ ((c : ℝ)/2)
  have hp (q : D → unitInterval) (hq : Measurable q) (i : I) :
      p (cappedObservationVector μ ν p₀ p₁ q A m) i =
        (cappedStatisticLaw μ ν p₀ p₁ (midpointPrior q (fun _ => c)) A m).real {i} := by
    rw [statistic_mass_midpoint μ ν p₀ p₁ q _ h₀ h₁ hq measurable_const A m i]
    change (1/2 : ℝ)*(cappedStatisticLaw μ ν p₀ p₁ q A m).real {i}+b i/2 = _
    dsimp [b,base]
    ring
  have he (q : D → unitInterval) (hq : Measurable q) :
      ell (cappedObservationVector μ ν p₀ p₁ q A m) =
        ∫ d, (midpointPrior q (fun _ => c) d : ℝ) ∂μ := by
    rw [midpointPrior_integral μ q _ hq measurable_const]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    change (1/2 : ℝ)*(∫ d, (q d : ℝ) ∂μ)+(c : ℝ)/2 = _
    ring
  let support := {i : I | 0 < b i}
  have hbsum : (∑ i, b i) = 1 := by
    simpa only [b,Finset.coe_univ,probReal_univ] using sum_measureReal_singleton (μ := base) Finset.univ
  have hsn : support.Nonempty := by
    by_contra hn
    have hz : ∀ i, b i = 0 := fun i =>
      le_antisymm (le_of_not_gt (fun hi => hn ⟨i,hi⟩)) measureReal_nonneg
    simp_rw [hz] at hbsum
    simp at hbsum
  have hpositive : ∀ v ∈ X, ∀ i ∈ support, 0 < p v i := by
    rintro v ⟨q,hq,rfl⟩ i hi
    change 0 < (1/2 : ℝ)*(cappedStatisticLaw μ ν p₀ p₁ q A m).real {i}+b i/2
    have hbi : 0 < b i := hi
    have hqi : 0 ≤ (cappedStatisticLaw μ ν p₀ p₁ q A m).real {i} := measureReal_nonneg
    linarith
  have hzero : ∀ v ∈ X, ∀ i ∉ support, p v i = 0 := by
    rintro v ⟨q,hq,rfl⟩ i hi
    have hb : b i = 0 := le_antisymm (le_of_not_gt hi) measureReal_nonneg
    have hqz := statistic_common_support μ ν p₀ p₁ q h₀ h₁ hq.1 c hc0 hc A m i hb
    change (1/2 : ℝ)*(cappedStatisticLaw μ ν p₀ p₁ q A m).real {i}+b i/2 = 0
    rw [hqz,hb]
    ring
  have htotal : ∀ v ∈ X, ∑ i, p v i = 1 := by
    rintro v ⟨q,hq,rfl⟩
    simp_rw [hp q hq.1]
    exact (capped_statistic_probabilities μ ν p₀ p₁ _ h₀ h₁ (measurable_midpointPrior q _ hq.1 measurable_const) A m).2
  have hXn := capped_observation_image_nonempty μ ν p₀ p₁ A m (c : ℝ) hc0.le
  obtain ⟨hXc,hXv⟩ := capped_observation_image_compact_convex μ ν p₀ p₁ h₀ h₁ A m hcap (c : ℝ)
  obtain ⟨f,hf⟩ := finite_convex_one_run X hXn hXc hXv p ell
    (by apply continuous_pi; intro i; change Continuous (fun v : Option I → ℝ => (1/2 : ℝ)*v (some i)+b i/2); fun_prop)
    (by change Continuous (fun v : Option I → ℝ => (1/2 : ℝ)*v none+(c : ℝ)/2); fun_prop)
    support hsn hpositive hzero htotal n ε hε (by
      rintro v ⟨q,hq,rfl⟩ w ⟨r,hr,rfl⟩ ha
      rw [he q hq.1,he r hr.1]
      apply hsep q r hq hr
      rw [capped_affinity_real μ ν p₀ p₁ _ _ h₀ h₁
        (measurable_midpointPrior q _ hq.1 measurable_const)
        (measurable_midpointPrior r _ hr.1 measurable_const) A m hcap]
      simpa only [funext (hp q hq.1),funext (hp r hr.1)] using ha)
  let Z := fun i => f i+((∫ j, f j ∂base)-(c : ℝ))
  refine ⟨Z,?_⟩
  intro q hq
  let P := cappedStatisticLaw μ ν p₀ p₁ q A m
  let M := cappedStatisticLaw μ ν p₀ p₁ (midpointPrior q (fun _ => c)) A m
  let : IsProbabilityMeasure P := cappedStatisticLaw_probability μ ν p₀ p₁ q h₀ h₁ hq.1 A m
  let : IsProbabilityMeasure M := cappedStatisticLaw_probability μ ν p₀ p₁ _ h₀ h₁
    (measurable_midpointPrior q _ hq.1 measurable_const) A m
  have ht := hf (cappedObservationVector μ ν p₀ p₁ q A m) ⟨q,hq,rfl⟩ M (fun i => (hp q hq.1 i).symm)
  have hb : |(∫ i, f i ∂M)-((∫ d, (q d : ℝ) ∂μ)+(c : ℝ))/2| ≤ 3*ε := by
    have h := ht.1
    change ((∫ i, f i ∂M)-((1/2 : ℝ)*(∫ d, (q d : ℝ) ∂μ)+(c : ℝ)/2))^2 ≤ 9*ε^2 at h
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg ((∫ i, f i ∂M)-((∫ d, (q d : ℝ) ∂μ)+(c : ℝ))/2+3*ε),
      sq_nonneg ((∫ i, f i ∂M)-((∫ d, (q d : ℝ) ∂μ)+(c : ℝ))/2-3*ε)]
  have h := half_score_transfer P base M (statistic_law_midpoint μ ν p₀ p₁ q _ h₀ h₁ hq.1 measurable_const A m)
    f c (∫ d, (q d : ℝ) ∂μ) (3*ε) ((n : ℝ)*(9*ε^2)) (by positivity) hb ht.2
  dsimp only at h
  refine ⟨h.1.trans_eq (by ring),h.2.trans_eq ?_⟩
  congr 1
  ring

end ThresholdHC.ConfidenceLocalization
