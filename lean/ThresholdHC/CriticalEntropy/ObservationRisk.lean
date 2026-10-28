import ThresholdHC.CriticalEntropy.FiniteSupport
import ThresholdHC.CriticalEntropy.StatisticProcedure

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- The affinity modulus of the actual capped observation experiment produces
one observable estimator, uniformly over all admissible populations. -/
theorem capped_observation_one_run {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (n : ℕ)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1)
    (hsep : ∀ q r : D → unitInterval, CappedPrior μ ρ q → CappedPrior μ ρ r →
      1/2 ≤ ((hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m)
        (cappedTranscriptLaw μ ν p₀ p₁ r A m)).toReal)^n →
      (∫ d, (q d : ℝ) ∂μ)-(∫ d, (r d : ℝ) ∂μ) < 2*ε) :
    ∃ f : Fin (m+1) × Fin (m+1) → ℝ,
      ∀ q : D → unitInterval, CappedPrior μ ρ q →
      |populationMean μ ν p₀ p₁ q (cappedStatisticProcedure A m hcap f)-
        (∫ d, (q d : ℝ) ∂μ)| ≤ 3*ε ∧
      evariance ((cappedStatisticProcedure A m hcap f).output ∘ populationInput p₀ p₁ q)
        (populationMeasure μ ν) ≤ ENNReal.ofReal ((n : ℝ)*(9*ε^2)) := by
  classical
  let I := Fin (m+1) × Fin (m+1)
  let X := cappedObservationImage μ ν p₀ p₁ A m ρ
  let select : (Option I → ℝ) →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun v i => v (some i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ell : (Option I → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => v none
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let s : Set I := {i | ((stoppedReference ν A m).map (fun z => stoppedStatistic m z.2)) {i} ≠ 0}
  have hXn : X.Nonempty := capped_observation_image_nonempty μ ν p₀ p₁ A m ρ hρ
  have hX := capped_observation_image_compact_convex μ ν p₀ p₁ h₀ h₁ A m hcap ρ
  have hz : ∀ v ∈ X, ∀ i ∉ s, select v i = 0 := by
    rintro v ⟨q,hq,rfl⟩ i hi
    have hzero := (cappedStatisticLaw_zero_iff_reference μ ν p₀ p₁ q h₀ h₁ hq.1 A m hcap hp i).mpr
      (by simpa only [s,mem_ofPred_eq,not_not] using hi)
    change (cappedStatisticLaw μ ν p₀ p₁ q A m).real {i} = 0
    simp only [measureReal_def,hzero,ENNReal.toReal_zero]
  have hs : ∀ v ∈ X, ∑ i, select v i = 1 := by
    rintro v ⟨q,hq,rfl⟩
    exact (capped_statistic_probabilities μ ν p₀ p₁ q h₀ h₁ hq.1 A m).2
  have hsn : s.Nonempty := by
    by_contra hn
    obtain ⟨v,hv⟩ := hXn
    have hzall : ∑ i, select v i = 0 := Finset.sum_eq_zero (fun i hi =>
      hz v hv i (fun his => hn ⟨i,his⟩))
    linarith [hs v hv]
  obtain ⟨f,hf⟩ := finite_convex_one_run X hXn hX.1 hX.2 select.toAffineMap ell.toAffineMap
    (by apply continuous_pi; intro i; exact continuous_apply (some i)) (continuous_apply none)
    s hsn (fun v hv i hi => capped_observation_image_positive μ ν p₀ p₁ h₀ h₁ A m hcap ρ hp i hi v hv)
    hz hs n ε hε (by
      rintro v ⟨q,hq,rfl⟩ w ⟨r,hr,rfl⟩ h
      apply hsep q r hq hr
      rwa [capped_observation_affinity_real μ ν p₀ p₁ q r h₀ h₁ hq.1 hr.1 A m hcap hp])
  refine ⟨f,?_⟩
  intro q hq
  let ξ := cappedStatisticLaw μ ν p₀ p₁ q A m
  let : IsProbabilityMeasure ξ := cappedStatisticLaw_probability μ ν p₀ p₁ q h₀ h₁ hq.1 A m
  have h := hf (cappedObservationVector μ ν p₀ p₁ q A m) ⟨q,hq,rfl⟩ ξ (fun i => rfl)
  let Z := cappedStatisticProcedure A m hcap f
  have hZ : Measurable (Z.output ∘ populationInput p₀ p₁ q) :=
    Z.measurable_output.comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq.1)
  have hlaw := cappedStatisticProcedure_output_law μ ν p₀ p₁ q h₀ h₁ hq.1 A m hcap f
  have hm : populationMean μ ν p₀ p₁ q Z = ∫ i, f i ∂ξ := by
    calc
      _ = ∫ y : ℝ, y ∂(populationMeasure μ ν).map (Z.output ∘ populationInput p₀ p₁ q) :=
        (integral_map hZ.aemeasurable measurable_id.aestronglyMeasurable).symm
      _ = ∫ y : ℝ, y ∂ξ.map f := by rw [hlaw]
      _ = _ := integral_map (measurable_of_countable f).aemeasurable measurable_id.aestronglyMeasurable
  have hv : evariance (Z.output ∘ populationInput p₀ p₁ q) (populationMeasure μ ν) = evariance f ξ := by
    calc
      _ = evariance id ((populationMeasure μ ν).map (Z.output ∘ populationInput p₀ p₁ q)) :=
        (evariance_map_measurable (populationMeasure μ ν) _ id hZ measurable_id).symm
      _ = evariance id (ξ.map f) := by rw [hlaw]
      _ = _ := evariance_map_measurable ξ f id (measurable_of_countable f) measurable_id
  constructor
  · change |populationMean μ ν p₀ p₁ q Z-(∫ d, (q d : ℝ) ∂μ)| ≤ 3*ε
    rw [hm]
    have hb : ((∫ i, f i ∂ξ)-(∫ d, (q d : ℝ) ∂μ))^2 ≤ 9*ε^2 := h.1
    apply (abs_le).mpr
    constructor <;> nlinarith [sq_nonneg ((∫ i, f i ∂ξ)-(∫ d, (q d : ℝ) ∂μ)+3*ε),
      sq_nonneg ((∫ i, f i ∂ξ)-(∫ d, (q d : ℝ) ∂μ)-3*ε)]
  · rw [hv]
    exact h.2

end ThresholdHC.CriticalEntropy
