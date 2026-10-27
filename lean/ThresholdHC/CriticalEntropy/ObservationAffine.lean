import ThresholdHC.CriticalEntropy.ObservationGeometryModel
import ThresholdHC.CriticalEntropy.LikelihoodAffine

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem cappedStatisticLaw_affine_moment {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (i : Fin (m+1) × Fin (m+1)) :
    ∃ (g : Lp ℝ 2 μ) (b : ℝ), ∀ q : D → unitInterval, Measurable q →
      (cappedStatisticLaw μ ν p₀ p₁ q A m).real {i} = (∫ d, (q d : ℝ)*g d ∂μ)+b := by
  obtain ⟨g,b,hgb⟩ := populationWordLikelihood_affine_moment μ p₀ p₁ h₀ h₁ i.1.val i.2.val
  let a := ((stoppedReference ν A m).map (fun z => stoppedStatistic m z.2)).real {i}
  refine ⟨a • g,b*a,?_⟩
  intro q hq
  rw [cappedStatisticLaw_real_mass μ ν p₀ p₁ q h₀ h₁ hq A m hcap i,hgb q hq]
  change ((∫ d, (q d : ℝ)*g d ∂μ)+b)*a = _
  calc
    _ = a*(∫ d, (q d : ℝ)*g d ∂μ)+b*a := by ring
    _ = (∫ d, a*((q d : ℝ)*g d) ∂μ)+b*a := by rw [integral_const_mul]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul a g] with d hd
      rw [hd]
      simp only [Pi.smul_apply,smul_eq_mul]
      ring

theorem cappedObservationVector_affine_coordinates {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) :
    ∃ (g : Option (Fin (m+1) × Fin (m+1)) → Lp ℝ 2 μ)
      (b : Option (Fin (m+1) × Fin (m+1)) → ℝ),
      ∀ q : D → unitInterval, Measurable q → cappedObservationVector μ ν p₀ p₁ q A m =
        (fun i => (∫ d, (q d : ℝ)*g i d ∂μ)+b i) := by
  classical
  have hc (i : Option (Fin (m+1) × Fin (m+1))) :
      ∃ (g : Lp ℝ 2 μ) (b : ℝ), ∀ q : D → unitInterval, Measurable q →
        cappedObservationVector μ ν p₀ p₁ q A m i = (∫ d, (q d : ℝ)*g d ∂μ)+b := by
    cases i with
    | none =>
      refine ⟨Lp.const 2 μ (1 : ℝ),0,?_⟩
      intro q hq
      simp only [cappedObservationVector,add_zero]
      symm
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with d hd
      simp [hd]
    | some i => exact cappedStatisticLaw_affine_moment μ ν p₀ p₁ h₀ h₁ A m hcap i
  choose g b hg using hc
  refine ⟨g,b,?_⟩
  intro q hq
  funext i
  exact hg i q hq

theorem cappedObservationVector_congr_ae {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (he : (fun d => (q d : ℝ)) =ᵐ[μ] (fun d => (r d : ℝ))) :
    cappedObservationVector μ ν p₀ p₁ q A m = cappedObservationVector μ ν p₀ p₁ r A m := by
  obtain ⟨g,b,hgb⟩ := cappedObservationVector_affine_coordinates μ ν p₀ p₁ h₀ h₁ A m hcap
  rw [hgb q hq,hgb r hr]
  funext i
  congr 1
  exact integral_congr_ae (he.mono (fun d hd => congrArg (fun t : ℝ => t*g i d) hd))

/-- A continuous affine representation of the actual finite experiment,
including its target coordinate. Equality is asserted on the proved population set. -/
theorem capped_observation_affine_representation {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (ρ : ℝ) :
    ∃ F : PopulationDual μ →ᵃ[ℝ] (Option (Fin (m+1) × Fin (m+1)) → ℝ),
      Continuous F ∧ ∀ f ∈ populationDualSet μ ρ,
        F f = cappedObservationVector μ ν p₀ p₁ (populationDualPrior μ f) A m := by
  obtain ⟨g,b,hgb⟩ := cappedObservationVector_affine_coordinates μ ν p₀ p₁ h₀ h₁ A m hcap
  refine ⟨populationMomentMap μ g b,populationMomentMap_continuous μ g b,?_⟩
  intro f hf
  rw [hgb _ (populationDualPrior_measurable μ f)]
  funext i
  rw [populationMomentMap_apply,populationDualPrior_test μ ρ f hf (g i)]

theorem capped_observation_image_compact_convex {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (ρ : ℝ) :
    IsCompact (cappedObservationImage μ ν p₀ p₁ A m ρ) ∧
      Convex ℝ (cappedObservationImage μ ν p₀ p₁ A m ρ) := by
  obtain ⟨g,b,hgb⟩ := cappedObservationVector_affine_coordinates μ ν p₀ p₁ h₀ h₁ A m hcap
  have he : cappedObservationImage μ ν p₀ p₁ A m ρ = boundedPriorMomentSet μ ρ g b := by
    ext v
    constructor
    · rintro ⟨q,hq,hv⟩
      refine ⟨q,hq.1,hq.2.1,hq.2.2,?_⟩
      intro i
      rw [← hv,hgb q hq.1]
    · rintro ⟨q,hq,hh,hm,hv⟩
      refine ⟨q,⟨hq,hh,hm⟩,?_⟩
      rw [hgb q hq]
      exact funext (fun i => (hv i).symm)
  rw [he]
  exact boundedPriorMomentSet_compact_convex μ ρ g b

theorem capped_observation_image_nonempty {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) (ν : Measure R) (p₀ p₁ : D → unitInterval)
    (A : StoppedProcedure R E) (m : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (cappedObservationImage μ ν p₀ p₁ A m ρ).Nonempty := by
  refine ⟨cappedObservationVector μ ν p₀ p₁ (fun _ => 0) A m,fun _ => 0,?_,rfl⟩
  refine ⟨measurable_const,?_,?_⟩
  · intro d; norm_num
  · simpa using hρ

theorem capped_observation_image_positive {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (ρ : ℝ)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1)
    (i : Fin (m+1) × Fin (m+1))
    (hi : ((stoppedReference ν A m).map (fun z => stoppedStatistic m z.2)) {i} ≠ 0)
    (v : Option (Fin (m+1) × Fin (m+1)) → ℝ)
    (hv : v ∈ cappedObservationImage μ ν p₀ p₁ A m ρ) : 0 < v (some i) := by
  obtain ⟨q,hq,rfl⟩ := hv
  let : IsProbabilityMeasure (cappedStatisticLaw μ ν p₀ p₁ q A m) :=
    cappedStatisticLaw_probability μ ν p₀ p₁ q h₀ h₁ hq.1 A m
  have hne : cappedStatisticLaw μ ν p₀ p₁ q A m {i} ≠ 0 :=
    fun hz => hi ((cappedStatisticLaw_zero_iff_reference μ ν p₀ p₁ q h₀ h₁ hq.1 A m hcap hp i).mp hz)
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

theorem capped_observation_uniform_positive {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1)
    (i : Fin (m+1) × Fin (m+1))
    (hi : ((stoppedReference ν A m).map (fun z => stoppedStatistic m z.2)) {i} ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ cappedObservationImage μ ν p₀ p₁ A m ρ, ε ≤ v (some i) := by
  obtain ⟨v,hv,hmin⟩ := (capped_observation_image_compact_convex μ ν p₀ p₁ h₀ h₁ A m hcap ρ).1.exists_isMinOn
    (capped_observation_image_nonempty μ ν p₀ p₁ A m ρ hρ) (continuous_apply (some i)).continuousOn
  exact ⟨v (some i),capped_observation_image_positive μ ν p₀ p₁ h₀ h₁ A m hcap ρ hp i hi v hv,hmin⟩

end ThresholdHC.CriticalEntropy
