import ThresholdHC.CriticalEntropy.CappedObservation

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem map_factored_density {Ω I : Type} [MeasurableSpace Ω] [MeasurableSpace I]
    (ξ : Measure Ω) (T : Ω → I) (hT : Measurable T)
    (g : I → ℝ≥0∞) (hg : Measurable g) :
    (ξ.withDensity (g ∘ T)).map T = (ξ.map T).withDensity g := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hT hS,withDensity_apply _ (hT hS),withDensity_apply _ hS,
    setLIntegral_map hS hg hT]
  rfl

theorem factored_density_restrict {Ω I : Type} [MeasurableSpace Ω] [MeasurableSpace I]
    [MeasurableSingletonClass I] (ξ : Measure Ω) (T : Ω → I) (hT : Measurable T)
    (g : I → ℝ≥0∞) (i : I) :
    (ξ.withDensity (g ∘ T)).restrict (T ⁻¹' {i}) = g i • ξ.restrict (T ⁻¹' {i}) := by
  rw [restrict_withDensity (hT (measurableSet_singleton i))]
  have he : g ∘ T =ᵐ[ξ.restrict (T ⁻¹' {i})] (fun _ => g i) := by
    filter_upwards [ae_restrict_mem (hT (measurableSet_singleton i))] with x hx
    change g (T x) = g i
    rw [show T x = i from hx]
  rw [withDensity_congr_ae he,withDensity_const]

theorem factored_density_fiber_mass {Ω I : Type} [MeasurableSpace Ω] [MeasurableSpace I]
    [MeasurableSingletonClass I] (ξ : Measure Ω) (T : Ω → I) (hT : Measurable T)
    (g : I → ℝ≥0∞) (i : I) :
    (ξ.withDensity (g ∘ T)) (T ⁻¹' {i}) = g i * ξ (T ⁻¹' {i}) := by
  have h := congrArg (fun P : Measure Ω => P univ) (factored_density_restrict ξ T hT g i)
  simpa using h

theorem factored_density_cond {Ω I : Type} [MeasurableSpace Ω] [MeasurableSpace I]
    [MeasurableSingletonClass I] (ξ : Measure Ω) (T : Ω → I) (hT : Measurable T)
    (g : I → ℝ≥0∞) (i : I) (hg₀ : g i ≠ 0) (hg_top : g i ≠ ∞) :
    cond (ξ.withDensity (g ∘ T)) (T ⁻¹' {i}) = cond ξ (T ⁻¹' {i}) := by
  rw [ProbabilityTheory.cond,ProbabilityTheory.cond,
    factored_density_fiber_mass ξ T hT g i,factored_density_restrict ξ T hT g i,
    smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hg₀) (Or.inl hg_top)]
  calc
    _ = (ξ (T ⁻¹' {i}))⁻¹ * ((g i)⁻¹*g i) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hg₀ hg_top,mul_one]

theorem cappedStatisticLaw_density {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m) :
    cappedStatisticLaw μ ν p₀ p₁ q A m =
      ((stoppedReference ν A m).map (fun z => stoppedStatistic m z.2)).withDensity
        (fun i => populationWordLikelihood μ p₀ p₁ q i.1.val i.2.val) := by
  rw [cappedStatisticLaw,cappedTranscriptLaw_density μ ν p₀ p₁ q h₀ h₁ hq A m hcap]
  let T : R × CappedWord m → Fin (m+1) × Fin (m+1) := fun z => stoppedStatistic m z.2
  let g : Fin (m+1) × Fin (m+1) → ℝ≥0∞ :=
    fun i => populationWordLikelihood μ p₀ p₁ q i.1.val i.2.val
  have he : (fun z : R × CappedWord m =>
      populationWordLikelihood μ p₀ p₁ q z.2.1.val (wordHeads z.2.2)) = g ∘ T := rfl
  rw [he]
  exact map_factored_density (stoppedReference ν A m) T
    ((measurable_of_countable (stoppedStatistic m)).comp measurable_snd) g (measurable_of_countable g)

end ThresholdHC.CriticalEntropy
