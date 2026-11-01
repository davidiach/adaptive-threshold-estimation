import ThresholdHC.EntropyTailLower.GatedAnnular
import ThresholdHC.ObservableSimulation.OriginalExperiment

/-! Exact population identities under a measurable parameter embedding,
extension of capped priors, and preservation of the actual one-coin
guarantee. The small-gap inclusion retains the original coin parameters. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.CriticalEntropy ThresholdHC.Tier6 ThresholdHC.ObservableSimulation

theorem population_lintegral_map {D E R : Type} [MeasurableSpace D] [MeasurableSpace E]
    [MeasurableSpace R] (μ : Measure D) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (f : D → E) (hf : Measurable f)
    (p₀ p₁ q : E → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (F : R × (ℕ → Bool) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (populationInput p₀ p₁ q z) ∂populationMeasure (μ.map f) ν) =
      ∫⁻ z, F (populationInput (p₀ ∘ f) (p₁ ∘ f) (q ∘ f) z) ∂populationMeasure μ ν := by
  unfold populationMeasure
  have he := Measure.map_prod_map μ (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure)) hf measurable_id
  rw [Measure.map_id] at he
  rw [he]
  have hG : Measurable (fun z => F (populationInput p₀ p₁ q z)) :=
    hF.comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq)
  rw [lintegral_map hG (hf.prodMap measurable_id)]
  rfl

theorem population_integral_map {D E R : Type} [MeasurableSpace D] [MeasurableSpace E]
    [MeasurableSpace R] (μ : Measure D) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (f : D → E) (hf : Measurable f)
    (p₀ p₁ q : E → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (F : R × (ℕ → Bool) → ℝ) (hF : Measurable F) :
    (∫ z, F (populationInput p₀ p₁ q z) ∂populationMeasure (μ.map f) ν) =
      ∫ z, F (populationInput (p₀ ∘ f) (p₁ ∘ f) (q ∘ f) z) ∂populationMeasure μ ν := by
  unfold populationMeasure
  have he := Measure.map_prod_map μ (uniformUnitMeasure.prod (ν.prod uniformTapeMeasure)) hf measurable_id
  rw [Measure.map_id] at he
  rw [he]
  have hG : Measurable (fun z => F (populationInput p₀ p₁ q z)) :=
    hF.comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq)
  rw [integral_map (hf.prodMap measurable_id).aemeasurable hG.aestronglyMeasurable]
  rfl

theorem cappedPrior_extend {D E : Type} [MeasurableSpace D] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (f : D → E) (hf : MeasurableEmbedding f)
    (ρ : ℝ) (q : D → unitInterval) (hq : CappedPrior μ ρ q) :
    ∃ q' : E → unitInterval, CappedPrior (μ.map f) ρ q' ∧ q' ∘ f = q := by
  let q' := Function.extend f q (fun _ => 0)
  have hm : Measurable q' := hf.measurable_extend hq.1 measurable_const
  have he : q' ∘ f = q := funext (fun d => hf.injective.extend_apply q (fun _ => 0) d)
  refine ⟨q',⟨hm,?_,?_⟩,he⟩
  · intro e
    by_cases hr : ∃ d, f d = e
    · obtain ⟨d,rfl⟩ := hr
      change ((q' ∘ f) d:ℝ) ≤ 1/2
      rw [he]
      exact hq.2.1 d
    · rw [show q' e = 0 from Function.extend_apply' q (fun _ => 0) e hr]
      norm_num
  · have hqr : Measurable (fun e => (q' e:ℝ)) := measurable_subtype_coe.comp hm
    rw [integral_map hf.measurable.aemeasurable hqr.aestronglyMeasurable]
    have he' : (fun d => (q' (f d):ℝ)) = fun d => (q d:ℝ) := congrArg (fun g => fun d => (g d:ℝ)) he
    rw [he']
    exact hq.2.2

theorem cappedGuarantee_pullback {D E R : Type} [MeasurableSpace D] [MeasurableSpace E]
    [MeasurableSpace R] (μ : Measure D) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (f : D → E) (hf : MeasurableEmbedding f)
    (p₀ p₁ : E → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ m : ℝ)
    (hA : CappedPopulationGuarantee (μ.map f) ν p₀ p₁ A ρ m) :
    CappedPopulationGuarantee μ ν (p₀ ∘ f) (p₁ ∘ f) A ρ m := by
  constructor
  · intro q hq
    obtain ⟨q',hq',he⟩ := cappedPrior_extend μ f hf ρ q hq
    have h := hA.moment q' hq'
    unfold populationSecondMoment at h ⊢
    have hF : Measurable (fun z => ENNReal.ofReal ((A.output z)^2)) :=
      ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2)
    rw [population_lintegral_map μ ν f hf.measurable p₀ p₁ q' h₀ h₁ hq'.1 _ hF,he] at h
    exact h
  · intro q hq
    obtain ⟨q',hq',he⟩ := cappedPrior_extend μ f hf ρ q hq
    have h := hA.work q' hq'
    unfold populationExpectedWork at h ⊢
    rw [population_lintegral_map μ ν f hf.measurable p₀ p₁ q' h₀ h₁ hq'.1
      _ (measurable_stoppedProcedureWork A),he] at h
    exact h
  · intro q hq
    obtain ⟨q',hq',he⟩ := cappedPrior_extend μ f hf ρ q hq
    have h := hA.bias q' hq'
    unfold populationMean at h ⊢
    rw [population_integral_map μ ν f hf.measurable p₀ p₁ q' h₀ h₁ hq'.1 _ A.measurable_output,he] at h
    have hqr : Measurable (fun e => (q' e:ℝ)) := measurable_subtype_coe.comp hq'.1
    rw [integral_map hf.measurable.aemeasurable hqr.aestronglyMeasurable] at h
    have he' : (fun d => (q' (f d):ℝ)) = fun d => (q d:ℝ) := congrArg (fun g => fun d => (g d:ℝ)) he
    simpa only [he'] using h

def entropyGapInclusion (d : EntropyGap) : Gap := ⟨d.val,d.property.1,by linarith [d.property.2]⟩

theorem entropyGapInclusion_measurableEmbedding : MeasurableEmbedding entropyGapInclusion := by
  refine ⟨fun d e h => Subtype.ext (congrArg (fun x : Gap => (x:ℝ)) h),measurable_subtype_coe.subtype_mk,?_⟩
  intro S hS
  have hm : MeasurableSet (Subtype.val '' S : Set ℝ) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ioc).measurableSet_image' hS
  have he : entropyGapInclusion '' S = (Subtype.val : Gap → ℝ) ⁻¹' (Subtype.val '' S) := by
    ext d
    constructor
    · rintro ⟨e,he,rfl⟩
      exact ⟨e,he,rfl⟩
    · rintro ⟨e,he,hed⟩
      exact ⟨e,he,Subtype.ext hed⟩
  rw [he]
  exact measurable_subtype_coe hm

theorem entropyGapInclusion_parameter (s : Bool) :
    gapParameter s ∘ entropyGapInclusion = fun d => signParameter d s := by
  funext d
  rfl

end ThresholdHC.EntropyTailLower
