import ThresholdHC.ConfidenceLocalization.DensityAffinity
import ThresholdHC.CriticalEntropy.HellingerGeometry

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

theorem capped_affinity_statistic {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m) :
    hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m) (cappedTranscriptLaw μ ν p₀ p₁ r A m) =
      hellingerAffinity (cappedStatisticLaw μ ν p₀ p₁ q A m) (cappedStatisticLaw μ ν p₀ p₁ r A m) := by
  let ξ := stoppedReference ν A m
  let T : R × CappedWord m → Fin (m+1) × Fin (m+1) := fun z => stoppedStatistic m z.2
  let f : Fin (m+1) × Fin (m+1) → ℝ≥0∞ :=
    fun i => populationWordLikelihood μ p₀ p₁ q i.1.val i.2.val
  let g : Fin (m+1) × Fin (m+1) → ℝ≥0∞ :=
    fun i => populationWordLikelihood μ p₀ p₁ r i.1.val i.2.val
  have hf : cappedTranscriptLaw μ ν p₀ p₁ q A m = ξ.withDensity (f ∘ T) :=
    cappedTranscriptLaw_density μ ν p₀ p₁ q h₀ h₁ hq A m hcap
  have hg : cappedTranscriptLaw μ ν p₀ p₁ r A m = ξ.withDensity (g ∘ T) :=
    cappedTranscriptLaw_density μ ν p₀ p₁ r h₀ h₁ hr A m hcap
  rw [cappedStatisticLaw,cappedStatisticLaw,hf,hg]
  apply affinity_factored_statistic ξ T
    ((measurable_of_countable (stoppedStatistic m)).comp measurable_snd) f g
    (measurable_of_countable f) (measurable_of_countable g)
  · intro i
    exact ne_top_of_le_ne_top (by norm_num) (populationWordLikelihood_le_one μ p₀ p₁ q _ _)
  · intro i
    exact ne_top_of_le_ne_top (by norm_num) (populationWordLikelihood_le_one μ p₀ p₁ r _ _)

theorem capped_affinity_real {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m) :
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r A m)).toReal =
      realFiniteAffinity
        (fun i => (cappedStatisticLaw μ ν p₀ p₁ q A m).real {i})
        (fun i => (cappedStatisticLaw μ ν p₀ p₁ r A m).real {i}) := by
  let := cappedStatisticLaw_probability μ ν p₀ p₁ q h₀ h₁ hq A m
  let := cappedStatisticLaw_probability μ ν p₀ p₁ r h₀ h₁ hr A m
  rw [capped_affinity_statistic μ ν p₀ p₁ q r h₀ h₁ hq hr A m hcap,hellingerAffinity_finite]
  exact finiteAffinity_toReal _ _ (fun i => measure_ne_top _ _) (fun i => measure_ne_top _ _)

theorem capped_pair_geometry {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (ρ : ℝ) :
    ∃ H : PopulationDual μ × PopulationDual μ → ℝ, Continuous H ∧
      ConvexOn ℝ (populationDualSet μ ρ ×ˢ populationDualSet μ ρ) H ∧
      ∀ f ∈ populationDualSet μ ρ, ∀ g ∈ populationDualSet μ ρ,
        H (f,g) = 1-(hellingerAffinity
          (cappedTranscriptLaw μ ν p₀ p₁ (populationDualPrior μ f) A m)
          (cappedTranscriptLaw μ ν p₀ p₁ (populationDualPrior μ g) A m)).toReal := by
  obtain ⟨F,hFc,hF⟩ := capped_observation_affine_representation μ ν p₀ p₁ h₀ h₁ A m hcap ρ
  let select : (Option (Fin (m+1) × Fin (m+1)) → ℝ) →ₗ[ℝ] (Fin (m+1) × Fin (m+1) → ℝ) :=
    { toFun := fun v i => v (some i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let G := select.toAffineMap.comp F
  have hGc : Continuous G := by
    apply continuous_pi
    intro i
    exact (continuous_apply (some i)).comp hFc
  have hG (f : PopulationDual μ) (hf : f ∈ populationDualSet μ ρ) (i : Fin (m+1) × Fin (m+1)) :
      G f i = (cappedStatisticLaw μ ν p₀ p₁ (populationDualPrior μ f) A m).real {i} := by
    change F f (some i) = _
    rw [hF f hf]
    rfl
  let H : PopulationDual μ × PopulationDual μ → ℝ :=
    fun z => 1-realFiniteAffinity (G z.1) (G z.2)
  refine ⟨H,?_,?_,?_⟩
  · exact continuous_const.sub (realFiniteAffinity_continuous.comp
      ((hGc.comp continuous_fst).prodMk (hGc.comp continuous_snd)))
  · have hc := ConvexOn.comp_affineMap (G.prodMap G) realFiniteDistance_convex
    apply hc.subset
    · intro z hz
      constructor
      · intro i
        change 0 ≤ G z.1 i
        rw [hG z.1 hz.1 i]
        exact measureReal_nonneg
      · intro i
        change 0 ≤ G z.2 i
        rw [hG z.2 hz.2 i]
        exact measureReal_nonneg
    · exact (populationDualSet_convex μ ρ).prod (populationDualSet_convex μ ρ)
  · intro f hf g hg
    rw [capped_affinity_real μ ν p₀ p₁ _ _ h₀ h₁
      (populationDualPrior_measurable μ f) (populationDualPrior_measurable μ g) A m hcap]
    change 1-realFiniteAffinity (G f) (G g) = _
    rw [show G f = (fun i => (cappedStatisticLaw μ ν p₀ p₁ (populationDualPrior μ f) A m).real {i})
        from funext (hG f hf),
      show G g = (fun i => (cappedStatisticLaw μ ν p₀ p₁ (populationDualPrior μ g) A m).real {i})
        from funext (hG g hg)]

end ThresholdHC.ConfidenceLocalization
