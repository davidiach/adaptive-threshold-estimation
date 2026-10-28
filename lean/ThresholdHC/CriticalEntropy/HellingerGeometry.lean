import ThresholdHC.CriticalEntropy.ObservationAffine
import ThresholdHC.CriticalEntropy.FiniteGeometry

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem capped_statistic_probabilities {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) (m : ℕ) :
    (∀ i, 0 ≤ (cappedStatisticLaw μ ν p₀ p₁ q A m).real {i}) ∧
      (∑ i, (cappedStatisticLaw μ ν p₀ p₁ q A m).real {i}) = 1 := by
  let : IsProbabilityMeasure (cappedStatisticLaw μ ν p₀ p₁ q A m) :=
    cappedStatisticLaw_probability μ ν p₀ p₁ q h₀ h₁ hq A m
  refine ⟨fun i => measureReal_nonneg,?_⟩
  simpa using sum_measureReal_singleton (μ := cappedStatisticLaw μ ν p₀ p₁ q A m) Finset.univ

theorem capped_observation_affinity_real {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1) :
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r A m)).toReal =
      realFiniteAffinity
        (fun i => (cappedStatisticLaw μ ν p₀ p₁ q A m).real {i})
        (fun i => (cappedStatisticLaw μ ν p₀ p₁ r A m).real {i}) := by
  let : IsProbabilityMeasure (cappedStatisticLaw μ ν p₀ p₁ q A m) :=
    cappedStatisticLaw_probability μ ν p₀ p₁ q h₀ h₁ hq A m
  let : IsProbabilityMeasure (cappedStatisticLaw μ ν p₀ p₁ r A m) :=
    cappedStatisticLaw_probability μ ν p₀ p₁ r h₀ h₁ hr A m
  rw [capped_observation_finite_affinity μ ν p₀ p₁ q r h₀ h₁ hq hr A m hcap hp]
  exact finiteAffinity_toReal _ _ (fun i => measure_ne_top _ _) (fun i => measure_ne_top _ _)

/-- A continuous function on the whole dual pair space that equals the actual
squared Hellinger distance on the admissible set and is convex there. -/
theorem capped_observation_hellinger_geometry {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (ρ : ℝ)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1) :
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
    rw [capped_observation_affinity_real μ ν p₀ p₁ _ _ h₀ h₁
      (populationDualPrior_measurable μ f) (populationDualPrior_measurable μ g) A m hcap hp]
    change 1-realFiniteAffinity (G f) (G g) = _
    rw [show G f = (fun i => (cappedStatisticLaw μ ν p₀ p₁ (populationDualPrior μ f) A m).real {i})
        from funext (hG f hf),
      show G g = (fun i => (cappedStatisticLaw μ ν p₀ p₁ (populationDualPrior μ g) A m).real {i})
        from funext (hG g hg)]

theorem capped_observation_affinity_le_one {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1) :
    hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r A m) ≤ 1 := by
  let : IsProbabilityMeasure (cappedStatisticLaw μ ν p₀ p₁ q A m) :=
    cappedStatisticLaw_probability μ ν p₀ p₁ q h₀ h₁ hq A m
  let : IsProbabilityMeasure (cappedStatisticLaw μ ν p₀ p₁ r A m) :=
    cappedStatisticLaw_probability μ ν p₀ p₁ r h₀ h₁ hr A m
  have hfin : hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r A m) ≠ ∞ := by
    rw [capped_observation_finite_affinity μ ν p₀ p₁ q r h₀ h₁ hq hr A m hcap hp]
    unfold finiteAffinity
    exact ENNReal.sum_ne_top.mpr (fun i hi =>
      ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)))
  apply (ENNReal.toReal_le_toReal hfin (by norm_num)).mp
  rw [capped_observation_affinity_real μ ν p₀ p₁ q r h₀ h₁ hq hr A m hcap hp,ENNReal.toReal_one]
  obtain ⟨hq₀,hqsum⟩ := capped_statistic_probabilities μ ν p₀ p₁ q h₀ h₁ hq A m
  obtain ⟨hr₀,hrsum⟩ := capped_statistic_probabilities μ ν p₀ p₁ r h₀ h₁ hr A m
  exact realFiniteAffinity_le_one _ _ hq₀ hr₀ hqsum hrsum

end ThresholdHC.CriticalEntropy
