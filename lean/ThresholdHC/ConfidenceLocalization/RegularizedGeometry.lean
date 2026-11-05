import ThresholdHC.ConfidenceLocalization.StatisticSupport

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

/-- Continuous convex Hellinger constraints for half-regularized priors on the
original compact dual population set. -/
theorem regularized_pair_geometry {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (c : unitInterval) :
    ∃ H : PopulationDual μ × PopulationDual μ → ℝ, Continuous H ∧
      ConvexOn ℝ (populationDualSet μ (c : ℝ) ×ˢ populationDualSet μ (c : ℝ)) H ∧
      ∀ f ∈ populationDualSet μ (c : ℝ), ∀ g ∈ populationDualSet μ (c : ℝ),
        H (f,g) = 1-(hellingerAffinity
          (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ f) (fun _ => c)) A m)
          (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ g) (fun _ => c)) A m)).toReal ∧
        H (f,g) ∈ Icc 0 1 := by
  obtain ⟨F,hFc,hF⟩ := capped_observation_affine_representation μ ν p₀ p₁ h₀ h₁ A m hcap (c : ℝ)
  let I := Fin (m+1) × Fin (m+1)
  let select : (Option I → ℝ) →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun v i => v (some i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let base := fun i : I => (cappedStatisticLaw μ ν p₀ p₁ (fun _ => c) A m).real {i}
  let G : PopulationDual μ →ᵃ[ℝ] (I → ℝ) :=
    (1/2 : ℝ) • (select.toAffineMap.comp F) + AffineMap.const ℝ _ (fun i => base i/2)
  have hGc : Continuous G := by
    apply continuous_pi
    intro i
    change Continuous (fun f : PopulationDual μ => (1/2 : ℝ)*F f (some i)+base i/2)
    exact (continuous_const.mul ((continuous_apply (some i)).comp hFc)).add continuous_const
  have hG (f : PopulationDual μ) (hf : f ∈ populationDualSet μ (c : ℝ)) (i : I) :
      G f i = (cappedStatisticLaw μ ν p₀ p₁
        (midpointPrior (populationDualPrior μ f) (fun _ => c)) A m).real {i} := by
    rw [statistic_mass_midpoint μ ν p₀ p₁ _ _ h₀ h₁
      (populationDualPrior_measurable μ f) measurable_const A m i]
    change (1/2 : ℝ)*F f (some i)+base i/2 = _
    rw [hF f hf]
    change (1/2 : ℝ)*(cappedStatisticLaw μ ν p₀ p₁ (populationDualPrior μ f) A m).real {i}+base i/2 = _
    dsimp [base]
    ring
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
    · exact (populationDualSet_convex μ (c : ℝ)).prod (populationDualSet_convex μ (c : ℝ))
  · intro f hf g hg
    have hreal : H (f,g) = 1-(hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ f) (fun _ => c)) A m)
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ g) (fun _ => c)) A m)).toReal := by
      rw [capped_affinity_real μ ν p₀ p₁ _ _ h₀ h₁
        (measurable_midpointPrior _ _ (populationDualPrior_measurable μ f) measurable_const)
        (measurable_midpointPrior _ _ (populationDualPrior_measurable μ g) measurable_const) A m hcap]
      change 1-realFiniteAffinity (G f) (G g) = _
      rw [funext (hG f hf),funext (hG g hg)]
    refine ⟨hreal,?_⟩
    rw [hreal]
    let (u : PopulationDual μ) : IsProbabilityMeasure
        (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ u) (fun _ => c)) A m) :=
      cappedTranscriptLaw_probability μ ν p₀ p₁ _ h₀ h₁
        (measurable_midpointPrior _ _ (populationDualPrior_measurable μ u) measurable_const) A m
    have ha := hellingerAffinity_probability_le_one
      (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ f) (fun _ => c)) A m)
      (cappedTranscriptLaw μ ν p₀ p₁ (midpointPrior (populationDualPrior μ g) (fun _ => c)) A m)
    have hle := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) ha
    simp only [ENNReal.toReal_one] at hle
    exact ⟨sub_nonneg.mpr hle,sub_le_self _ ENNReal.toReal_nonneg⟩

end ThresholdHC.ConfidenceLocalization
