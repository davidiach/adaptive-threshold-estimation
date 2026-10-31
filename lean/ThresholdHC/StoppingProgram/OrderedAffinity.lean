import ThresholdHC.StoppingProgram.OrderedStoppedLaw
import ThresholdHC.CriticalEntropy.EventualAffinity

/-! Full seed-and-stopped-word Hellinger affinity reduces exactly to finite
word weights, including boundary Bernoulli parameters and null cells. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw)

theorem factored_affinity_nonnegative {Ω I : Type} [MeasurableSpace Ω] [MeasurableSpace I]
    (ξ : Measure Ω) [IsFiniteMeasure ξ] (T : Ω → I) (hT : Measurable T)
    (f g : I → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hft : ∀ i, f i ≠ ⊤) (hgt : ∀ i, g i ≠ ⊤) :
    hellingerAffinity (ξ.withDensity (f ∘ T)) (ξ.withDensity (g ∘ T)) =
      hellingerAffinity ((ξ.withDensity (f ∘ T)).map T) ((ξ.withDensity (g ∘ T)).map T) := by
  rw [map_factored_density ξ T hT f hf,map_factored_density ξ T hT g hg,
    hellingerAffinity_withDensity_nonnegative ξ _ _ (hf.comp hT) (hg.comp hT)
      (fun x => hft (T x)) (fun x => hgt (T x)),
    hellingerAffinity_withDensity_nonnegative (ξ.map T) f g hf hg hft hgt,
    lintegral_map (by fun_prop) hT]
  rfl

theorem original_stopped_word_mass {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (q : SignLaw) (A : StoppedProcedure R E) (N : ℕ) (hcap : ∀ z, A.stop z ≤ N)
    (w : CappedWord N) :
    ((cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit q) A N).map Prod.snd).real {w} =
      ν.real (stoppedSeedCell A w.2 Set.univ)*prefixCoefficient μ q w.1.val (wordHeads w.2) := by
  rw [Measure.real,Measure.map_apply measurable_snd (measurableSet_singleton w)]
  have he : (Prod.snd : R × CappedWord N → CappedWord N) ⁻¹' {w} = Set.univ ×ˢ {w} := by ext z; simp
  rw [he,cappedTranscriptLaw_cell μ ν _ _ _ (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit q) A N hcap w Set.univ MeasurableSet.univ,
    original_wordLikelihood_integral,ENNReal.toReal_mul]
  change ν.real (stoppedSeedCell A w.2 Set.univ)*
    (ENNReal.ofReal (prefixCoefficient μ q w.1.val (wordHeads w.2))).toReal = _
  rw [ENNReal.toReal_ofReal (prefixCoefficient_nonneg μ q _ _)]

theorem original_stopped_word_affinity {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (q r : SignLaw) (A : StoppedProcedure R E) (N : ℕ) (hcap : ∀ z, A.stop z ≤ N) :
    (hellingerAffinity
      (cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit q) A N)
      (cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit r) A N)).toReal =
      ∑ w : CappedWord N, ν.real (stoppedSeedCell A w.2 Set.univ)*
        Real.sqrt (prefixCoefficient μ q w.1.val (wordHeads w.2)*prefixCoefficient μ r w.1.val (wordHeads w.2)) := by
  let P := cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit q) A N
  let Q := cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit r) A N
  let ξ := stoppedReference ν A N
  let f : CappedWord N → ℝ≥0∞ := fun w => ENNReal.ofReal (prefixCoefficient μ q w.1.val (wordHeads w.2))
  let g : CappedWord N → ℝ≥0∞ := fun w => ENNReal.ofReal (prefixCoefficient μ r w.1.val (wordHeads w.2))
  have hP : P = ξ.withDensity (f ∘ Prod.snd) := by
    dsimp only [P,ξ]
    rw [cappedTranscriptLaw_density μ ν _ _ _ (measurable_gapParameter false)
      (measurable_gapParameter true) (measurable_signUnit q) A N hcap]
    congr 1
    funext z
    exact original_wordLikelihood_integral μ q _ _
  have hQ : Q = ξ.withDensity (g ∘ Prod.snd) := by
    dsimp only [Q,ξ]
    rw [cappedTranscriptLaw_density μ ν _ _ _ (measurable_gapParameter false)
      (measurable_gapParameter true) (measurable_signUnit r) A N hcap]
    congr 1
    funext z
    exact original_wordLikelihood_integral μ r _ _
  have ha : hellingerAffinity P Q = hellingerAffinity (P.map Prod.snd) (Q.map Prod.snd) := by
    rw [hP,hQ]
    exact factored_affinity_nonnegative ξ Prod.snd measurable_snd f g (measurable_of_countable _) (measurable_of_countable _)
      (fun _ => ENNReal.ofReal_ne_top) (fun _ => ENNReal.ofReal_ne_top)
  letI : IsProbabilityMeasure P := cappedTranscriptLaw_probability μ ν _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q) A N
  letI : IsProbabilityMeasure Q := cappedTranscriptLaw_probability μ ν _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit r) A N
  change (hellingerAffinity P Q).toReal = _
  rw [ha,hellingerAffinity_finite_real,realFiniteAffinity]
  apply Finset.sum_congr rfl
  intro w _
  dsimp only [P,Q]
  rw [original_stopped_word_mass μ ν q A N hcap w,original_stopped_word_mass μ ν r A N hcap w,
    Real.sqrt_mul (mul_nonneg measureReal_nonneg (prefixCoefficient_nonneg μ q _ _))]
  exact sqrt_product_scale _ _ _ measureReal_nonneg (prefixCoefficient_nonneg μ q _ _)

end ThresholdHC.StoppingProgram
