import ThresholdHC.StoppingProgram.OrderedWeights
import ThresholdHC.CapIdentification.StoppedMatching

/-! The aggregated ordered weights are the actual seed-and-stopped-word
law, with the inactive root handled separately. -/

noncomputable section
open MeasureTheory
open scoped Classical ENNReal BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw)

theorem orderedStopMass_eq {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E) {N n : ℕ}
    (hcap : ∀ z, A.stop z ≤ N) (hn : 0 < n) (w : Fin n → Bool) :
    orderedStopMass ν A w = ν.real (stoppedSeedCell A w Set.univ) := by
  let S := stoppedSeedCell A w Set.univ
  have hS : MeasurableSet S := measurableSet_stoppedSeedCell A w Set.univ MeasurableSet.univ
  have he : orderedStopIndicator A w = S.indicator (fun _ => (1:ℝ)) := by
    funext r
    simp only [orderedStopIndicator,hn,true_and,completedStop_eq_iff A hcap,
      Set.indicator,S,stoppedSeedCell,Set.mem_ofPred_eq,Set.mem_univ,true_and]
  rw [orderedStopMass,he,integral_indicator hS,integral_const]
  simp only [smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ]
  rfl

theorem finite_word_projection_integral {R W : Type} [MeasurableSpace R] [Fintype W]
    [MeasurableSpace W] [MeasurableSingletonClass W] (P : Measure (R × W)) [IsFiniteMeasure P]
    (F : W → ℝ) :
    (∫ z, F z.2 ∂P) = ∑ w, P.real (Set.univ ×ˢ {w})*F w := by
  have hm : Measurable F := measurable_of_countable F
  have hi : Integrable F (P.map Prod.snd) := Integrable.of_bound hm.aestronglyMeasurable
    (∑ w, ‖F w‖) (Filter.Eventually.of_forall (fun w =>
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ w)))
  rw [← integral_map measurable_snd.aemeasurable hm.aestronglyMeasurable,integral_fintype hi]
  apply Finset.sum_congr rfl
  intro w _
  rw [Measure.real,Measure.map_apply measurable_snd (measurableSet_singleton w)]
  have he : (Prod.snd : R × W → W) ⁻¹' {w} = Set.univ ×ˢ {w} := by ext z; simp
  rw [he]
  rfl

theorem original_stopped_word_integral {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (q : SignLaw) (A : StoppedProcedure R E) (N : ℕ) (hcap : ∀ z, A.stop z ≤ N)
    (F : CappedWord N → ℝ) :
    (∫ z, F z.2 ∂cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit q) A N) =
      ∑ w : CappedWord N, ν.real (stoppedSeedCell A w.2 Set.univ)*
        prefixCoefficient μ q w.1.val (wordHeads w.2)*F w := by
  let P := cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit q) A N
  letI : IsProbabilityMeasure P := cappedTranscriptLaw_probability μ ν _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q) A N
  change (∫ z, F z.2 ∂P) = _
  rw [finite_word_projection_integral P F]
  apply Finset.sum_congr rfl
  intro w _
  change (cappedTranscriptLaw μ ν _ _ _ A N (Set.univ ×ˢ {w})).toReal*F w = _
  rw [cappedTranscriptLaw_cell μ ν _ _ _ (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit q) A N hcap w Set.univ MeasurableSet.univ,
    original_wordLikelihood_integral,ENNReal.toReal_mul]
  change ν.real (stoppedSeedCell A w.2 Set.univ)*
    (ENNReal.ofReal (prefixCoefficient μ q w.1.val (wordHeads w.2))).toReal*F w = _
  rw [ENNReal.toReal_ofReal (prefixCoefficient_nonneg μ q _ _)]

end ThresholdHC.StoppingProgram
