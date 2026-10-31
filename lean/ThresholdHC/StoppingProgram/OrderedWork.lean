import ThresholdHC.StoppingProgram.OrderedRewards
import ThresholdHC.CriticalEntropy.ObservationInformation

/-! The actual hidden-coin experiment and the aggregated count flow have
exactly the same expected physical work for every sign prior. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 (Gap SignLaw)

theorem original_work_stopped_integral {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (q : SignLaw) (A : StoppedProcedure R E) (N : ℕ) (hcap : ∀ z, A.stop z ≤ N) :
    populationExpectedWork μ ν (gapParameter false) (gapParameter true) (signUnit q) A =
      ENNReal.ofReal (∫ z, (z.2.1.val:ℝ) ∂
        cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit q) A N) := by
  let P := cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit q) A N
  letI : IsProbabilityMeasure P := cappedTranscriptLaw_probability μ ν _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q) A N
  have hm : Measurable (fun z : R × CappedWord N => (z.2.1.val:ℝ)) :=
    (measurable_of_countable (fun w : CappedWord N => (w.1.val:ℝ))).comp measurable_snd
  have hi : Integrable (fun z : R × CappedWord N => (z.2.1.val:ℝ)) P :=
    Integrable.of_bound hm.aestronglyMeasurable N (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast Nat.le_of_lt_succ z.2.1.isLt))
  change _ = ENNReal.ofReal (∫ z, (z.2.1.val:ℝ) ∂P)
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))]
  simp only [ENNReal.ofReal_natCast]
  dsimp only [P]
  have htime : Measurable (fun z : R × CappedWord N => (z.2.1.val:ℝ≥0∞)) :=
    (measurable_of_countable (fun w : CappedWord N => (w.1.val:ℝ≥0∞))).comp measurable_snd
  rw [cappedTranscriptLaw,lintegral_map htime
    ((measurable_cappedTranscript A N).comp (measurable_populationInput _ _ _
      (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)))]
  exact lintegral_congr (fun z => capped_transcript_work A N _ (hcap _))

theorem orderedFlow_actual_work {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (q : SignLaw) (A : StoppedProcedure R E) (N : ℕ) (hcap : ∀ z, A.stop z ≤ N) :
    populationExpectedWork μ ν (gapParameter false) (gapParameter true) (signUnit q) A =
      ENNReal.ofReal (countMean μ q (orderedFlow ν A N).continueWeight) := by
  rw [original_work_stopped_integral μ ν q A N hcap]
  have he := original_stopped_word_integral μ ν q A N hcap (fun w => (w.1.val:ℝ))
  rw [he]
  have hs : (∑ w : CappedWord N, ν.real (stoppedSeedCell A w.2 Set.univ)*
      prefixCoefficient μ q w.1.val (wordHeads w.2)*(w.1.val:ℝ)) =
      stoppedReferenceSum ν A N (fun n k => n*prefixCoefficient μ q n k) := by
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hs,orderedFlow_work_moment μ ν q A N hcap]

end ThresholdHC.StoppingProgram
