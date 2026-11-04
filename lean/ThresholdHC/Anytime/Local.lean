import ThresholdHC.ConfidenceProgram.MedianController
import ThresholdHC.Confidence.Model
import ThresholdHC.ConfidenceTransfer.Terminal

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.Anytime
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.BlindUpper
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceProgram ThresholdHC.Confidence
open ThresholdHC.StoppingProgram ThresholdHC.ConfidenceTransfer

theorem observable_event {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (E : Set (R × ProcessTape)) (hE : MeasurableSet E) :
    (experimentLaw μ A q) {z | (z.1.1,z.2) ∈ E} =
      (originalSimulationLaw μ A q) {z | (z.1,populationPath (A.policy z.1) z.2) ∈ E} := by
  have h := congrArg (fun P : Measure (R × ProcessTape) => P E) (original_observable_simulation_law μ A q)
  have hm : Measurable (fun z : R × Table => (z.1,populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun w => measurable_to_countable' (A.policy_measurable w)))
  change (experimentLaw μ A q) ((fun z => (z.1.1,z.2)) ⁻¹' E) =
    (originalSimulationLaw μ A q) ((fun z => (z.1,populationPath (A.policy z.1) z.2)) ⁻¹' E)
  simpa only [Measure.map_apply (measurable_fst.fst.prodMk measurable_snd) hE,Measure.map_apply hm hE] using h

/-- A pathwise-capped stage has completed after its last reserved flip
almost surely under the original hidden-gap experiment. -/
theorem cap_stops {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (N : ℕ) (hc : PathwiseCap A N) :
    ∀ᵐ z ∂originalSimulationLaw μ A q,
      A.policy z.1 (processHistory (populationPath (A.policy z.1) z.2) N) = none := by
  let E := {z : R × ProcessTape | A.policy z.1 (processHistory z.2 N) ≠ none}
  have hp : Measurable (fun z : R × List Bool => A.policy z.1 z.2) :=
    measurable_from_prod_countable_left (fun w => measurable_to_countable' (A.policy_measurable w))
  have hm : Measurable (fun z : R × ProcessTape => A.policy z.1 (processHistory z.2 N)) :=
    hp.comp (measurable_fst.prodMk ((measurable_processHistory_fixed N).comp measurable_snd))
  have hE : MeasurableSet E := (measurableSet_eq_fun hm measurable_const).compl
  have hzero : (experimentLaw μ A q) {z | (z.1.1,z.2) ∈ E} = 0 := by
    change (experimentLaw μ A q) {z | ¬ A.policy z.1.1 (processHistory z.2 N) = none} = 0
    rw [← ae_iff]
    filter_upwards [original_path_valid μ A q] with z hz
    by_contra he
    have hw := valid_path_continuation_work (A.policy z.1.1) z.2 hz N he
    have hp := hc z.1.1 z.2 hz
    have hN : (N:ℝ≥0∞)+1 ≤ N := by
      simpa only [ENNReal.ofReal_add (Nat.cast_nonneg N) zero_le_one,ENNReal.ofReal_natCast,ENNReal.ofReal_one] using hw.trans hp
    have h := ENNReal.toReal_mono (by finiteness : (N:ℝ≥0∞) ≠ ⊤) hN
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at h
    norm_num at h
  rw [observable_event μ A q E hE] at hzero
  have ha := ae_iff.mpr hzero
  filter_upwards [ha] with z hz
  exact hz

theorem clipped_error (M θ x : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ M) :
    |clipEstimate M x-θ| ≤ |x-θ| := by
  by_cases hx : x ≤ 0
  · rw [clipEstimate,min_eq_right (hx.trans (hθ.1.trans hθ.2)),max_eq_left hx]
    rw [zero_sub,abs_neg,abs_of_nonneg hθ.1,abs_of_nonpos (by linarith : x-θ ≤ 0)]
    linarith
  · by_cases hx' : x ≤ M
    · rw [clipEstimate,min_eq_right hx',max_eq_right (le_of_not_ge hx)]
    · rw [clipEstimate,min_eq_left (le_of_not_ge hx'),max_eq_right (hθ.1.trans hθ.2),
        abs_of_nonneg (sub_nonneg.mpr hθ.2),abs_of_nonneg (by linarith : 0 ≤ x-θ)]
      linarith

theorem hard_local_failure {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (N : ℕ) (M r δ : ℝ)
    (hc : PathwiseCap A N) (hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ M)
    (hf : failureProbability μ A q r ≤ ENNReal.ofReal δ) :
    (originalSimulationLaw μ A q) {z | r < |localValue M (outcome A N M z)-signMean μ q.val|} ≤ ENNReal.ofReal δ := by
  let θ := signMean μ q.val
  let E := {z : R × ProcessTape | r < |A.output z-θ|}
  have hE : MeasurableSet E := measurableSet_lt measurable_const ((A.output_measurable.sub_const θ).abs)
  have he := observable_event μ A q E hE
  change failureProbability μ A q r = (originalSimulationLaw μ A q)
    {z | r < |A.output (z.1,populationPath (A.policy z.1) z.2)-θ|} at he
  rw [he] at hf
  apply le_trans _ hf
  apply measure_mono_ae
  filter_upwards [cap_stops μ A q N hc] with z hz
  intro hbad

  have hclip := clipped_error M θ (A.output (z.1,populationPath (A.policy z.1) z.2)) hθ
  have hbad' : r < |clipEstimate M (A.output (z.1,populationPath (A.policy z.1) z.2))-θ| := by
    simpa only [localValue,outcome,observed,hz,Option.isSome_none,Bool.false_eq_true,ite_false] using hbad
  exact hbad'.trans_le hclip

end ThresholdHC.Anytime
