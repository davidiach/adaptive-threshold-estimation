import ThresholdHC.Anytime.Local
import ThresholdHC.Anytime.Spending
import ThresholdHC.Anytime.IntervalAlgebra
import ThresholdHC.HardBudget.Inputs

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.Anytime
open ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.ConfidenceProgram ThresholdHC.Confidence
open ThresholdHC.ObservableSimulation

variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

/-- One common private-seed and coin-table law serves every observation budget. -/
def streamLaw (μ : Measure Gap) (base : ∀ j, AdaptiveEstimator (R j)) (q : SignLaw) :
    Measure ((∀ j, R j) × Table) := originalSimulationLaw μ (estimator base 0 0) q

instance streamLaw_probability (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ j, AdaptiveEstimator (R j)) (q : SignLaw) : IsProbabilityMeasure (streamLaw μ base q) := by
  unfold streamLaw originalSimulationLaw estimator
  infer_instance

/-- All running intersections cover the parameter on a single event.
Coverage is therefore preserved after any data-dependent choice of stage. -/
theorem all_stage_coverage (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ j, AdaptiveEstimator (R j)) (q : SignLaw) (M : ℝ) (radius : ℕ → ℝ) {δ : ℝ}
    (hd : 0 ≤ δ) (hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ M)
    (hcap : ∀ j, PathwiseCap (base j) (stageCap j))
    (hf : ∀ j, failureProbability μ (base j) q (radius j) ≤ ENNReal.ofReal (stageFailure δ j)) :
    (streamLaw μ base q) {z | ∃ k, ¬ ((tableInterval base M radius z.1 z.2 k).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (tableInterval base M radius z.1 z.2 k).2)} ≤ ENNReal.ofReal δ := by
  let θ := signMean μ q.val
  let X (j : ℕ) (z : R j × Table) := localValue M (outcome (base j) (stageCap j) M z)
  let E (j : ℕ) := {z : R j × Table | radius j < |X j z-θ|}
  have hE (j : ℕ) : MeasurableSet (E j) := measurableSet_lt measurable_const
    ((((measurable_localValue M).comp (measurable_outcome (base j) (stageCap j) M)).sub_const θ).abs)
  let Bad (j : ℕ) := {z : (∀ j, R j) × Table | stageInputs z j ∈ E j}
  have hBad (j) : (streamLaw μ base q) (Bad j) ≤ ENNReal.ofReal (stageFailure δ j) := by
    let P (j) := originalSimulationLaw μ (base j) q
    let _ (j) : IsProbabilityMeasure (P j) := by dsimp [P,originalSimulationLaw]; infer_instance
    have hp := stageInputs_preserving base M 0 μ q
    have hcoord := (measurePreserving_eval_infinitePi P j).comp hp
    change (originalSimulationLaw μ (estimator base M 0) q) ((Function.eval j ∘ stageInputs) ⁻¹' E j) ≤ _
    rw [hcoord.measure_preimage (hE j).nullMeasurableSet]
    exact hard_local_failure μ (base j) q (stageCap j) M (radius j) (stageFailure δ j) (hcap j) hθ (hf j)
  apply (measure_mono (t := ⋃ j, Bad j) ?_).trans (simultaneous_coverage _ Bad hd hBad)
  rintro z ⟨k,hbad⟩
  by_contra hnone
  have hs (j) : |X j (stageInputs z j)-θ| ≤ radius j := by
    apply le_of_not_gt
    intro h
    exact hnone (mem_iUnion.mpr ⟨j,h⟩)
  apply hbad
  apply interval_coverage base M θ radius z.1 z.2 hθ _ k
  intro j
  rw [stageResult_value]
  exact hs j

theorem stopped_stage_coverage (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ j, AdaptiveEstimator (R j)) (q : SignLaw) (M : ℝ) (radius : ℕ → ℝ) {δ : ℝ}
    (hd : 0 ≤ δ) (hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ M)
    (hcap : ∀ j, PathwiseCap (base j) (stageCap j))
    (hf : ∀ j, failureProbability μ (base j) q (radius j) ≤ ENNReal.ofReal (stageFailure δ j))
    (τ : ((∀ j, R j) × Table) → ℕ) :
    (streamLaw μ base q) {z | ¬ ((tableInterval base M radius z.1 z.2 (τ z)).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (tableInterval base M radius z.1 z.2 (τ z)).2)} ≤ ENNReal.ofReal δ :=
  (measure_mono (t := {z | ∃ k, ¬ ((tableInterval base M radius z.1 z.2 k).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (tableInterval base M radius z.1 z.2 k).2)})
    (fun z hz => ⟨τ z,hz⟩)).trans (all_stage_coverage μ base q M radius hd hθ hcap hf)

end ThresholdHC.Anytime
