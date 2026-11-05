import ThresholdHC.ContinuousObserved.Reduction
import ThresholdHC.ContinuousObserved.BinaryMoments

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier6 ThresholdHC.ObservedState ThresholdHC.ObservableSimulation

theorem binary_mean_positive (d : Gap) (s : Bool) : 0 < binaryMean d s ↔ s = true := by
  simpa only [conditionalMean,binaryMean] using
    conditional_mean_positive (fun _ : Fin 1 => d) (fun _ : unitInterval => (0 : Fin 1))
      (fun _ => s) (0 : unitInterval)

theorem query_threshold_target {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) :
    volume.real {u : unitInterval |
      0 < ∫ b, binaryValue b ∂bernoulliMeasure true false (gapParameter (s (D.cell u)) (D.gap u))} =
        stateTarget D.cell s := by
  simp only [binary_mean,binary_mean_positive,stateTarget]

theorem query_gap_magnitude {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) (u : unitInterval) :
    |∫ b, binaryValue b ∂bernoulliMeasure true false (gapParameter (s (D.cell u)) (D.gap u))| / 2 =
      (D.gap u : ℝ) := by
  rw [binary_mean,binary_mean_magnitude]
  ring

end ThresholdHC.ContinuousObserved
