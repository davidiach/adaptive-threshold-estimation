import ThresholdHC.ContinuousObserved.Density
import ThresholdHC.ContinuousObserved.StandardizedMoments
import ThresholdHC.ContinuousObserved.Target

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier6 ThresholdHC.ObservedState ThresholdHC.ObservableSimulation

def queryNormalizedMagnitude {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool)
    (u : unitInterval) : ℝ :=
  |∫ b, binaryValue b ∂bernoulliMeasure true false (gapParameter (s (D.cell u)) (D.gap u))| /
    Real.sqrt (variance binaryValue (bernoulliMeasure true false (gapParameter (s (D.cell u)) (D.gap u))))

theorem queryNormalizedMagnitude_eq {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) (u : unitInterval) :
    queryNormalizedMagnitude D s u = normalizedGap (D.gap u) := by
  rw [queryNormalizedMagnitude,binary_mean,binary_mean_magnitude,binary_variance]
  rfl

theorem query_normalized_density {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = uniformGaps) :
    volume.map (queryNormalizedMagnitude D s) =
      volume.withDensity (fun z => ENNReal.ofReal (normalizedDensity z)) := by
  have he : queryNormalizedMagnitude D s = (fun d : Gap => normalizedGap d) ∘ D.gap := by
    funext u
    exact queryNormalizedMagnitude_eq D s u
  have hm : Measurable (fun d : Gap => normalizedGap d) :=
    measurable_normalizedGap.comp measurable_subtype_coe
  rw [he,← Measure.map_map hm D.gap_measurable,hl,normalizedGap_density]

theorem query_normalized_moment {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool)
    (hd : ∀ u, (D.gap u : ℝ) ≤ 1 / 4) (u : unitInterval) {q : ℝ} (hq : 0 ≤ q) :
    (∫ b, (|binaryValue b -
      ∫ a, binaryValue a ∂bernoulliMeasure true false (gapParameter (s (D.cell u)) (D.gap u))| /
        Real.sqrt (variance binaryValue
          (bernoulliMeasure true false (gapParameter (s (D.cell u)) (D.gap u))))) ^ q
      ∂bernoulliMeasure true false (gapParameter (s (D.cell u)) (D.gap u))) ≤ (3 : ℝ) ^ (q / 2) := by
  rw [binary_mean]
  exact binary_standardized_moment (D.gap u) (hd u) (s (D.cell u)) hq

end ThresholdHC.ContinuousObserved
