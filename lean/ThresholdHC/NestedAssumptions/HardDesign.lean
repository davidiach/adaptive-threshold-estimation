import ThresholdHC.NestedAssumptions.Binary
import ThresholdHC.ContinuousObserved.UniformReal

/-!
# The hard sign-cell designs belong to the nested-simulation class

For a sign-cell design `D` with gap law `uniformGaps` and any sign array `s`, the half
conditional-mean magnitude at state `u` is exactly the gap `D.gap u`, whose law is
`uniformGaps`; its real law is `4 • Leb` on `(0, 1/4]`.
-/

noncomputable section
namespace ThresholdHC.NestedAssumptions
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.ObservedState ThresholdHC.ObservableSimulation
  ThresholdHC.ContinuousObserved

theorem hard_halfMagnitude (h : Gap) (δ : ℝ) (D : CellDesign uniformGaps h δ)
    (s : Fin D.count → Bool) (u : unitInterval) :
    |condMean (binaryLaw (stateParameter (CellDesign.queryDesign uniformGaps h δ D) s)) u| / 2 =
      (D.gap u : ℝ) := by
  rw [condMean_binaryLaw]
  change |binaryMean (D.gap u) (s (D.cell u))| / 2 = _
  rw [binary_mean_magnitude]
  ring

theorem hard_design_model (h : Gap) (δ : ℝ) (D : CellDesign uniformGaps h δ)
    (s : Fin D.count → Bool) :
    NestedModel (stateParameter (CellDesign.queryDesign uniformGaps h δ D) s) := by
  refine ⟨measurable_stateParameter _ s, ?_⟩
  have he : (fun u =>
      |condMean (binaryLaw (stateParameter (CellDesign.queryDesign uniformGaps h δ D) s)) u| / 2) =
        (fun d : Gap => (d : ℝ)) ∘ D.gap := by
    funext u
    exact hard_halfMagnitude h δ D s u
  rw [he, ← Measure.map_map measurable_subtype_coe D.gap_measurable, D.gap_law,
    uniformGaps_real_law]

theorem hard_design_binaryLaw (h : Gap) (δ : ℝ) (D : CellDesign uniformGaps h δ)
    (s : Fin D.count → Bool) (u : unitInterval) :
    binaryLaw (stateParameter (CellDesign.queryDesign uniformGaps h δ D) s) u =
      (bernoulliMeasure true false (gapParameter (s (D.cell u)) (D.gap u))).map binaryValue :=
  rfl

end ThresholdHC.NestedAssumptions
