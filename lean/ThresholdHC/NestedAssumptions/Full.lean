import ThresholdHC.NestedAssumptions.Model
import ThresholdHC.NestedAssumptions.HardDesign

/-!
# The nested-simulation class and the transcribed Giles--Haji-Ali assumptions

Proofs of the five targets of `ThresholdHC.NestedAssumptions.Specification`
(`paper/v6/core.tex`, Corollary `cor:nested`, final sentence).
-/

noncomputable section
namespace ThresholdHC.NestedAssumptions
open MeasureTheory ProbabilityTheory Set
open ThresholdHC.Tier6 ThresholdHC.ObservedState ThresholdHC.ObservableSimulation
  ThresholdHC.ContinuousObserved

theorem nested_assumptions : NestedAssumptionsStatement :=
  fun _ hp => ⟨fun _ hδ => nested_bounded_density hp hδ, fun _ hq => nested_moment hp hq⟩

theorem uniform_constants : UniformConstantsStatement :=
  ⟨2, 1, 3, (3 : ℝ) ^ ((3 : ℝ) / 2), fun p hp =>
    ⟨(nested_assumptions p hp).1 1 one_pos, (nested_assumptions p hp).2 3 (by norm_num)⟩⟩

theorem hard_design_nested : HardDesignStatement :=
  fun h δ D s => hard_design_model h δ D s

theorem hard_design_law : HardDesignLawStatement :=
  fun h δ D s u => hard_design_binaryLaw h δ D s u

theorem nested_model_nonempty : NestedModelNonemptyStatement := by
  obtain ⟨D, -⟩ := uniform_design_exists ⟨1 / 8, by norm_num⟩ (δ := 1) one_pos
  exact ⟨_, hard_design_nested _ _ D (fun _ => true)⟩

end ThresholdHC.NestedAssumptions
