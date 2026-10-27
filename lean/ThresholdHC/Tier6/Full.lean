import ThresholdHC.Tier6.Process
import ThresholdHC.Tier6.ModelReduction
import ThresholdHC.Tier6.HardPair
import ThresholdHC.Tier6.Testing
import ThresholdHC.Tier6.AlgorithmNonempty
import ThresholdHC.Tier6.AlgorithmRisk

noncomputable section
open MeasureTheory
namespace ThresholdHC.Tier6

theorem population_realization : PopulationRealizationStatement :=
  populationRealization_of_process process_realization

theorem budget_class_nonempty : BudgetClassNonemptyStatement :=
  budgetClassNonempty_of_realization population_realization

theorem adaptive_algorithm_lower_bound : AlgorithmLowerBoundStatement :=
  algorithmLowerBound_of_realization population_realization

theorem minimax_lower_bound : MinimaxLowerBoundStatement :=
  minimaxLowerBound_of_algorithm adaptive_algorithm_lower_bound

theorem minimaxRisk_le_one (μ : Measure Gap) [IsProbabilityMeasure μ]
    (B : ℝ) (hB : 0 ≤ B) : minimaxRisk μ B ≤ 1 := by
  apply le_trans ?_ (immediate_maximalRMSRisk_le_one population_realization μ)
  apply sInf_le
  refine ⟨Unit, inferInstance, immediateEstimator, ?_, rfl⟩
  intro q
  rw [immediate_expectedWork_zero population_realization]
  exact bot_le

theorem tier6_landmark : Tier6LandmarkStatement :=
  ⟨process_realization, population_realization, hard_pair_validity, hard_pair_separation,
    modulus_scaling, budget_hard_pair, two_point_risk_lower, budget_class_nonempty,
    adaptive_algorithm_lower_bound, minimax_lower_bound⟩

end ThresholdHC.Tier6
