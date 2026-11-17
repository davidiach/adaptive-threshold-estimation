import SharpUnrestricted
import SharpAdaptiveSimulation

open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.SharpRMS

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/6) ≤ minimaxRisk μ B := @unrestricted_minimax_lower

example : ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*c) ≤ minimaxRisk μ B) ↔ c ≤ 1/6 := universal_coefficient_iff

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*Real.sqrt (59/2100:ℝ)) ≤ minimaxRisk μ B :=
  @large_budget_minimax_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (g : Gap) (B : ℝ),
    ENNReal.ofReal (modulus μ g.val)*minimaxRisk (Measure.dirac g) B ≤ minimaxRisk μ B := @critical_gap_reduction

example : ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (g : Gap) (A : AdaptiveEstimator R) (q : SignLaw),
    expectedWork (Measure.dirac g) (sourceEstimator μ g A) q = expectedWork μ A (sourceTarget g q) :=
  @simulation_expected_work

example : ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (g : Gap) (A : AdaptiveEstimator R) (q : SignLaw),
    ENNReal.ofReal (modulus μ g.val) * rootMeanRisk (experimentLaw (Measure.dirac g) (sourceEstimator μ g A) q)
      (populationOutput (sourceEstimator μ g A)) (signMean (Measure.dirac g) q.val) =
    rootMeanRisk (experimentLaw μ A (sourceTarget g q)) (populationOutput A) (signMean μ (sourceTarget g q).val) :=
  @simulation_rms

#print axioms unrestricted_minimax_lower
#print axioms universal_coefficient_iff
#print axioms large_budget_minimax_lower
#print axioms critical_gap_reduction
#print axioms simulation_expected_work
#print axioms simulation_rms
