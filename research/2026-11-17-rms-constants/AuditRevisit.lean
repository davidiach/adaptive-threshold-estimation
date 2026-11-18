import RevisitWitness

open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.SharpRMS
open ThresholdHC.SharpRMS.LargeBudget ThresholdHC.SharpRMS.Revisit

example : HardBudget.PathwiseCap revisitEstimator 25 := revisit_cap

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], UniformBudget μ revisitEstimator 25 := @revisit_budget

example : ∀ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) revisitEstimator q)
    (populationOutput revisitEstimator) (signMean (Measure.dirac fifthGap) q.val) ≤
    ENNReal.ofReal ((188087/1000000:ℝ)^2) := revisit_squared_risk

example : minimaxRisk (Measure.dirac fifthGap) 25 ≤ ENNReal.ofReal (188087/1000000:ℝ) := revisit_upper_25

example : ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*c) ≤ minimaxRisk μ B) → c ≤ 188087/1000000 := revisit_coefficient_upper

#print axioms revisit_cap
#print axioms revisit_budget
#print axioms revisit_squared_risk
#print axioms revisit_upper_25
#print axioms revisit_coefficient_upper
