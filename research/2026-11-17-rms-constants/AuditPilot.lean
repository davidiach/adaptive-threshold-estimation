import PilotWitness

open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.SharpRMS
open ThresholdHC.SharpRMS.LargeBudget ThresholdHC.SharpRMS.Pilot

example : HardBudget.PathwiseCap pilotEstimator 25 := pilot_cap

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], UniformBudget μ pilotEstimator 25 := @pilot_budget

example : ∀ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator q)
    (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) q.val) ≤
    ENNReal.ofReal ((186752/1000000:ℝ)^2) := pilot_squared_risk

example : (⨆ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator q)
    (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) q.val)) =
    ENNReal.ofReal ((348763093753675683898541718818533:ℝ)/10^34) := by
  rw [pilot_worst_squared]
  norm_num [endpoint]

example : minimaxRisk (Measure.dirac fifthGap) 25 ≤ ENNReal.ofReal (186752/1000000:ℝ) := pilot_upper_25

example : ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*c) ≤ minimaxRisk μ B) → c ≤ 186752/1000000 := pilot_coefficient_upper

#print axioms pilot_worst_squared
#print axioms pilot_cap
#print axioms pilot_budget
#print axioms pilot_squared_risk
#print axioms pilot_upper_25
#print axioms pilot_coefficient_upper
