import MultiBiasBounds

open MeasureTheory Real
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.OracleLower
open ThresholdHC.SharpRMS.MultiBias

example : ∀ x : ℝ, |x|≤1 →
    tilt*target-25*(∑ i, log (cut i)) ≤ tilt*x^2+∑ i, pair i x := scalar_test

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B r : ℝ), 25≤B → 0<r →
    weightSum*(4*r^2-target)+price B≤price 25 →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*r) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*r) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*r) ≤ selectedMinimaxRisk μ B := @lower_of_price

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ThresholdHC.SharpRMS.LargeBudget.lowerForAll μ B
      (Real.sqrt (4*(175198/1000000:ℝ)^2+(price 25-price B)/weightSum)/2) := @lower_curve

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(175198/1000000:ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(175198/1000000:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(175198/1000000:ℝ)) ≤ selectedMinimaxRisk μ B := @lower_25

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 100≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17807955/100000000:ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17807955/100000000:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17807955/100000000:ℝ)) ≤ selectedMinimaxRisk μ B := @lower_100

#print axioms scalar_test
#print axioms lower_of_price
#print axioms lower_curve
#print axioms lower_25
#print axioms lower_100
