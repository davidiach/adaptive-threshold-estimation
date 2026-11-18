import LargeBudgetBounds
import LargeBudgetWitness

open MeasureTheory Real
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.OracleLower
open ThresholdHC.SharpRMS ThresholdHC.SharpRMS.LargeBudget

example : ∀ {n : ℕ} (pol : List Bool → Option ℕ) (s t : ℝ), 0<s → s<1 → t^2≤2/3 →
    let Q := fun a : ℝ => creationLaw (n:=n) pol (fun _ => s/2) (fun _ => (1+a)/2)
    pairedCost (Q 0) (Q t) (Q (-t)) ≤ -log (1-t^2*s^2)*∑ w, Q 0 w*workOf w :=
  @adaptive_reverse_cost

example : ∀ x : ℝ, |x|≤1 → 27401/10000 ≤
    log (1/8+29/4*(x-29/40)^2)+log (1/8+29/4*(x- -(29/40))^2)+11774928000/2595112129*x^2 := log_tests

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B r : ℝ), 25≤B → 0<r →
    4*(11774928000/2595112129+2*(29/4))*r^2-log (1-4*(29/40)^2/B)*B ≤ 27401/10000+2*(1-1/8) →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(r:ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(r:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(r:ℝ)) ≤ selectedMinimaxRisk μ B := @logarithmic_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17356166/100000000:ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17356166/100000000:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17356166/100000000:ℝ)) ≤ selectedMinimaxRisk μ B := @lower_25

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 100≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17623782/100000000:ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17623782/100000000:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*(17623782/100000000:ℝ)) ≤ selectedMinimaxRisk μ B := @lower_100

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], UniformBudget μ twentyFiveFlips 25 :=
  @twenty_five_budget

example : ∀ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) twentyFiveFlips q)
    (populationOutput twentyFiveFlips) (signMean (Measure.dirac fifthGap) q.val) ≤
    ENNReal.ofReal ((195454/1000000:ℝ)^2) := twenty_five_squared_risk

example : minimaxRisk (Measure.dirac fifthGap) 25 ≤ ENNReal.ofReal (195454/1000000:ℝ) := upper_25

example : ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*c) ≤ minimaxRisk μ B) → c ≤ 195454/1000000 := coefficient_upper

#print axioms twenty_five_budget
#print axioms twenty_five_squared_risk
#print axioms upper_25
#print axioms coefficient_upper
#print axioms adaptive_reverse_cost
#print axioms log_tests
#print axioms logarithmic_lower
#print axioms lower_25
#print axioms lower_100
