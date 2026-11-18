import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.OracleLower.Model

/-! Target statements for the coefficient of the RMS lower bound at budgets of
at least 25. They use only the original experiment, risk and modulus
definitions. The proofs are in the other modules of this directory. -/
noncomputable section
namespace ThresholdHC.LargeBudgetRMS
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.OracleLower

/-- The gap one fifth, the critical gap of the budget 25. -/
def fifthGap : Gap := ⟨1/5, by norm_num⟩

/-- For every gap law and every budget at least 25, the minimax RMS risk is at
least 0.175198 times the modulus, with or without a magnitude oracle. Policies
may use arbitrary measurable private randomness, interleaving, revisits and
unbounded stopping. -/
def BracketLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * (175198/1000000 : ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * (175198/1000000 : ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * (175198/1000000 : ℝ)) ≤ selectedMinimaxRisk μ B

/-- The same three bounds with the coefficient 0.17807955 once the budget is
at least 100. -/
def HundredLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 100 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * (17807955/100000000 : ℝ)) ≤ minimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * (17807955/100000000 : ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * (17807955/100000000 : ℝ)) ≤ selectedMinimaxRisk μ B

/-- At the gap one fifth and the budget 25, some policy has worst-case RMS risk
at most 0.186752. -/
def FifthGapUpperStatement : Prop :=
  minimaxRisk (Measure.dirac fifthGap) 25 ≤ ENNReal.ofReal (186752/1000000 : ℝ)

/-- No coefficient above 0.186752 is valid for every gap law at every budget
of at least 25. -/
def BracketUpperStatement : Prop :=
  ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ minimaxRisk μ B) → c ≤ 186752/1000000

end ThresholdHC.LargeBudgetRMS
