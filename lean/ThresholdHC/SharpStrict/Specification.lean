import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.OracleLower.Model

/-! Target statements for strictness of the sharp universal RMS lower bound
away from the budget four. They use only the original experiment, risk and
modulus definitions. The proofs are in the other modules of this group. -/
noncomputable section
namespace ThresholdHC.SharpStrict
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.OracleLower

/-- For every gap law and every budget at least one other than four, the
minimax RMS risk is strictly larger than one sixth of the modulus. -/
def StrictSharpLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≠ 4 →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) < minimaxRisk μ B

/-- At each budget at least one other than four, one coefficient strictly
larger than one sixth works for every gap law simultaneously. -/
def StrictCoefficientStatement : Prop :=
  ∀ B : ℝ, 1 ≤ B → B ≠ 4 → ∃ c : ℝ, 1/6 < c ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ minimaxRisk μ B

/-- Equality in the sharp lower bound forces the budget four. -/
def SharpEqualityCaseStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B = ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) → B = 4

/-- At most four expected flips, an explicit bound for every gap law. It
exceeds one sixth exactly when the budget is below four. -/
def SmallBudgetLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 0 ≤ B → B ≤ 4 →
    ENNReal.ofReal (Real.sqrt ((10 - B) / 216)) ≤ minimaxRisk μ B

/-- Every critical point mass with flip bias below one has single-gap
minimax risk strictly above one sixth. -/
def CriticalStrictStatement : Prop :=
  ∀ (g : Gap) (B : ℝ), 2 * g.val < 1 → (2 * g.val) ^ 2 * B = 4 →
    ENNReal.ofReal (1/6 : ℝ) < minimaxRisk (Measure.dirac g) B

/-- The strict bound with every magnitude revealed, and with each fresh
magnitude selected by the algorithm. -/
def OracleStrictSharpLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≠ 4 →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) < revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) < selectedMinimaxRisk μ B

end ThresholdHC.SharpStrict
