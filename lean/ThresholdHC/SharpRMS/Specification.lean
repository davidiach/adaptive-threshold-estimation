import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.OracleLower.Model

/-! Target statements for the sharp universal RMS lower coefficient. They use
only the original experiment, risk and modulus definitions. The proofs are in
the other modules of this directory. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.OracleLower

/-- The gap one half: one flip reveals the sign. -/
def halfGap : Gap := ⟨1/2, by norm_num⟩

/-- For every gap law and every budget at least one, the minimax RMS risk is
at least one sixth of the modulus. Policies may use arbitrary measurable
private randomness, interleaving, revisits and unbounded stopping. -/
def SharpLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) ≤ minimaxRisk μ B

/-- One sixth is the largest coefficient valid at every gap law and budget. -/
def SharpCoefficientStatement : Prop :=
  ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ minimaxRisk μ B) ↔ c ≤ 1/6

/-- Four fresh flips attain one sixth at the gap one half and budget four. -/
def SharpEndpointStatement : Prop :=
  minimaxRisk (Measure.dirac halfGap) 4 = ENNReal.ofReal (1/6 : ℝ)

/-- A strictly larger coefficient for every gap law once the budget is at least 25. -/
def LargeBudgetLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * Real.sqrt (59/2100 : ℝ)) ≤ minimaxRisk μ B

/-- The risk under any gap law dominates the modulus at a gap times the risk
under the point mass at that gap, at the same budget. -/
def GapReductionStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (g : Gap) (B : ℝ),
    ENNReal.ofReal (modulus μ g.val) * minimaxRisk (Measure.dirac g) B ≤ minimaxRisk μ B

/-- The sharp lower bound with every magnitude revealed, and with each fresh
magnitude selected by the algorithm. -/
def OracleSharpLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) ≤ selectedMinimaxRisk μ B

def OracleLargeBudgetLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * Real.sqrt (59/2100 : ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * Real.sqrt (59/2100 : ℝ)) ≤ selectedMinimaxRisk μ B

def OracleEndpointStatement : Prop :=
  revealedMinimaxRisk (Measure.dirac halfGap) 4 = ENNReal.ofReal (1/6 : ℝ) ∧
  selectedMinimaxRisk (Measure.dirac halfGap) 4 = ENNReal.ofReal (1/6 : ℝ)

end ThresholdHC.SharpRMS
