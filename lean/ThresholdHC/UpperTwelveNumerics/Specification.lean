import ThresholdHC.Statements2
import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.UpperDisagreement.ErrorSum
import ThresholdHC.UpperMixture.Full
import ThresholdHC.BlindUpper.CallLaw

/-! Target statements for the decimal bounds and the remarks of the appendix on
the upper constant 12 of the RMS law (`paper/v6/appendix-upper-constant.tex`,
`app:upper-12`).

* `CallCostDecimalStatement`: the bound `(1-r)∑_{j≥1} r^j C_j sqrt v_j < 5.19` in
  the proof of `eq:upper-12-cost` (part of `lem:upper-12-call`), stated on the
  series itself.
* `WrongSideDecimalStatement`: the bound `< 0.401` on the wrong-side early stops
  in the paragraph after `eq:upper-12-split`, which bounds the last sum of that
  equation for `eq:upper-12-moment`, on the expression and on the level sum of
  the early-stopping error terms.
* `SecondMomentDecimalStatement`: the bound `(2+sqrt 2)*89/50 + 41/100 < 6.49`
  in the proof of `eq:upper-12-moment` (part of `lem:upper-12-call`), on the
  expression and on the one-call second moment for every gap `0 < d ≤ 1/2`.
* `MixtureRemarkStatement`, `DyadicBatchStatement`, `ScaleFourBiasStatement`:
  the three remarks after the proof of `thm:upper-12` (the two-level mixture
  pays `9/2`, giving `sqrt((9/2)*174/5) ≈ 12.5`; the dyadic batch pays the
  factor `B/2^L < 8`, with supremum `8`, and for `B ≥ 1` the family
  `budgetEstimator B` keeps the budget `B` with RMS risk at most
  `sqrt(8*174/5)*ω(B^{-1/2})` (about `16.69`); the calibration at scale `B/4` pays
  `4`, and the squared bias of the level-`L` call is at most `λ` times
  `ω((B/4)^{-1/2})^2` with `1 ≤ λ < 2`).

Unlike the other upper-constant specifications, which use only the experiment,
budget, risk and modulus definitions of `Tier6.AlgorithmModel`, these
statements name the one-coin definitions `secondMomentK` (with its classifier
`classifyK`/`thrK` at `k1 = k2 = 1`), `pLevel` and `rLevel` of
`ThresholdHC.Statements2` and `ThresholdHC.Statements`, the early-stopping
error `UpperDisagreement.stopError`, the
families `UpperMixture.budgetMixture` and `BlindUpper.budgetEstimator`, the
level `BlindUpper.budgetLevel`, and the level-`L` call
(`BlindUpper.cutoffValue` under `BlindUpper.callMeasure`). Their definitions
are fingerprinted in `tools/definition_lock.json`. The remarks are stated for
these specific families: existence forms would be implied by the constant 12.
No lower bound on any risk is stated. The approximate values `5.182`, `5.185`
and `1.762` are not stated here. -/
noncomputable section
namespace ThresholdHC.UpperTwelveNumerics
open Finset MeasureTheory ThresholdHC.Tier6
open scoped ENNReal

/-- The offset `C_{j+1}` of the paper: `89/20`, `17/4`, then `399/100`. -/
def callOffset (j : ℕ) : ℝ := if j = 0 then 89/20 else if j = 1 then 17/4 else 399/100

/-- Term `j+1` of `(1-r) ∑_{j≥1} r^j C_j sqrt v_j`, with `v_j = 1 + j*log 2`;
the summand of `UpperCallCost.callCost_constant_le`. -/
def callCostTerm (j : ℕ) : ℝ :=
  (1 - rLevel) * rLevel ^ (j + 1) * (Real.sqrt (1 + ((j : ℝ) + 1) * Real.log 2) * callOffset j)

/-- `(1-r)∑_{j≥1} r^j C_j sqrt v_j < 5.19`. -/
def CallCostDecimalStatement : Prop :=
  Summable callCostTerm ∧ ∑' j, callCostTerm j < 519/100

/-- The wrong-side constant
`(1+sqrt 2)*(2+sqrt 2)^2/(4*13/10)*e^{-2}*sqrt 2/(4-sqrt 2)`. -/
def wrongSideConstant : ℝ :=
  (1 + Real.sqrt 2) * ((2 + Real.sqrt 2)^2 / (4*(13/10)) * Real.exp (-2) *
    (Real.sqrt 2 / (4 - Real.sqrt 2)))

/-- `< 0.401`, on the expression and on the wrong-side early stops. -/
def WrongSideDecimalStatement : Prop :=
  wrongSideConstant < 401/1000 ∧
  ∀ (L : ℕ) (d : ℝ), 0 < d →
    d * ∑ l ∈ range (L + 1),
        (UpperDisagreement.stopError l d + UpperDisagreement.stopError (l - 1) d) / pLevel l
      ≤ wrongSideConstant

/-- `< 6.49`, on the expression and on the one-call second moment (every `0 < d ≤ 1/2`). -/
def SecondMomentDecimalStatement : Prop :=
  (2 + Real.sqrt 2) * (89/50) + 41/100 < (649/100 : ℝ) ∧
  ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    d * secondMomentK 1 1 L d S ≤ (2 + Real.sqrt 2) * (89/50) + 41/100

/-- Remark: the two-level mixture pays `9/2`, giving `sqrt((9/2)(174/5)) ≈ 12.5`. -/
def MixtureRemarkStatement : Prop :=
  (1251/100 : ℝ) < Real.sqrt ((9/2) * (174/5)) ∧ Real.sqrt ((9/2) * (174/5)) < 1252/100 ∧
  ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    UniformBudget μ (UpperMixture.budgetMixture B) B ∧
    maximalRMSRisk μ (UpperMixture.budgetMixture B) ≤
      ENNReal.ofReal (Real.sqrt ((9/2) * (174/5)) * modulus μ (1 / Real.sqrt B))

/-- Remark: the dyadic batch pays the factor `B/2^L < 8`, with supremum `8`; for
`B ≥ 1` the family `budgetEstimator B` keeps the budget `B`, with RMS risk at most
`sqrt(8*174/5)*ω(B^{-1/2})` (about `16.69`). -/
def DyadicBatchStatement : Prop :=
  (∀ B : ℝ, 4 ≤ B → B / (2 : ℝ) ^ BlindUpper.budgetLevel B < 8) ∧
  (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 4 ≤ B ∧ 8 - ε < B / (2 : ℝ) ^ BlindUpper.budgetLevel B) ∧
  ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    UniformBudget μ (BlindUpper.budgetEstimator B) B ∧
    maximalRMSRisk μ (BlindUpper.budgetEstimator B) ≤
      ENNReal.ofReal (Real.sqrt (8 * (174/5)) * modulus μ (1 / Real.sqrt B))

/-- Remark: scale `B/4` pays `4`; the squared bias of the level-`L` call is at
most `λ ω((B/4)^{-1/2})^2`, `1 ≤ λ < 2`. -/
def ScaleFourBiasStatement : Prop :=
  ∀ B : ℝ, 4 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    1 ≤ B / (4 * (2:ℝ) ^ BlindUpper.budgetLevel B) ∧
    B / (4 * (2:ℝ) ^ BlindUpper.budgetLevel B) < 2 ∧
    ((∫ z, BlindUpper.cutoffValue (BlindUpper.budgetLevel B) z ∂BlindUpper.callMeasure μ q) -
        signMean μ q.val) ^ 2 ≤
      B / (4 * (2:ℝ) ^ BlindUpper.budgetLevel B) * modulus μ (1 / Real.sqrt (B / 4)) ^ 2 ∧
    modulus μ (1 / Real.sqrt (B / 4)) ^ 2 ≤ 4 * modulus μ (1 / Real.sqrt B) ^ 2

end ThresholdHC.UpperTwelveNumerics
