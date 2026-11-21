import ThresholdHC.HardBudget.Words
import ThresholdHC.LargeBudgetRMS.Specification

/-! Target statement for the 20+5 revisit witness at the gap `1/5` with a hard
cap of 25 flips, in the original population experiment.

Source: `research/2026-11-17-rms-constants/README.md`, section
*The coefficient for budgets of at least 25* (the paragraphs on the 20-flip
pilot): flip 20 distinct coins and let `j` be the number of heads; for
`5 ≤ j ≤ 9` revisit five distinct coins that showed heads, for `11 ≤ j ≤ 15`
five that showed tails, and otherwise flip five fresh coins. The estimate
depends on `j` and on the head count among the final five flips, and its RMS
risk is at most `0.188087`. The research proofs are
`research/2026-11-17-rms-constants/RevisitWitness.lean` (`revisit_cap`,
`revisit_budget`, `revisit_squared_risk`) with the exact statements in
`AuditRevisit.lean`; the library record
`results/large-budget-rms-20261118/README.md` lists these files as not
promoted.

The labelling rule is stated about an arbitrary reader `L`, so this file
depends only on the original experiment, risk and budget definitions, the
deterministic stopping wrapper `HardBudget.stopAt` and the gap
`LargeBudgetRMS.fifthGap`. The minimax and coefficient corollaries of this
witness (`0.188087`) are weaker than the audited `LargeBudgetRMS` targets
`FifthGapUpperStatement` and `BracketUpperStatement` (`0.186752`) and are not
restated here. -/
noncomputable section
namespace ThresholdHC.RevisitUpper
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6

/-- The 20+5 labelling rule. Pilot flip `n` uses the new label `n`. After a
pilot word `v` with `j` heads and `k < 5` follow-up answers, the label is a
pilot coin that showed heads (`5 ≤ j ≤ 9`), a pilot coin that showed tails
(`11 ≤ j ≤ 15`), or otherwise the new label `20 + k`. Follow-up labels are
distinct. -/
def RevisitRule (L : List Bool → ℕ) : Prop :=
  (∀ xs : List Bool, xs.length < 20 → L xs = xs.length) ∧
  (∀ v w : List Bool, v.length = 20 → w.length < 5 →
    ((5 ≤ v.count true ∧ v.count true ≤ 9) → L (v ++ w) < 20 ∧ v[L (v ++ w)]? = some true) ∧
    ((11 ≤ v.count true ∧ v.count true ≤ 15) → L (v ++ w) < 20 ∧ v[L (v ++ w)]? = some false) ∧
    (¬(5 ≤ v.count true ∧ v.count true ≤ 9) → ¬(11 ≤ v.count true ∧ v.count true ≤ 15) →
      L (v ++ w) = 20 + w.length)) ∧
  (∀ v w w' : List Bool, v.length = 20 → w.length < 5 → w'.length < 5 →
    L (v ++ w) = L (v ++ w') → w.length = w'.length)

/-- Some deterministic estimator runs that rule, stopped at 25 flips, with
output a function of the pilot head count and the follow-up head count. It
makes at most 25 flips on every path, meets the budget 25 under every gap law,
and has worst RMS risk at most `0.188087` at the gap `1/5`. -/
def RevisitWitnessStatement : Prop :=
  ∃ (L : List Bool → ℕ) (A : AdaptiveEstimator Unit) (f : ℕ → ℕ → ℝ),
    RevisitRule L ∧
    (∀ r, A.policy r = HardBudget.stopAt 25 L) ∧
    (∀ x : ProcessTape, A.output ((), x) =
      f (((Proofs.fullHist (processPrefix 25 x)).take 20).count true)
        (((Proofs.fullHist (processPrefix 25 x)).drop 20).count true)) ∧
    HardBudget.PathwiseCap A 25 ∧
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ], UniformBudget μ A 25) ∧
    maximalRMSRisk (Measure.dirac LargeBudgetRMS.fifthGap) A ≤
      ENNReal.ofReal (188087/1000000 : ℝ)

end ThresholdHC.RevisitUpper
