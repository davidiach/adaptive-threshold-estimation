import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.OracleLower.Model

/-! Target statements for the restricted settings in which the research note
`research/2026-11-17-rms-constants/rms-gap.tex` ("Narrowing the universal RMS
constant", 17 November 2026) finds the RMS coefficient exactly one sixth. The
package `README.md` (line 11) summarizes them: "The coefficient is exactly
$1/6$ for budgets through four, for protocols with at most three flips per
coin, and for the two classes with unlimited revisits described below."

* `SmallBudgetCoefficientStatement`: rms-gap.tex:23 and :98, the budget
  restricted to `1 ≤ B ≤ 4`. `OracleSmallBudgetCoefficientStatement` is the
  same restriction for both magnitude oracles. The note states the restriction
  for the ordinary model; for the oracles the support is
  sharp-unrestricted.tex:23 ("Both magnitude oracles have the same sharp
  constant"), since restricting the budgets keeps one sixth valid and the
  oracle endpoint `B = 4` lies in `[1, 4]`.
* `ThreeFlipCoefficientStatement`: rms-gap.tex:23 and :100-111, protocols with
  at most three flips per coin, including adaptive revisiting and interleaving.
* `RestrictedCoefficientStatement`: a conditional statement for any class of
  protocols that contains every four-fresh-flip protocol, and any set of
  budgets at least one that contains four. The preassigned local and the
  sign-symmetric classes of rms-gap.tex:130 and :143 are not defined in Lean.
  That they contain the four-flip witness is the paper's sentence at
  rms-gap.tex:145.

Each statement has the form of `SharpRMS.SharpCoefficientStatement` (the
oracle statement is two such forms, and the class statement is one under
hypotheses): a real coefficient `c` is valid at every gap law and every
admissible budget if and only if `c ≤ 1/6`. The note writes this as `inf R_μ(B)/ω = 1/6`, where
`ω = modulus μ (1 / Real.sqrt B)`; the forms agree because `ω > 0`. The proofs
are in `Restricted.lean`. They derive every lower bound from the all-protocol
theorem `SharpRMS.sharp_coefficient`, or from `SharpRMS.oracle_sharp_lower`
for the oracles, and do not formalize the note's class-specific arguments. -/
noncomputable section
namespace ThresholdHC.RestrictedRMS
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.OracleLower

/-- rms-gap.tex:23 and :98. With the budget restricted to `1 ≤ B ≤ 4`, one
sixth is still the largest coefficient valid at every gap law. Policies may
use arbitrary measurable private randomness, interleaving, revisits and
unbounded stopping. -/
def SmallBudgetCoefficientStatement : Prop :=
  ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≤ 4 →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ minimaxRisk μ B) ↔ c ≤ 1/6

/-- The same budget restriction with every magnitude revealed, and with each
fresh magnitude selected by the algorithm. -/
def OracleSmallBudgetCoefficientStatement : Prop :=
  ∀ c : ℝ,
    ((∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≤ 4 →
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ revealedMinimaxRisk μ B) ↔ c ≤ 1/6) ∧
    ((∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≤ 4 →
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ selectedMinimaxRisk μ B) ↔ c ≤ 1/6)

/-- Conditional statement for restricted settings. Let `C` be a class of
ordinary protocols that contains every estimator whose policy is
`freshPolicy 3` at every seed: four fresh coins, each flipped once, with any
seed space, seed law and output. Let `S` be a set of budgets, each at least
one, that contains four. Then one sixth is the largest coefficient valid at
every gap law and every budget in `S` for the minimax risk over `C`.

Lean verifies these hypotheses in two cases only, and derives both from this
statement: the three-flip class of `ThreeFlipCoefficientStatement` with every
budget `B ≥ 1`, and the budget restriction `1 ≤ B ≤ 4` of
`SmallBudgetCoefficientStatement` with every protocol. The preassigned local
experiments of rms-gap.tex:130 and the adaptively selected sign-symmetric
rules of rms-gap.tex:143 are not defined in Lean. That every such four-flip
estimator belongs to both classes follows from their descriptions there (any
seed and output; a one-flip tree is sign-symmetric), and rms-gap.tex:145
states it for the witness; it is not checked here. -/
def RestrictedCoefficientStatement : Prop :=
  ∀ (C : ∀ (R : Type) [MeasurableSpace R], AdaptiveEstimator R → Prop) (S : Set ℝ),
    (∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
      (∀ s, A.policy s = freshPolicy 3) → C R A) →
    (∀ B ∈ S, 1 ≤ B) → 4 ∈ S →
    ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), B ∈ S →
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤
        sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
          C R A ∧ UniformBudget μ A B ∧ r = maximalRMSRisk μ A}) ↔ c ≤ 1/6

/-- rms-gap.tex:23 and :100-111. Protocols that flip each coin at most three
times, with adaptive revisits, interleaving, arbitrary measurable private
randomness and unbounded stopping, at every budget `B ≥ 1`. A label is one
coin, with one gap and one sign. At seed `s` and outcome history `xs` the next
flip uses coin `policy s xs`; on a reachable history, the flip that produced
entry `i` of `xs` used coin `policy s (xs.take i)` (`histBefore` and
`pathProb` in `Statements2.lean`). The count below is therefore the number of
earlier flips of coin `j`. The condition is required at every seed and every
history, including unreachable ones, so this class is contained in the
paper's class. It still contains the four-fresh-flip protocols, and the lower
bound holds for every protocol, so the narrowing does not change the
conclusion. -/
def ThreeFlipCoefficientStatement : Prop :=
  ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤
      sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
        (∀ (s : R) (xs : List Bool) (j : ℕ), A.policy s xs = some j →
          (List.range xs.length).countP (fun i => decide (A.policy s (xs.take i) = some j)) < 3) ∧
        UniformBudget μ A B ∧ r = maximalRMSRisk μ A}) ↔ c ≤ 1/6

end ThresholdHC.RestrictedRMS
