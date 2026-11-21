import ThresholdHC.TwoFlipFeedback.Specification

/-! Target statements for the dominance step of the strict acquisition-feedback
advantage at the two-point gap law with a total cap of two flips: the paper's
class of preselected, independently executed local designs reduces to the
seed-conditional normal form `NoninteractiveCapTwo` of
`ThresholdHC.TwoFlipFeedback`, and the lower bound and the separation hold for
that class itself.

Source: `research/2026-10-27-nonlinear-population/lower/feedback.tex`
(section `sec:feedback-counterexample`): the definition of the noninteractive
comparison class before Theorem `feedback:strict` and the dominance paragraph
after it; and `research/2026-10-27-nonlinear-population/lower/full_class-body.tex`,
Theorem `feedback:full-class` (section `sec:feedback-full-class`), which uses
that class and that dominance argument over the full rarity class.

* `ownBits pol c xs` lists the answers of coin `c` in the history `xs`: the
  answer at position `k` belongs to the coin that the policy chose at the
  history `xs.take k`.
* `LocalAcquisition A`: at every seed (shared and local seeds together) every
  coin has a continuation rule that reads only that coin's own answers. The
  policy stops exactly when every rule says stop, so no rule is cancelled
  because of another coin's answers, and it flips only a coin whose own rule
  asks for a flip. The order among active coins is free, so block-sequential
  and interleaved executions are both members. The condition is imposed at
  every finite history.
* `AlmostSureCap A n`: the total number of flips is at most `n` almost surely
  in the original experiment at every globally rare sign law, the parameter
  class `∫ q dμ ≤ 1/4` of the theorem.
* `localMinimax` is the infimum of the worst rare mean squared error
  `rareSquaredRisk` over the class with the almost-sure cap of two.
* The dominance step is stated in two forms: under a pathwise cap a local
  design is itself in the normal form; under the almost-sure cap almost every
  seed stops after two flips and is in the normal form at that seed. The
  paper's step that completes early stops to one of two full schedules is
  replaced by the direct six-shape Bayes bound of `ThresholdHC.TwoFlipFeedback`.
* The feedback witness is not a local design; it obeys both caps. -/

noncomputable section
namespace ThresholdHC.TwoFlipDominance
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget
open ThresholdHC.TwoFlipFeedback

/-- The answers of coin `c` in the history `xs`, in time order. -/
def ownBits (pol : List Bool → Option ℕ) (c : ℕ) (xs : List Bool) : List Bool :=
  ((List.range xs.length).filter (fun k => decide (pol (xs.take k) = some c))).filterMap
    (fun k => xs[k]?)

/-- Preselected local acquisition: at every seed, each coin has a continuation
rule on its own answers. The policy stops exactly when every coin's rule says
stop (no outcome-dependent cancellation) and flips only a coin whose own rule
asks for a flip. The order among active coins is free, so block-sequential and
interleaved executions are both members. -/
def LocalAcquisition {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) : Prop :=
  ∀ r : R, ∃ cont : ℕ → List Bool → Bool, ∀ xs : List Bool,
    (A.policy r xs = none ↔ ∀ c, cont c (ownBits (A.policy r) c xs) = false) ∧
    ∀ c, A.policy r xs = some c → cont c (ownBits (A.policy r) c xs) = true

/-- The total flips are at most `n` almost surely at every rare sign law. -/
def AlmostSureCap {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (n : ℕ) : Prop :=
  ∀ q : SignLaw, RarePrior twoGapLaw (1/4) q →
    ∀ᵐ z ∂experimentLaw twoGapLaw A q, totalProcessWork z.2 ≤ n

/-- Minimax worst mean squared error of the paper's noninteractive class. -/
def localMinimax : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    AlmostSureCap A 2 ∧ LocalAcquisition A ∧ t = rareSquaredRisk A}

/-- Dominance step, pathwise form: the design itself is in the normal form. -/
def PathwiseDominanceStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    PathwiseCap A 2 → LocalAcquisition A → NoninteractiveCapTwo A

/-- Dominance step, seed-conditional form under the almost-sure cap: almost
every seed stops after two flips and is in the normal form. -/
def SeedDominanceStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    AlmostSureCap A 2 → LocalAcquisition A →
    ∀ᵐ r ∂A.randomLaw,
      (∀ b b' : Bool, A.policy r [] ≠ none → A.policy r [b] ≠ none →
        A.policy r [b, b'] = none) ∧
      ∀ c : ℕ, A.policy r [] = some c →
        (∀ b : Bool, A.policy r [b] = none ∨ A.policy r [b] = some c) ∨
        ((∀ b : Bool, A.policy r [b] ≠ some c) ∧
          (A.policy r [false]).isSome = (A.policy r [true]).isSome)

/-- The pathwise cap implies the almost-sure cap; the class holds genuine
two-flip schedules; its infimum is finite. -/
def LocalClassStatement : Prop :=
  (∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
      PathwiseCap A 2 → AlmostSureCap A 2) ∧
  (∃ A : AdaptiveEstimator Unit, (∀ r, A.policy r = stopAt 2 (fun _ => 0)) ∧
      PathwiseCap A 2 ∧ LocalAcquisition A) ∧
  (∃ A : AdaptiveEstimator Unit, (∀ r, A.policy r = stopAt 2 (fun xs => xs.length)) ∧
      PathwiseCap A 2 ∧ LocalAcquisition A) ∧
  localMinimax ≤ ENNReal.ofReal (1/64)

/-- Every local design with the almost-sure cap of two has worst mean squared
error at least `1547585/10^8`. -/
def LocalUniformLowerStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    AlmostSureCap A 2 → LocalAcquisition A →
    ENNReal.ofReal (1547585/100000000) ≤ rareSquaredRisk A

/-- The minimax mean squared error of the paper's class exceeds `15475/10^6`,
and it is finite. -/
def LocalLowerStatement : Prop :=
  ENNReal.ofReal (15475/1000000) < localMinimax ∧ localMinimax ≤ ENNReal.ofReal (1/64)

/-- The pinned feedback witness obeys both caps, is not a local design, and
beats the minimax of the paper's class by more than `32/10^6`. -/
def LocalSeparationStatement : Prop :=
  ∃ A : AdaptiveEstimator Unit,
    (∀ r, A.policy r = stopAt 2 feedbackLabel) ∧
    (∀ x : ProcessTape, A.output ((), x) = feedbackOutput (processPrefix 2 x)) ∧
    PathwiseCap A 2 ∧ AlmostSureCap A 2 ∧ ¬ LocalAcquisition A ∧
    rareSquaredRisk A + ENNReal.ofReal (32/1000000) < localMinimax

end ThresholdHC.TwoFlipDominance
