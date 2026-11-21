import ThresholdHC.HardBudget.Words
import ThresholdHC.RareAboveTwo.Model

/-! Target statements for the strict acquisition-feedback advantage over the
full global-rarity class at the two-point gap law with a total cap of two flips.

Source: `research/2026-10-27-nonlinear-population/lower/full_class-body.tex`,
Theorem `feedback:full-class` (section `sec:feedback-full-class`), with the
comparison class and its cap-two dominance argument of
`research/2026-10-27-nonlinear-population/lower/feedback.tex`
(section `sec:feedback-counterexample`), the exact coefficients of
`lower/full_class_certificate.json`, and the summary in
`research/2026-10-27-nonlinear-population/FINAL_REPORT.md`.

The gap law is `μ = (δ_{1/4} + δ_{1/8})/2` and the rarity level is `1/4`.
The risk is the worst mean squared error over every measurable sign law `q`
with `∫ q dμ ≤ 1/4`, in the original population experiment of
`ThresholdHC.Tier6` (private seed, iid hidden magnitudes and signs,
unrestricted coin labels, every flip charged).

* The feedback witness flips coin `0`; after a tail it flips the fresh coin `1`,
  after a head it revisits coin `0`. Its output is the rational table of
  `full_class-body.tex` in the word order `TT, TH, HT, HH`.
* The comparison class `NoninteractiveCapTwo` with `PathwiseCap A 2` is the
  seed-conditional normal form to which the paper's dominance step reduces a
  preselected independent local-acquisition design under the cap: after the
  first flip of coin `c`, either the second action stays on `c` or stops, or
  it never revisits `c` and whether a second flip happens does not depend on
  the first answer. Fresh labels may differ between the two branches. The
  paper's reduction from independently executed local policies to this form
  is not formalized; the cap holds on every valid path of every seed.
* `noninteractiveMinimax` is an infimum over that class; the class statement
  exhibits members, including genuine two-flip schedules, and bounds the
  infimum by `1/64`, so the comparison is not against an empty class. -/

noncomputable section
namespace ThresholdHC.TwoFlipFeedback
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget

def quarterGap : Gap := ⟨1/4, by norm_num⟩

def eighthGap : Gap := ⟨1/8, by norm_num⟩

/-- `μ = (δ_{1/4} + δ_{1/8})/2`. -/
def twoGapLaw : Measure Gap :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac quarterGap + (2⁻¹ : ℝ≥0∞) • Measure.dirac eighthGap

instance twoGapLaw_probability : IsProbabilityMeasure twoGapLaw :=
  ⟨by simp [twoGapLaw, ENNReal.inv_two_add_inv_two]⟩

/-- Worst mean squared error over every globally rare sign law, `∫ q dμ ≤ 1/4`. -/
def rareSquaredRisk {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) : ℝ≥0∞ :=
  ⨆ (q : SignLaw) (_ : RarePrior twoGapLaw (1/4) q),
    squaredRisk (experimentLaw twoGapLaw A q) (populationOutput A) (signMean twoGapLaw q.val)

/-- Seed-conditional normal form under a total cap of two, invariant under
relabeling fresh coins (`feedback.tex`, dominance paragraph). -/
def NoninteractiveCapTwo {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) : Prop :=
  ∀ (r : R) (c : ℕ), A.policy r [] = some c →
    (∀ b : Bool, A.policy r [b] = none ∨ A.policy r [b] = some c) ∨
    ((∀ b : Bool, A.policy r [b] ≠ some c) ∧
      (A.policy r [false]).isSome = (A.policy r [true]).isSome)

/-- Minimax worst mean squared error of the noninteractive cap-two class. -/
def noninteractiveMinimax : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    PathwiseCap A 2 ∧ NoninteractiveCapTwo A ∧ t = rareSquaredRisk A}

/-- Coin `0` first; after a tail the fresh coin `1`, after a head coin `0` again. -/
def feedbackLabel : List Bool → ℕ
  | [false] => 1
  | _ => 0

/-- The rational table of `full_class-body.tex` in the order `TT, TH, HT, HH`
(`true` is a head). Words that the witness never produces get `0`. -/
def feedbackOutput (w : Fin 2 → Option Bool) : ℝ :=
  match w 0, w 1 with
  | some false, some false => 26862477375/237281040413
  | some false, some true => 3223497285/24696819223
  | some true, some false => 1074499095/8589934592
  | some true, some true => 22564480995/146053120736
  | _, _ => 0

/-- The feedback witness has worst mean squared error below `15443/10^6`. -/
def FeedbackUpperStatement : Prop :=
  ∃ A : AdaptiveEstimator Unit,
    (∀ r, A.policy r = stopAt 2 feedbackLabel) ∧
    (∀ x : ProcessTape, A.output ((), x) = feedbackOutput (processPrefix 2 x)) ∧
    PathwiseCap A 2 ∧ ¬ NoninteractiveCapTwo A ∧
    rareSquaredRisk A < ENNReal.ofReal (15443/1000000)

/-- The class holds genuine two-flip schedules, and the infimum is finite. -/
def NoninteractiveClassStatement : Prop :=
  (∃ A : AdaptiveEstimator Unit, (∀ r, A.policy r = stopAt 2 (fun _ => 0)) ∧
      PathwiseCap A 2 ∧ NoninteractiveCapTwo A) ∧
  (∃ A : AdaptiveEstimator Unit, (∀ r, A.policy r = stopAt 2 (fun xs => xs.length)) ∧
      PathwiseCap A 2 ∧ NoninteractiveCapTwo A) ∧
  noninteractiveMinimax ≤ ENNReal.ofReal (1/64)

/-- Every member of the class has worst mean squared error at least
`1547585/10^8` (the uniform form of the lower bound). -/
def UniformLowerStatement : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    PathwiseCap A 2 → NoninteractiveCapTwo A →
    ENNReal.ofReal (1547585/100000000) ≤ rareSquaredRisk A

/-- The noninteractive minimax mean squared error exceeds `15475/10^6`, and it
is finite. -/
def NoninteractiveLowerStatement : Prop :=
  ENNReal.ofReal (15475/1000000) < noninteractiveMinimax ∧
  noninteractiveMinimax ≤ ENNReal.ofReal (1/64)

/-- The pinned feedback witness beats the noninteractive minimax by more than
`32/10^6`. -/
def SeparationStatement : Prop :=
  ∃ A : AdaptiveEstimator Unit,
    (∀ r, A.policy r = stopAt 2 feedbackLabel) ∧
    (∀ x : ProcessTape, A.output ((), x) = feedbackOutput (processPrefix 2 x)) ∧
    PathwiseCap A 2 ∧ ¬ NoninteractiveCapTwo A ∧
    rareSquaredRisk A + ENNReal.ofReal (32/1000000) < noninteractiveMinimax

end ThresholdHC.TwoFlipFeedback
