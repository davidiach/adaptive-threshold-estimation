import ThresholdHC.ObservableSimulation.OriginalExperiment
import ThresholdHC.StoppingProgram.TruncatedPrefix

/-! The geometric fallback reduction for deterministic authorized budgets.
The statement fixes the stopped experiment and the observable result on
every private seed and persistent table of coin flips. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation

def stageAllowance (j : ℕ) : ℕ := 2^j
def stageCap (j : ℕ) : ℕ := 4*stageAllowance j
def reservation (j : ℕ) : ℕ := 4*(2^(j+1)-1)

/-- A path is admissible when an observation is present exactly when the
policy requested one. This quantifies over every private seed and such path. -/
def PathwiseCap {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (n : ℕ) : Prop :=
  ∀ (r : R) (x : ProcessTape), (∀ k, (x k).isSome = (A.policy r (processHistory x k)).isSome) →
    totalProcessWork x ≤ n

def clipEstimate (M x : ℝ) : ℝ := max 0 (min M x)

/-- The intended output for a stage on an independent, complete local run.
The outcome at exactly the last paid observation counts as a success. -/
def stageResult {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (n : ℕ)
    (M : ℝ) (r : R) (table : ℕ → ℕ → Bool) : Option ℝ :=
  let x := populationPath (A.policy r) table
  if A.policy r (processHistory x n) = none then some (clipEstimate M (A.output (r,x))) else none

def idealFallback {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]
    (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (r : ∀ j, R j) (table : ℕ → ℕ → Bool) :
    ℕ → ℝ
  | 0 => M/2
  | j+1 => (stageResult (base j) (stageCap j) M (r j) (fun c => table (Nat.pair j c))).getD
      (idealFallback base M r table j)

/-- One controller fixed before the law and sign prior, with the exact
last-success output, disjoint stage inputs, a cap on every valid path and
the original experiment's squared risk. A stage may spend its reserved
flips after success, which preserves its output and the pathwise budget. -/
def ObservableFallbackStatement : Prop :=
  ∀ (R : ℕ → Type) [∀ j, MeasurableSpace (R j)] (base : ∀ j, AdaptiveEstimator (R j))
    (M : ℝ), 0 ≤ M → ∃ controller : ℝ → AdaptiveEstimator (∀ j, R j),
    ∀ B : ℝ, 0 ≤ B →
    (controller B).randomLaw = Measure.infinitePi (fun j => (base j).randomLaw) ∧
    PathwiseCap (controller B) ⌊B⌋₊ ∧
    (B < 4 → PathwiseCap (controller B) 0 ∧ ∀ r table,
      (controller B).output (r,populationPath ((controller B).policy r) table) = M/2) ∧
    (∀ m : ℕ, (reservation m : ℝ) ≤ B → B < reservation (m+1) → ∀ r table,
      (controller B).output (r,populationPath ((controller B).policy r) table) =
        idealFallback base M r table (m+1)) ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (C : ℝ) (f : ℝ → ℝ),
      4 ≤ B → 0 ≤ signMean μ q.val → signMean μ q.val ≤ M → 1/2 ≤ C →
      (∀ b, 1/2 ≤ b → 0 ≤ f b) → f (1/2) = M →
      (∀ b b', 1/2 ≤ b → b ≤ b' → f b ≤ Real.sqrt (b'/b)*f b') →
      (∀ j, expectedWork μ (base j) q ≤ stageAllowance j ∧
        squaredRisk (experimentLaw μ (base j) q) (populationOutput (base j)) (signMean μ q.val) ≤
          ENNReal.ofReal (C^2*(f (stageAllowance j))^2)) →
      squaredRisk (experimentLaw μ (controller B) q) (populationOutput (controller B)) (signMean μ q.val) ≤
        ENNReal.ofReal (32*C^2*(f B)^2)

end ThresholdHC.HardBudget
