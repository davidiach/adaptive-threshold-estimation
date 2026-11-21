import ThresholdHC.HardBudget.Specification
import ThresholdHC.RareAboveTwo.Model

/-! Target statements for the hard-cap counterexamples: a single timeout
fallback, or one random seed shared by every stage, leaves a nonvanishing
error floor, while the independent fallback ladder does not.

Source: `research/2026-10-30-hard-budget-rms/NOTE.md`, section
`5. Necessary assumptions: counterexamples`. At `mu = delta_(1/2)` a fresh flip
reveals an iid Bernoulli sign; fix `rho = 1/4`. For dyadic `b >= 4` the base
takes `b/4` fresh observations and forms a clipped sample mean; independently,
with probability `p = 1/8`, it requests `4b` discarded observations before
returning. Its expected work is `3b/4 <= b` and its uncapped MSE is at most
`min(rho^2, 4 rho/b) = K(b)^2`; at `b = 1, 2` it uses the zero-work midpoint.
A single cap at `4b` followed by the midpoint on timeout has MSE
`p (rho/2)^2 = rho^2/32`, and reusing the same delay bit at every stage keeps
that floor. The summary is `docs/RESULTS.md`, section `Hard observation caps
for the RMS rates`: a single timeout fallback, or randomness shared across
stages, leaves a nonvanishing error floor.

* `RareRateStatement`: the explicit rate `K(b) = min(rho, 2 sqrt(rho/b))` at
  `rho = 1/4` meets the rate hypotheses of
  `HardBudget.ObservableFallbackStatement` with `M = 1/4`, and `32 C^2 K(B)^2`
  eventually drops below the floor `rho^2/32 = 1/512` for every `C`.
* `HardCapNecessityStatement`: one base family with one seed law at every stage
  meets the stage premise of `HardBudget.ObservableFallbackStatement` uniformly
  over the rare sign laws at the endpoint gap (`RarePremise`). With independent
  stages the fallback controller keeps the cap and the last-success output, and
  for `B >= 4` and every rare sign law has risk at most `32 K(B)^2`. A controller that feeds one seed to every stage
  also keeps the cap and the last-success output (on the constant seed array).
  Every estimator with that seed law whose output is the shared-seed ladder
  output (at any depth), and every estimator with the stage seed law whose
  output is one capped run of stage `j >= 2` (capped at `4 * 2^j`) with the
  midpoint on timeout, has squared risk at least `rho^2/32 = 1/512` at
  `theta = 0`.

Deviations from the source: the floors are lower bounds, not the exact values
`p (rho/2)^2` and `(rho/2)^2 p^(m-1)`; the independent controller gets the
bound `32 K(B)^2` of the general reduction instead of its exact MSE; the single
fallback is indexed by its cap `4 * 2^j` for `j >= 2`; and restarts on unused
flips of the same hidden coin are not formalized separately (the shared-seed
stages read disjoint coin labels). -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardCapNecessity
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.HardBudget ThresholdHC.RareAboveTwo

/-- The endpoint gap 1/2: a fresh flip reveals its coin's sign. -/
def halfGap : Gap := ⟨1/2, by norm_num⟩

/-- Every sign negative, so the target is theta = 0. -/
def zeroSigns : SignLaw := ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, zero_le_one⟩⟩

/-- K(b) = min(rho, 2 sqrt(rho/b)) at rho = 1/4, so K(b)^2 = min(rho^2, 4 rho/b). -/
def rareRate (b : ℝ) : ℝ := min (1/4) (2 * Real.sqrt ((1/4) / b))

/-- The stage premise of ObservableFallbackStatement with M = rho = 1/4, C = 1 and
f = rareRate, uniformly over every rare sign law at the endpoint gap. -/
def RarePremise {S : Type} [MeasurableSpace S] (base : ℕ → AdaptiveEstimator S) : Prop :=
  ∀ q : SignLaw, RarePrior (Measure.dirac halfGap) (1/4) q → ∀ j : ℕ,
    expectedWork (Measure.dirac halfGap) (base j) q ≤ stageAllowance j ∧
    squaredRisk (experimentLaw (Measure.dirac halfGap) (base j) q) (populationOutput (base j))
        (signMean (Measure.dirac halfGap) q.val) ≤
      ENNReal.ofReal (1^2 * (rareRate (stageAllowance j))^2)

/-- rareRate meets the rate hypotheses of ObservableFallbackStatement with M = 1/4, and
32 C^2 K(B)^2 eventually drops below the floor rho^2/32 = 1/512 for every C. -/
def RareRateStatement : Prop :=
  rareRate (1/2) = 1/4 ∧ (∀ b, 1/2 ≤ b → 0 ≤ rareRate b) ∧
  (∀ b b', 1/2 ≤ b → b ≤ b' → rareRate b ≤ Real.sqrt (b'/b) * rareRate b') ∧
  ∀ C : ℝ, ∃ B₀ : ℝ, 4 ≤ B₀ ∧ ∀ B : ℝ, B₀ ≤ B → 32 * C^2 * (rareRate B)^2 < 1/512

/-- One base family, with one seed law at every stage, meets the premise uniformly.
With independent stages, the controller of ObservableFallbackStatement has risk at most
32 K(B)^2 for B >= 4 and every rare sign law. A controller that feeds one seed to every
stage keeps the cap and the last-success output on the constant seed array. Every
estimator with that seed law and the shared-seed ladder output (any depth), and every
estimator with the stage seed law and the output of one capped run of stage j >= 2
(capped at 4 * 2^j) that falls back to the midpoint, has risk at least
rho^2/32 = 1/512 at theta = 0. -/
def HardCapNecessityStatement : Prop :=
  ∃ (S : Type) (_ : MeasurableSpace S) (base : ℕ → AdaptiveEstimator S),
    (∀ j, (base j).randomLaw = (base 0).randomLaw) ∧ RarePremise base ∧
    (∃ indep : ℝ → AdaptiveEstimator (ℕ → S), ∀ B : ℝ, 0 ≤ B →
      (indep B).randomLaw = Measure.infinitePi (fun j => (base j).randomLaw) ∧
      PathwiseCap (indep B) ⌊B⌋₊ ∧
      (∀ m : ℕ, (reservation m : ℝ) ≤ B → B < reservation (m+1) → ∀ r table,
        (indep B).output (r, populationPath ((indep B).policy r) table) =
          idealFallback (R := fun _ => S) base (1/4) r table (m+1)) ∧
      (4 ≤ B → ∀ q : SignLaw, RarePrior (Measure.dirac halfGap) (1/4) q →
        squaredRisk (experimentLaw (Measure.dirac halfGap) (indep B) q) (populationOutput (indep B))
          (signMean (Measure.dirac halfGap) q.val) ≤ ENNReal.ofReal (32 * (rareRate B)^2))) ∧
    (∃ shared : ℝ → AdaptiveEstimator S, ∀ B : ℝ, 0 ≤ B →
      (shared B).randomLaw = (base 0).randomLaw ∧ PathwiseCap (shared B) ⌊B⌋₊ ∧
      (B < 4 → ∀ r table, (shared B).output (r, populationPath ((shared B).policy r) table) = 1/8) ∧
      (∀ m : ℕ, (reservation m : ℝ) ≤ B → B < reservation (m+1) → ∀ r table,
        (shared B).output (r, populationPath ((shared B).policy r) table) =
          idealFallback (R := fun _ => S) base (1/4) (fun _ => r) table (m+1))) ∧
    (∀ (k : ℕ) (A : AdaptiveEstimator S), A.randomLaw = (base 0).randomLaw →
      (∀ r table, A.output (r, populationPath (A.policy r) table) =
        idealFallback (R := fun _ => S) base (1/4) (fun _ => r) table k) →
      ENNReal.ofReal (1/512) ≤
        squaredRisk (experimentLaw (Measure.dirac halfGap) A zeroSigns)
          (populationOutput A) (signMean (Measure.dirac halfGap) zeroSigns.val)) ∧
    ∀ j : ℕ, 2 ≤ j →
      (∃ A : AdaptiveEstimator S, A.randomLaw = (base j).randomLaw ∧ PathwiseCap A (stageCap j) ∧
        ∀ r table, A.output (r, populationPath (A.policy r) table) =
          (stageResult (base j) (stageCap j) (1/4) r table).getD (1/8)) ∧
      ∀ A : AdaptiveEstimator S, A.randomLaw = (base j).randomLaw →
        (∀ r table, A.output (r, populationPath (A.policy r) table) =
          (stageResult (base j) (stageCap j) (1/4) r table).getD (1/8)) →
        ENNReal.ofReal (1/512) ≤
          squaredRisk (experimentLaw (Measure.dirac halfGap) A zeroSigns)
            (populationOutput A) (signMean (Measure.dirac halfGap) zeroSigns.val)

end ThresholdHC.HardCapNecessity
