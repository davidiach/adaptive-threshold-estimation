import ThresholdHC.ArbitraryLawController.Intervals
import ThresholdHC.Anytime.Coverage
import ThresholdHC.ArbitraryLawAdaptation.TailBlockReader

/-!
# The unknown-law confidence sequence: target statements

Source: `docs/UNKNOWN_LAW_CONFIDENCE.md`, the theorem at the top of the note
(lines 8-13), section One stage (lines 21-50) and section All authorized
budgets (lines 52-63); scope as in `docs/SECONDARY_CLAIMS.md`, inventory
item 1 (The simpler unknown-law confidence sequence).

Stage `j` has cap `c_j = 4 * 2^j` (`HardBudget.stageCap`). It takes
`n = floor(sqrt c_j)` fresh items and `m = floor(c_j / n)` flips on each. For
`0 < e` the count `H(k,e)` is the least natural `H` with
`k * ceil(log2(1/e)) <= 2 H^2`. With `tau = 1/n`, `r = H(m,tau)/m` and
`a = H(n, delta_j/3)/n`, where `delta_j = delta/((j+1)(j+2))`, an item is
positive when its observed head fraction is strictly above `1/2 + r` and
negative when it is strictly below `1/2 - r`. The stage interval is
`[p+ - a - tau, 1 - p- + a + tau]` intersected with `[0,1]`, with hats on the
two sample fractions. The reported interval at budget `B` intersects `[0,u]`
with every stage interval completed within the budget.

Formal reading. The population is the repository's observable simulation:
a private seed (here trivial) and a persistent table of iid coin tapes under
`streamLaw`, as for `ArbitraryLawController.arbitrary_law_controller`. The
gap law `mu` on `Gap = (0,1/2]` is arbitrary and the sign probability
`q : SignLaw` may depend measurably on the gap; `theta = signMean mu q`.
Each stage is a `LearnedStage` with no pilot whose continuation flips the
items one after another; item `i` of stage `j` is the coin
`Nat.pair j (Nat.pair 1 (Nat.pair i 0))`. The supplied bound `u` is an
arbitrary real: coverage assumes `theta <= u`, and the case `u = 1` is stated
separately with no hypothesis. Width is `2 * Anytime.halfWidth`, that is
`max 0 (upper - lower)`, and the stage bound `P(D <= 2r) + 3a + 3tau` is
stated at every completed stage. Width tending to zero is split into the
deterministic limit of the stage bound and the pathwise limit of the
reported half-width on the success event.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.UnknownLawConfidence
open ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.ObservableSimulation
open ThresholdHC.ArbitraryLawAdaptation

/-- `H(k,e)`: the least natural `H` with `k * ceil(log2(1/e)) <= 2 H^2`. -/
def hoeffdingCount (k : ℕ) (e : ℝ) : ℕ :=
  sInf {H : ℕ | k * ⌈Real.logb 2 (1 / e)⌉₊ ≤ 2 * H ^ 2}

/-- `n = floor(sqrt c_j)` items at stage `j`. -/
def itemCount (j : ℕ) : ℕ := Nat.sqrt (stageCap j)

/-- `m = floor(c_j / n)` flips on each item. -/
def flipCount (j : ℕ) : ℕ := stageCap j / itemCount j

/-- `tau = 1/n`. -/
def tolerance (j : ℕ) : ℝ := 1 / (itemCount j : ℝ)

/-- `r = H(m,tau)/m`. -/
def radius (j : ℕ) : ℝ := (hoeffdingCount (flipCount j) (tolerance j) : ℝ) / flipCount j

/-- `a = H(n, delta_j/3)/n`. -/
def sampling (δ : ℝ) (j : ℕ) : ℝ :=
  (hoeffdingCount (itemCount j) (Anytime.stageFailure δ j / 3) : ℝ) / itemCount j

/-- Items `i < n` in turn, `m` flips each; item `i` is the coin `Nat.pair i 0`. -/
def stageReader (j : ℕ) : Reader :=
  seqReader (fun _ => flipCount j) (fun _ _ => 0) (itemCount j)

/-- Observed head fraction of item `i` in the stage word. -/
def itemFraction (j i : ℕ) (w : List Bool) : ℝ :=
  ((seqWord (fun _ => flipCount j) i w).count true : ℝ) / flipCount j

/-- Items declared positive. -/
def positiveCount (j : ℕ) (w : List Bool) : ℕ :=
  ((Finset.range (itemCount j)).filter (fun i => 1 / 2 + radius j < itemFraction j i w)).card

/-- Items declared negative. -/
def negativeCount (j : ℕ) (w : List Bool) : ℕ :=
  ((Finset.range (itemCount j)).filter (fun i => itemFraction j i w < 1 / 2 - radius j)).card

/-- `I_j = [p+ - a - tau, 1 - p- + a + tau]` intersected with `[0,1]`. -/
def stageInterval (δ : ℝ) (j : ℕ) (w : List Bool) : ℝ × ℝ :=
  (max 0 ((positiveCount j w : ℝ) / itemCount j - sampling δ j - tolerance j),
   min 1 (1 - (negativeCount j w : ℝ) / itemCount j + sampling δ j + tolerance j))

/-- No pilot; the item flips are the continuation, so the interval sees the word. -/
def stage (δ : ℝ) (j : ℕ) : LearnedStage Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  pilotCost := 0
  continuationCost := itemCount j * flipCount j
  depth := 0
  pilot := fun _ => 0
  upper := fun _ _ => 1
  upper_nonneg := fun _ _ => zero_le_one
  upper_zero := fun _ => rfl
  continuation := fun _ _ => stageReader j
  continuation_measurable := fun _ _ => measurable_const
  interval := fun _ _ w => stageInterval δ j w
  interval_measurable := fun _ _ => measurable_const

/-- The private seed is trivial. -/
abbrev Seed := ℕ → Unit

/-- The controller at integer budget `B`, reporting the upper or lower endpoint. -/
def controller (δ u : ℝ) (B : ℕ) (upper : Bool) : AdaptiveEstimator Seed :=
  ArbitraryLawController.endpoint (R := fun _ => Unit) (stage δ) u (stageCount (B : ℝ)) upper

/-- The reported interval `J(B)` as a function of the seed and the coin table. -/
def interval (δ u : ℝ) (B : ℕ) (z : Seed × Table) : ℝ × ℝ :=
  ArbitraryLawController.observedInterval (R := fun _ => Unit) (stage δ) u
    (stageCount (B : ℝ)) z

/-- One common seed and coin-table law serves every budget. -/
def streamLaw (μ : Measure Gap) (q : SignLaw) (δ : ℝ) : Measure (Seed × Table) :=
  Anytime.streamLaw (R := fun _ => Unit) μ (fun j => (stage δ j).endpoint false) q

/-- The stage bound `P(D <= 2r) + 3a + 3tau`. -/
def widthBound (μ : Measure Gap) (δ : ℝ) (j : ℕ) : ℝ :=
  μ.real {d : Gap | (d : ℝ) ≤ 2 * radius j} + 3 * sampling δ j + 3 * tolerance j

/-- Coverage at every integer budget and the stage bound at every completed stage. -/
def successEvent (μ : Measure Gap) (q : SignLaw) (δ u : ℝ) : Set (Seed × Table) :=
  {z | (∀ B : ℕ, (interval δ u B z).1 ≤ signMean μ q.val ∧
        signMean μ q.val ≤ (interval δ u B z).2) ∧
    ∀ B j : ℕ, j < stageCount (B : ℝ) →
      2 * Anytime.halfWidth (interval δ u B z) ≤ widthBound μ δ j}

/-- Budget caps, prefix compatibility, nesting, range in `[0,u]`, the law
identity, simultaneous coverage with probability at least `1 - delta` (for a
supplied `u >= theta`, and for `u = 1` with no hypothesis), the limit of the
stage bound, and the pathwise limit of the half-width on the success event. -/
def UnknownLawConfidenceStatement : Prop :=
  ∀ {δ : ℝ} (u : ℝ), 0 < δ → δ < 1 →
    (∀ B : ℕ, ∀ upper : Bool, PathwiseCap (controller δ u B upper) B) ∧
    (∀ B C : ℕ, B ≤ C → ∀ (upper upper' : Bool) (r : Seed) (xs : List Bool),
      xs.length < ArbitraryLawController.spent (R := fun _ => Unit) (stage δ)
        (stageCount (B : ℝ)) →
      (controller δ u C upper').policy r xs = (controller δ u B upper).policy r xs) ∧
    (∀ B C : ℕ, B ≤ C → ∀ z : Seed × Table,
      (interval δ u B z).1 ≤ (interval δ u C z).1 ∧
        (interval δ u C z).2 ≤ (interval δ u B z).2) ∧
    (∀ (B : ℕ) (z : Seed × Table), 0 ≤ (interval δ u B z).1 ∧ (interval δ u B z).2 ≤ u) ∧
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
      (∀ (B : ℕ) (upper : Bool),
        originalSimulationLaw μ (controller δ u B upper) q = streamLaw μ q δ) ∧
      (signMean μ q.val ≤ u → 1 - ENNReal.ofReal δ ≤ streamLaw μ q δ (successEvent μ q δ u)) ∧
      1 - ENNReal.ofReal δ ≤ streamLaw μ q δ (successEvent μ q δ 1)) ∧
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ], Tendsto (widthBound μ δ) atTop (𝓝 0)) ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (z : Seed × Table),
      z ∈ successEvent μ q δ u →
        Tendsto (fun B : ℕ => Anytime.halfWidth (interval δ u B z)) atTop (𝓝 0)

/-- On the success event, every data-dependent stopping budget has coverage
and the stage bound at every stage completed within it. -/
def UnknownLawStoppingStatement : Prop :=
  ∀ (μ : Measure Gap) (q : SignLaw) (δ u : ℝ) (z : Seed × Table),
    z ∈ successEvent μ q δ u → ∀ τ : Seed × Table → ℕ,
      ((interval δ u (τ z) z).1 ≤ signMean μ q.val ∧
        signMean μ q.val ≤ (interval δ u (τ z) z).2) ∧
      ∀ j : ℕ, j < stageCount ((τ z : ℕ) : ℝ) →
        2 * Anytime.halfWidth (interval δ u (τ z) z) ≤ widthBound μ δ j

end ThresholdHC.UnknownLawConfidence
