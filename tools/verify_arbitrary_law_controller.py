"""Check every full arbitrary-law all-budget controller declaration and its transitive axioms.

The statements below are independent, fixed restatements. The audit rejects
unregistered declarations and missing reports and never changes evidence.
"""

import subprocess

from verify_blind_upper_components import (
    FORBIDDEN, LEAN, bind_restatements, registered_names, strip_comments, validate_reports,
)

MODULES = ["ThresholdHC.ArbitraryLawController." + name for name in ('Schedule', 'Budget', 'LogSchedule', 'Execution', 'Intervals', 'JointFailure', 'Stages', 'Onset', 'ZeroScale', 'Coverage', 'Rate', 'Full')]
SOURCES = [LEAN / (name.replace(".", "/") + ".lean") for name in MODULES]
NAMES = [
    'pilotLog', 'pilotGroups', 'repetitions',
    'pilotReservation', 'depth', 'remaining',
    'repetitions_pos', 'repetitions_odd', 'pilotReservation_zero',
    'depth_le', 'depth_fits', 'fitting_depth_le',
    'depth_maximal', 'next_depth_exceeds', 'depth_zero_iff',
    'remaining_bounds', 'pilot_scale_upper', 'pilot_scale_lower',
    'pilotLog_nonneg', 'repetitions_pilot_error', 'pilotLog_next',
    'repetitions_next', 'selected_scale', 'continuation_base_ge',
    'median_schedule_failure', 'repetitions_log_bound', 'effective_budget',
    'spent', 'reader', 'intersect',
    'historyInterval', 'tableInterval', 'spent_mono',
    'spent_le_paid', 'measurable_reader', 'measurable_historyInterval',
    'endpoint', 'endpoint_cap', 'endpoint_budget_cap',
    'reader_range', 'next_stage_fresh', 'interval_readBlock',
    'endpoint_output', 'reader_compatible', 'word_prefix',
    'endpoint_policy_compatible', 'observedInterval', 'observedInterval_eq',
    'measurable_observedInterval', 'tableInterval_nested', 'tableInterval_coverage',
    'tableInterval_width', 'learnedStage_joint_failure_le', 'StageSeed',
    'idleStage', 'stage', 'stage_active',
    'stage_idle', 'stage_cap', 'pilotGood',
    'stageBad', 'measurableSet_stageBad', 'stage_pilot_failure',
    'stage_failure', 'repetitions_linear_bound', 'depth_eventually',
    'completed_depth_eventually', 'finite_zeroSelection', 'zeroSelection_antitone',
    'zeroSelection_budget_scale', 'Seed', 'controller',
    'interval', 'streamLaw', 'streamLaw_probability',
    'controller_original_law', 'controller_cap', 'stageCount_mono',
    'controller_compatible', 'interval_nested', 'goodEvent',
    'measurableSet_goodEvent', 'goodEvent_failure', 'goodEvent_probability',
    'goodEvent_pilot', 'goodEvent_coverage', 'stopping_budget_coverage',
    'radiusCoefficient', 'radiusCoefficient_pos', 'continuation_radius_le',
    'paidMedianStage_table_radius', 'stage_oracle_width', 'oracle_effective_scale',
    'eventual_oracle_width', 'successEvent', 'measurableSet_successEvent',
    'controller_paused', 'arbitrary_law_controller', 'successEvent_stopping',
]


def declared_names():
    found = []
    for path in SOURCES:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        found += registered_names(source)
    return found


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing all-budget controller declaration")
    source = """
import ThresholdHC.ArbitraryLawController.Full
noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget
open ThresholdHC.Anytime ThresholdHC.ArbitraryLawAdaptation ThresholdHC.RobustContinuation
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper ThresholdHC.KnownLawPlanner

example : ∀ (δ : ℝ) (s J : ℕ), pilotLog δ s J =
    Real.log (4 * (J : ℝ) / stageFailure δ s) / Real.log 2 := by intros; rfl
example : ∀ (δ : ℝ) (s J : ℕ), pilotGroups δ s J = ⌈pilotLog δ s J⌉₊ := by intros; rfl
example : ∀ (δ : ℝ) (s J : ℕ), repetitions δ s J = 8 * pilotGroups δ s J + 1 := by intros; rfl
example : ∀ (δ : ℝ) (s J : ℕ), pilotReservation δ s J = repetitions δ s J * pilotSpan J := by intros; rfl
example : ∀ (δ : ℝ) (s : ℕ), depth δ s =
    Nat.findGreatest (fun J => 2 * pilotReservation δ s J ≤ stageCap s) (s + 2) := by intros; rfl
example : ∀ (δ : ℝ) (s : ℕ), remaining δ s = stageCap s - pilotReservation δ s (depth δ s) := by intros; rfl
example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)),
    spent S 0 = 0 ∧ ∀ j, spent S (j + 1) = spent S j + (S j).cap := by intros; exact ⟨rfl, fun _ => rfl⟩
example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (r : ∀ j, R j),
    reader S r 0 = (fun _ => 0) ∧ ∀ j, reader S r (j + 1) =
      thenRead (spent S j) (reader S r j) (Nat.pair j ∘ (S j).reader (r j)) := by intros; exact ⟨rfl, fun _ => rfl⟩
example : ∀ (I J : ℝ × ℝ), intersect I J = (max I.1 J.1, min I.2 J.2) := by intros; rfl
example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (r : ∀ j, R j),
    (∀ xs, historyInterval S ρ r 0 xs = (0, ρ)) ∧ ∀ j xs, historyInterval S ρ r (j + 1) xs =
      intersect (historyInterval S ρ r j (xs.take (spent S j)))
        ((S j).historyInterval (r j) (xs.drop (spent S j))) := by intros; exact ⟨fun _ => rfl, fun _ _ => rfl⟩
example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (r : ∀ j, R j) (t : Table), tableInterval S ρ r t 0 = (0, ρ) ∧
      ∀ j, tableInterval S ρ r t (j + 1) = intersect (tableInterval S ρ r t j)
        ((S j).tableInterval (r j) (t ∘ Nat.pair j)) := by intros; exact ⟨rfl, fun _ => rfl⟩
example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (k : ℕ) (upper : Bool),
    (endpoint S ρ k upper).randomLaw = Measure.infinitePi (fun j => (S j).randomLaw) ∧
    (endpoint S ρ k upper).policy = (fun r => stopAt (spent S k) (reader S r k)) ∧
    (endpoint S ρ k upper).output = (fun z =>
      let I := historyInterval S ρ z.1 k (processHistory z.2 (spent S k)); if upper then I.2 else I.1) :=
    by intros; exact ⟨rfl, rfl, rfl⟩
example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (k : ℕ) (z : (∀ j, R j) × Table), observedInterval S ρ k z =
      (let x := populationPath ((endpoint S ρ k false).policy z.1) z.2
       ((endpoint S ρ k false).output (z.1, x), (endpoint S ρ k true).output (z.1, x))) := by intros; rfl
example : ∀ (ρ δ : ℝ) (s : ℕ), StageSeed ρ δ s =
    MedianSeed ρ (remaining δ s) (4 * pilotGroups δ s (depth δ s)) := by intros; rfl
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (ρ : ℝ),
    (idleStage S ρ).randomLaw = S.randomLaw ∧ (idleStage S ρ).pilotCost = 0 ∧
    (idleStage S ρ).continuationCost = 0 ∧ (idleStage S ρ).depth = S.depth ∧
    (idleStage S ρ).pilot = S.pilot ∧ (idleStage S ρ).upper = S.upper ∧
    (idleStage S ρ).continuation = S.continuation ∧ (idleStage S ρ).interval = (fun _ _ _ => (0, ρ)) :=
    by intros; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
example : ∀ (ρ δ : ℝ) (s : ℕ), stage ρ δ s =
    (let S := paidMedianStage ρ (remaining δ s) (4 * pilotGroups δ s (depth δ s))
      (depth δ s) (repetitions δ s (depth δ s))
     if depth δ s = 0 then idleStage S ρ else S) := by intros; rfl
example : ∀ (μ : Measure Gap) (ρ δ : ℝ) (s : ℕ) (xs : List Bool), pilotGood μ ρ δ s xs ↔
    (∀ x, (μ.map Subtype.val) (Iic x) ≤ (stage ρ δ s).learnedLaw xs (Iic x)) ∧
      ∀ i, i < depth δ s → (stage ρ δ s).upper xs i ≤ pilotBound μ (depth δ s) ρ (i + 1) := by intros; rfl
example : ∀ (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) (s : ℕ), stageBad μ q ρ δ s =
    {z | (depth δ s ≠ 0 ∧ ¬pilotGood μ ρ δ s
      (readBlock (stage ρ δ s).pilotCost (stage ρ δ s).pilot (z.2 ∘ Nat.pair 0)).1) ∨
      (stage ρ δ s).tableInterval z.1 z.2 ∈ intervalFailure (signMean μ q.val)} := by intros; rfl
example : ∀ (ρ δ : ℝ), Seed ρ δ = (∀ s, StageSeed ρ δ s) := by intros; rfl
example : ∀ (ρ δ : ℝ) (B : ℕ) (upper : Bool), controller ρ δ B upper =
    endpoint (stage ρ δ) ρ (stageCount (B : ℝ)) upper := by intros; rfl
example : ∀ (ρ δ : ℝ) (B : ℕ) (z : Seed ρ δ × Table), interval ρ δ B z =
    observedInterval (stage ρ δ) ρ (stageCount (B : ℝ)) z := by intros; rfl
example : ∀ (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ), streamLaw μ q ρ δ =
    Anytime.streamLaw μ (fun s => (stage ρ δ s).endpoint false) q := by intros; rfl
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (ρ δ : ℝ),
    IsProbabilityMeasure (streamLaw μ q ρ δ) := @streamLaw_probability
example : ∀ (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ), goodEvent μ q ρ δ =
    {z | ∀ s, stageInputs z s ∉ stageBad μ q ρ δ s} := by intros; rfl
example : radiusCoefficient = 6 * plannedCoefficient 28000 := rfl
example : ∀ (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) (H : ℕ), successEvent μ q ρ δ H =
    {z | (∀ B : ℕ, (interval ρ δ B z).1 ≤ signMean μ q.val ∧ signMean μ q.val ≤ (interval ρ δ B z).2) ∧
      ∀ B : ℕ, H ≤ B → Anytime.halfWidth (interval ρ δ B z) ≤
        2 ^ 32 * radiusCoefficient *
          (EntropyTail.selection μ ρ ((B : ℝ) / Anytime.inflation B δ)).toReal} := by intros; rfl
example : ∀ (δ : ℝ) (s J : ℕ),
    0 < repetitions δ s J := @repetitions_pos

example : ∀ (δ : ℝ) (s J : ℕ),
    repetitions δ s J = 2 * (4 * pilotGroups δ s J) + 1 := @repetitions_odd

example : ∀ (δ : ℝ) (s : ℕ),
    pilotReservation δ s 0 = 0 := @pilotReservation_zero

example : ∀ (δ : ℝ) (s : ℕ),
    depth δ s ≤ s + 2 := @depth_le

example : ∀ (δ : ℝ) (s : ℕ),
    2 * pilotReservation δ s (depth δ s) ≤ stageCap s := @depth_fits

example : ∀ {δ : ℝ} {s J : ℕ} (hJ : 1 ≤ J)
    (hfit : 2 * pilotReservation δ s J ≤ stageCap s),
    J ≤ s + 2 := @fitting_depth_le

example : ∀ {δ : ℝ} {s J : ℕ} (hJ : 1 ≤ J)
    (hfit : 2 * pilotReservation δ s J ≤ stageCap s),
    J ≤ depth δ s := @depth_maximal

example : ∀ (δ : ℝ) (s : ℕ),
    stageCap s < 2 * pilotReservation δ s (depth δ s + 1) := @next_depth_exceeds

example : ∀ (δ : ℝ) (s : ℕ),
    depth δ s = 0 ↔
    ∀ J, 1 ≤ J → stageCap s < 2 * pilotReservation δ s J := @depth_zero_iff

example : ∀ (δ : ℝ) (s : ℕ),
    0 < remaining δ s ∧ stageCap s ≤ 2 * remaining δ s ∧
      pilotReservation δ s (depth δ s) + remaining δ s = stageCap s := @remaining_bounds

example : ∀ {δ : ℝ} {s J : ℕ} (hJ : 1 ≤ J),
    pilotReservation δ s J ≤ repetitions δ s J * 4 ^ J := @pilot_scale_upper

example : ∀ {δ : ℝ} {s J : ℕ} (hJ : 1 ≤ J),
    repetitions δ s J * 4 ^ J ≤ 2 * pilotReservation δ s J := @pilot_scale_lower

example : ∀ {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) {J : ℕ} (hJ : 1 ≤ J),
    0 ≤ pilotLog δ s J := @pilotLog_nonneg

example : ∀ {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) {J : ℕ} (_hJ : 1 ≤ J),
    8 * log (2 * (J : ℝ) / (stageFailure δ s / 2)) ≤ repetitions δ s J := @repetitions_pilot_error

example : ∀ {δ : ℝ} (hd : 0 < δ) (s : ℕ) {J : ℕ} (hJ : 1 ≤ J),
    pilotLog δ s (J + 1) ≤ pilotLog δ s J + 1 := @pilotLog_next

example : ∀ {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) {J : ℕ} (hJ : 1 ≤ J),
    repetitions δ s (J + 1) ≤ 2 * repetitions δ s J := @repetitions_next

example : ∀ {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) (hJ : 1 ≤ depth δ s),
    stageCap s < 16 * repetitions δ s (depth δ s) * 4 ^ depth δ s ∧
      repetitions δ s (depth δ s) * 4 ^ depth δ s ≤ stageCap s := @selected_scale

example : ∀ {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) (hJ : 1 ≤ depth δ s),
    (4 : ℝ) ^ depth δ s / 16 ≤
      medianBaseBudget (remaining δ s) (4 * pilotGroups δ s (depth δ s)) := @continuation_base_ge

example : ∀ {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) {J : ℕ} (hJ : 1 ≤ J),
    (3/4 : ℝ) ^ (4 * pilotGroups δ s J) / 2 ≤ stageFailure δ s / 2 := @median_schedule_failure

example : ∀ {δ B : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (hB : 0 ≤ B) {s : ℕ} (hs : stageCount B = s + 1)
    (hJ : 1 ≤ depth δ s),
    (repetitions δ s (depth δ s) : ℝ) ≤ 64 * inflation B δ := @repetitions_log_bound

example : ∀ {δ B : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (hB : 0 ≤ B) {s : ℕ} (hs : stageCount B = s + 1)
    (hJ : 1 ≤ depth δ s),
    B / (4096 * inflation B δ) < (4 : ℝ) ^ depth δ s := @effective_budget

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)),
    Monotone (spent S) := @spent_mono

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j))
    (h : ∀ j, (S j).cap ≤ stageCap j) (k : ℕ),
    spent S k ≤ paid k := @spent_le_paid

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (k : ℕ) (xs : List Bool),
    Measurable (fun r => reader S r k xs) := @measurable_reader

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (k : ℕ) (xs : List Bool),
    Measurable (fun r => historyInterval S ρ r k xs) := @measurable_historyInterval

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (k : ℕ) (upper : Bool),
    PathwiseCap (endpoint S ρ k upper) (spent S k) := @endpoint_cap

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (h : ∀ j, (S j).cap ≤ stageCap j) (B : ℝ) (upper : Bool),
    PathwiseCap (endpoint S ρ (stageCount B) upper) ⌊B⌋₊ := @endpoint_budget_cap

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (r : ∀ j, R j)
    (n : ℕ) (hn : 0 < n) (xs : List Bool),
    ∃ i < n, ∃ c, reader S r n xs = Nat.pair i c := @reader_range

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (r : ∀ j, R j)
    (n : ℕ) (s : Table) (c : ℕ),
    (readBlock (spent S n) (reader S r n) s).2 (Nat.pair n c) = s (Nat.pair n c) := @next_stage_fresh

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (r : ∀ j, R j) (s : Table) (k : ℕ),
    historyInterval S ρ r k (readBlock (spent S k) (reader S r k) s).1 =
      tableInterval S ρ r s k := @interval_readBlock

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (k : ℕ)
    (upper : Bool) (r : ∀ j, R j) (s : Table),
    (endpoint S ρ k upper).output (r, populationPath ((endpoint S ρ k upper).policy r) s) =
      if upper then (tableInterval S ρ r s k).2 else (tableInterval S ρ r s k).1 := @endpoint_output

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (r : ∀ j, R j)
    {k l : ℕ} (hkl : k ≤ l) (xs : List Bool) (hx : xs.length < spent S k),
    reader S r l xs = reader S r k xs := @reader_compatible

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (r : ∀ j, R j)
    {k l : ℕ} (hkl : k ≤ l) (s : Table),
    ((readBlock (spent S l) (reader S r l) s).1).take (spent S k) =
      (readBlock (spent S k) (reader S r k) s).1 := @word_prefix

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    {k l : ℕ} (hkl : k ≤ l) (upper upper' : Bool) (r : ∀ j, R j)
    (xs : List Bool) (hx : xs.length < spent S k),
    (endpoint S ρ l upper').policy r xs = (endpoint S ρ k upper).policy r xs := @endpoint_policy_compatible

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (k : ℕ)
    (z : (∀ j, R j) × Table),
    observedInterval S ρ k z = tableInterval S ρ z.1 z.2 k := @observedInterval_eq

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (k : ℕ),
    Measurable (observedInterval S ρ k) := @measurable_observedInterval

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (r : ∀ j, R j) (s : Table) {k l : ℕ} (hkl : k ≤ l),
    (tableInterval S ρ r s k).1 ≤ (tableInterval S ρ r s l).1 ∧
      (tableInterval S ρ r s l).2 ≤ (tableInterval S ρ r s k).2 := @tableInterval_nested

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ θ : ℝ)
    (r : ∀ j, R j) (s : Table) (hθ : 0 ≤ θ ∧ θ ≤ ρ)
    (h : ∀ j, ((S j).tableInterval (r j) (s ∘ Nat.pair j)).1 ≤ θ ∧
      θ ≤ ((S j).tableInterval (r j) (s ∘ Nat.pair j)).2) (k : ℕ),
    (tableInterval S ρ r s k).1 ≤ θ ∧ θ ≤ (tableInterval S ρ r s k).2 := @tableInterval_coverage

example : ∀ {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (r : ∀ j, R j) (s : Table) (j : ℕ),
    Anytime.halfWidth (tableInterval S ρ r s (j + 1)) ≤
      Anytime.halfWidth ((S j).tableInterval (r j) (s ∘ Nat.pair j)) := @tableInterval_width

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R) (q : SignLaw)
    (good : List Bool → Prop) (θ : ℝ) (δ : ℝ≥0∞)
    (hf : ∀ xs, good xs →
      ((originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.interval (S.learnedLaw xs) z.1
          (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1))
        (intervalFailure θ) ≤ δ),
    (originalSimulationLaw μ (S.endpoint false) q)
      {z | ¬good (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 ∨
        S.tableInterval z.1 z.2 ∈ intervalFailure θ} ≤
      (originalSimulationLaw μ (S.endpoint false) q)
        {z | ¬good (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1} + δ := @learnedStage_joint_failure_le

example : ∀ {ρ δ : ℝ} {s : ℕ} (h : 1 ≤ depth δ s),
    stage ρ δ s = paidMedianStage ρ (remaining δ s) (4 * pilotGroups δ s (depth δ s))
      (depth δ s) (repetitions δ s (depth δ s)) := @stage_active

example : ∀ {ρ δ : ℝ} {s : ℕ} (h : depth δ s = 0),
    (stage ρ δ s).cap = 0 ∧
      (∀ r xs, (stage ρ δ s).historyInterval r xs = (0, ρ)) ∧
      (∀ r t, (stage ρ δ s).tableInterval r t = (0, ρ)) := @stage_idle

example : ∀ (ρ δ : ℝ) (s : ℕ),
    (stage ρ δ s).cap ≤ stageCap s := @stage_cap

example : ∀ (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) (s : ℕ),
    MeasurableSet (stageBad μ q ρ δ s) := @measurableSet_stageBad

example : ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) (hJ : 1 ≤ depth δ s) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (originalSimulationLaw μ ((stage ρ δ s).endpoint false) q)
      {z | ¬pilotGood μ ρ δ s
        (readBlock (stage ρ δ s).pilotCost (stage ρ δ s).pilot (z.2 ∘ Nat.pair 0)).1} ≤
      ENNReal.ofReal (stageFailure δ s / 2) := @stage_pilot_failure

example : ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hd : 0 < δ) (hu : δ ≤ 1/4) (s : ℕ)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (hq : RarePrior μ ρ q),
    (originalSimulationLaw μ ((stage ρ δ s).endpoint false) q) (stageBad μ q ρ δ s) ≤
      ENNReal.ofReal (stageFailure δ s) := @stage_failure

example : ∀ {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    {J : ℕ} (hJ : 1 ≤ J) (s : ℕ),
    (repetitions δ s J : ℝ) ≤ (16 * log (4 * (J : ℝ) / δ) + 57) * ((s : ℝ) + 1) := @repetitions_linear_bound

example : ∀ {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4) (J : ℕ),
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → J ≤ depth δ s := @depth_eventually

example : ∀ {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4) (J : ℕ),
    ∃ H : ℕ, 1 ≤ H ∧ ∀ B : ℕ, H ≤ B → ∃ s : ℕ,
      stageCount (B : ℝ) = s + 1 ∧ J ≤ depth δ s := @completed_depth_eventually

example : ∀ (α : Measure ℝ) (ρ B : ℝ),
    zeroSelection α ρ B ≠ ⊤ := @finite_zeroSelection

example : ∀ (α : Measure ℝ) (ρ : ℝ) {b B : ℝ}
    (hb : 0 < b) (hB : b ≤ B),
    zeroSelection α ρ B ≤ zeroSelection α ρ b := @zeroSelection_antitone

example : ∀ (α : Measure ℝ) (ρ : ℝ) {b B : ℝ}
    (hb : 0 < b) (hB : b ≤ B),
    zeroSelection α ρ b ≤ ENNReal.ofReal (Real.sqrt (B/b)) * zeroSelection α ρ B := @zeroSelection_budget_scale

example : ∀ (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ)
    (B : ℕ) (upper : Bool),
    originalSimulationLaw μ (controller ρ δ B upper) q = streamLaw μ q ρ δ := @controller_original_law

example : ∀ (ρ δ : ℝ) (B : ℕ) (upper : Bool),
    PathwiseCap (controller ρ δ B upper) B := @controller_cap

example : ∀ {B C : ℕ} (h : B ≤ C),
    stageCount (B : ℝ) ≤ stageCount (C : ℝ) := @stageCount_mono

example : ∀ (ρ δ : ℝ) {B C : ℕ} (h : B ≤ C)
    (upper upper' : Bool) (r : Seed ρ δ) (xs : List Bool)
    (hx : xs.length < spent (stage ρ δ) (stageCount (B : ℝ))),
    (controller ρ δ C upper').policy r xs = (controller ρ δ B upper).policy r xs := @controller_compatible

example : ∀ (ρ δ : ℝ) {B C : ℕ} (h : B ≤ C) (z : Seed ρ δ × Table),
    (interval ρ δ B z).1 ≤ (interval ρ δ C z).1 ∧
      (interval ρ δ C z).2 ≤ (interval ρ δ B z).2 := @interval_nested

example : ∀ (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ),
    MeasurableSet (goodEvent μ q ρ δ) := @measurableSet_goodEvent

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hd : 0 < δ) (hu : δ ≤ 1/4) (hq : RarePrior μ ρ q),
    streamLaw μ q ρ δ (goodEvent μ q ρ δ)ᶜ ≤ ENNReal.ofReal δ := @goodEvent_failure

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hd : 0 < δ) (hu : δ ≤ 1/4) (hq : RarePrior μ ρ q),
    1 - ENNReal.ofReal δ ≤ streamLaw μ q ρ δ (goodEvent μ q ρ δ) := @goodEvent_probability

example : ∀ (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ)
    {z : Seed ρ δ × Table} (hz : z ∈ goodEvent μ q ρ δ) {s : ℕ} (hs : 1 ≤ depth δ s),
    pilotGood μ ρ δ s (readBlock (stage ρ δ s).pilotCost (stage ρ δ s).pilot
      ((stageInputs z s).2 ∘ Nat.pair 0)).1 := @goodEvent_pilot

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (ρ δ : ℝ) (hq : RarePrior μ ρ q) {z : Seed ρ δ × Table}
    (hz : z ∈ goodEvent μ q ρ δ) (B : ℕ),
    (interval ρ δ B z).1 ≤ signMean μ q.val ∧ signMean μ q.val ≤ (interval ρ δ B z).2 := @goodEvent_coverage

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hd : 0 < δ) (hu : δ ≤ 1/4) (hq : RarePrior μ ρ q)
    (τ : (Seed ρ δ × Table) → ℕ),
    streamLaw μ q ρ δ {z | ¬((interval ρ δ (τ z) z).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (interval ρ δ (τ z) z).2)} ≤ ENNReal.ofReal δ := @stopping_budget_coverage

example : 0 < radiusCoefficient := @radiusCoefficient_pos

example : ∀ {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) (hJ : 1 ≤ depth δ s) (α : Measure ℝ) (ρ : ℝ),
    medianRadius α ρ (remaining δ s) (4 * pilotGroups δ s (depth δ s)) ≤
      4 * radiusCoefficient * (zeroSelection α ρ ((4 : ℝ) ^ depth δ s)).toReal := @continuation_radius_le

example : ∀ (ρ B : ℝ) (m J k : ℕ)
    (r : MedianSeed ρ B m) (t : Table),
    let S := paidMedianStage ρ B m J k
    Anytime.halfWidth (S.tableInterval r t) =
      medianRadius (S.learnedLaw (readBlock S.pilotCost S.pilot (t ∘ Nat.pair 0)).1) ρ B m := @paidMedianStage_table_radius

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hd : 0 < δ) (hu : δ ≤ 1/4)
    {z : Seed ρ δ × Table} (hz : z ∈ goodEvent μ q ρ δ) {s : ℕ}
    (hJ : 1 ≤ depth δ s) (hon : PilotOnset μ ρ (depth δ s)),
    Anytime.halfWidth ((stage ρ δ s).tableInterval (z.1 s) (z.2 ∘ Nat.pair s)) ≤
      4 * radiusCoefficient * 16777216 * (EntropyTail.selection μ ρ ((4 : ℝ) ^ depth δ s)).toReal := @stage_oracle_width

example : ∀ (μ : Measure Gap) (ρ : ℝ) {δ B : ℝ}
    (hd : 0 < δ) (hu : δ ≤ 1/4) (hB : 0 < B) {s : ℕ}
    (hs : stageCount B = s + 1) (hJ : 1 ≤ depth δ s),
    (EntropyTail.selection μ ρ ((4 : ℝ) ^ depth δ s)).toReal ≤
      64 * (EntropyTail.selection μ ρ (B / Anytime.inflation B δ)).toReal := @oracle_effective_scale

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hd : 0 < δ) (hu : δ ≤ 1/4),
    ∃ H : ℕ, 1 ≤ H ∧ ∀ (q : SignLaw) (z : Seed ρ δ × Table),
      z ∈ goodEvent μ q ρ δ → ∀ B : ℕ, H ≤ B →
        Anytime.halfWidth (interval ρ δ B z) ≤
          2 ^ 32 * radiusCoefficient *
            (EntropyTail.selection μ ρ ((B : ℝ) / Anytime.inflation B δ)).toReal := @eventual_oracle_width

example : ∀ (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) (H : ℕ),
    MeasurableSet (successEvent μ q ρ δ H) := @measurableSet_successEvent

example : ∀ (ρ δ : ℝ) {B C : ℕ}
    (h : stageCount (B : ℝ) = stageCount (C : ℝ)) (upper : Bool),
    controller ρ δ B upper = controller ρ δ C upper := @controller_paused

example : ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hd : 0 < δ) (hu : δ ≤ 1/4),
    (∀ B : ℕ, ∀ upper : Bool, PathwiseCap (controller ρ δ B upper) B) ∧
    (∀ B C : ℕ, B ≤ C → ∀ (upper upper' : Bool) (r : Seed ρ δ) (xs : List Bool),
      xs.length < spent (stage ρ δ) (stageCount (B : ℝ)) →
      (controller ρ δ C upper').policy r xs = (controller ρ δ B upper).policy r xs) ∧
    (∀ B C : ℕ, B ≤ C → ∀ z : Seed ρ δ × Table,
      (interval ρ δ B z).1 ≤ (interval ρ δ C z).1 ∧
        (interval ρ δ C z).2 ≤ (interval ρ δ B z).2) ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ∃ H : ℕ, 1 ≤ H ∧
      ∀ q : SignLaw, RarePrior μ ρ q →
        1 - ENNReal.ofReal δ ≤ streamLaw μ q ρ δ (successEvent μ q ρ δ H) := @arbitrary_law_controller

example : ∀ (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) (H : ℕ)
    {z : Seed ρ δ × Table} (hz : z ∈ successEvent μ q ρ δ H)
    (τ : (Seed ρ δ × Table) → ℕ),
    ((interval ρ δ (τ z) z).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (interval ρ δ (τ z) z).2) ∧
    (H ≤ τ z → Anytime.halfWidth (interval ρ δ (τ z) z) ≤
      2 ^ 32 * radiusCoefficient *
        (EntropyTail.selection μ ρ (((τ z : ℕ) : ℝ) / Anytime.inflation (τ z) δ)).toReal) := @successEvent_stopping

end ThresholdHC.ArbitraryLawController
"""
    if source.count("example ") != len(NAMES):
        raise ValueError("Each all-budget controller declaration needs one restated statement")
    bind_restatements(source, NAMES)
    roots = {"ThresholdHC.ArbitraryLawController." + name for name in NAMES}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", *MODULES], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
