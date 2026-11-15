"""Audit the capped multi-depth pilot of the arbitrary-law adaptation proof.

Every definition and theorem of the two pilot modules is restated in full, so
a changed definition, hypothesis or constant is an elaboration error, and the
transitive axioms of every declaration are reported. A declaration in those
modules that is not registered here is an error. Prints the kernel report;
writes nothing.
"""

import subprocess
from verify_blind_upper_components import (FORBIDDEN, LEAN, bind_restatements,
                                           registered_names, strip_comments,
                                           validate_reports)

MODULE = "ThresholdHC.ArbitraryLawAdaptation.TailPilotLaw"
SOURCES = [LEAN / "ThresholdHC/ArbitraryLawAdaptation" / (name + ".lean")
           for name in ("TailPilot", "TailPilotLaw")]
NAMES = [
    "pilotBudget", "pilotCoinCap", "pilotSpan", "pilotBudget_pos", "pilotCoinCap_pos",
    "sum_inv_consecutive", "sum_two_pow", "pilot_reciprocal_sum", "pilot_geometric_sum",
    "pilotSpan_cast", "pilotSpan_le", "le_two_mul_pilotSpan", "probeResolved_one_zero",
    "probeResolved_one_one", "DepthOneState", "depthOneState_step", "depthOneState_run",
    "probeWordCompleted_depth_one", "probeUpper_one", "medianWordUpper_depth_one",
    "medianWordUpper_pos", "medianWordUpper_le_one", "pilotLength", "pilotReader", "pilotCost",
    "pilotUpper", "pilotCost_eq", "pilotCost_le", "pilotUpper_zero", "pilotUpper_nonneg",
    "pilotUpper_le_one", "pilotUpper_readBlock", "exists_lt_eq_biUnion", "measurableSet_exists_lt",
    "block_union_bound", "infinitePi_map_first_block", "pilotBound", "capped_bound_le_pilotBound",
    "PilotGood", "pilotFailure", "measurableSet_pilotFailure", "pilotGood_of_not_failure",
    "original_pilotFailure_le", "original_pilot_event", "pilotStreams", "stageStreams",
    "measurable_pilotStreams", "measurable_stageStreams", "pilotStreams_law", "stageStreams_law",
    "pilotEstimator", "pilotEstimator_cap", "observable_pilot_event", "pilotStage",
    "pilotStage_cap", "pilotStage_cap_le", "pilotStage_pathwise", "pilotStageWord",
    "pilotStage_tableInterval", "pilotStage_upper_word", "pilotStage_learnedLaw_probability",
    "pilotStage_learnedLaw_eq", "pilotStage_learnedLaw_zero", "pilotStage_learnedLaw_grid",
    "pilotStage_dominates", "original_pilotStage_event",
]


def declared_names():
    """Every declaration of the two modules, after rejecting proof escapes."""
    found = []
    for path in SOURCES:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        found += registered_names(source)
    return found


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing pilot declaration")
    source = """
import ThresholdHC.ArbitraryLawAdaptation.TailPilotLaw
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier6
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.HardBudget ThresholdHC.BlindUpper

example : ∀ (J j : ℕ), pilotBudget J j =
    ⌈(4 : ℝ) ^ J / (2 * (j : ℝ) * ((j : ℝ) + 1))⌉₊ + 2 ^ (J + j - 2) := fun _ _ => rfl
example : ∀ (J : ℕ) (ρ : ℝ),
    pilotCoinCap J ρ = ⌈Real.sqrt (64 * (4 : ℝ) ^ J / ρ)⌉₊ := fun _ _ => rfl
example : ∀ (J : ℕ),
    pilotSpan J = ∑ i ∈ Finset.range J, pilotBudget J (i + 1) := fun _ => rfl
example : ∀ (st : ProbeState), DepthOneState st ↔
    (st.level ≤ 1 ∧ st.len < 4 ^ st.level ∧ st.heads ≤ st.len ∧ st.count ≤ 1 ∧
      (st.count = 1 → st.stopped = true)) := fun _ => Iff.rfl
example : ∀ (J m i : ℕ), pilotLength J m i = m * pilotBudget J (i + 1) := fun _ _ _ => rfl
example : ∀ (J m M : ℕ), pilotReader J m M =
    seqReader (pilotLength J m) (fun i => medianReader (i + 1) M (pilotBudget J (i + 1)) m) J :=
  fun _ _ _ => rfl
example : ∀ (J m : ℕ), pilotCost J m = seqOffset (pilotLength J m) J := fun _ _ => rfl
example : ∀ (J m M : ℕ) (w : List Bool) (i : ℕ), pilotUpper J m M w i =
    medianWordUpper (i + 1) m (pilotBudget J (i + 1)) M (seqWord (pilotLength J m) i w) :=
  fun _ _ _ _ _ => rfl
example : ∀ (μ : Measure Gap) (J : ℕ) (ρ : ℝ) (j : ℕ), pilotBound μ J ρ j =
    128 * (tailUnresolvedMass μ j + (∫ d : Gap, tailWorkEnvelope j d ∂μ) / pilotBudget J j +
      1 / pilotCoinCap J ρ) := fun _ _ _ _ => rfl
example : ∀ (μ : Measure Gap) (J m : ℕ) (ρ : ℝ) (z : ℕ → ℕ → ℕ → ℕ → Bool),
    PilotGood μ J m ρ z ↔
      ∀ i, i < J →
        (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
          medianUpper (i + 1) m b' M' (z i)) ∧
        medianUpper (i + 1) m (fun _ => pilotBudget J (i + 1)) (fun _ => pilotCoinCap J ρ)
            (z i) ≤ pilotBound μ J ρ (i + 1) := fun _ _ _ _ _ => Iff.rfl
example : ∀ (μ : Measure Gap) (J m : ℕ) (ρ : ℝ), pilotFailure μ J m ρ =
    {z | ∃ i, i < J ∧ z i ∈ medianFailure (i + 1) m (pilotBudget J (i + 1)) (pilotCoinCap J ρ)
      (μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)})
      (min 1 (128 * max (max (tailUnresolvedMass μ (i + 1))
        ((∫ d : Gap, tailWorkEnvelope (i + 1) d ∂μ) / pilotBudget J (i + 1)))
        (1 / pilotCoinCap J ρ)))} := fun _ _ _ _ => rfl
example : ∀ (ω : ℕ → ℕ → Bool),
    pilotStreams ω = fun i k c => ω (Nat.pair i (Nat.pair k c)) := fun _ => rfl
example : ∀ (ω : ℕ → ℕ → Bool),
    stageStreams ω = fun i k c => ω (Nat.pair 0 (Nat.pair i (Nat.pair k c))) := fun _ => rfl
example : ∀ (J m : ℕ) (ρ : ℝ) (i : ℕ), pilotEstimator J m ρ i =
    wordEstimator (pilotCost J m) (pilotReader J m (pilotCoinCap J ρ))
      (fun w => pilotUpper J m (pilotCoinCap J ρ) w i) := fun _ _ _ _ => rfl
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (J m : ℕ) (ρ : ℝ),
    (pilotStage S J m ρ).randomLaw = S.randomLaw ∧
      (pilotStage S J m ρ).pilotCost = pilotCost J m ∧
      (pilotStage S J m ρ).continuationCost = S.continuationCost ∧
      (pilotStage S J m ρ).depth = J - 1 ∧
      (pilotStage S J m ρ).pilot = pilotReader J m (pilotCoinCap J ρ) ∧
      (pilotStage S J m ρ).upper = pilotUpper J m (pilotCoinCap J ρ) ∧
      (pilotStage S J m ρ).continuation = S.continuation ∧
      (pilotStage S J m ρ).interval = S.interval :=
  fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
example : ∀ (J m : ℕ) (ρ : ℝ) (s : Table), pilotStageWord J m ρ s =
    (readBlock (pilotCost J m) (pilotReader J m (pilotCoinCap J ρ))
      (fun i => s (Nat.pair 0 i))).1 := fun _ _ _ _ => rfl

example : ∀ (J j : ℕ),
    0 < pilotBudget J j := @pilotBudget_pos
example : ∀ (J : ℕ) {ρ : ℝ} (hρ : 0 < ρ),
    0 < pilotCoinCap J ρ := @pilotCoinCap_pos
example : ∀ (n : ℕ),
    ∑ i ∈ Finset.range n, (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 2)) = 1 - 1 / ((n : ℝ) + 1) := @sum_inv_consecutive
example : ∀ (n : ℕ),
    ∑ i ∈ Finset.range n, (2 : ℝ) ^ i = 2 ^ n - 1 := @sum_two_pow
example : ∀ (J : ℕ),
    ∑ i ∈ Finset.range J,
      (4 : ℝ) ^ J / (2 * (((i + 1 : ℕ) : ℝ)) * ((((i + 1 : ℕ) : ℝ)) + 1)) =
      (4 : ℝ) ^ J / 2 * (1 - 1 / ((J : ℝ) + 1)) := @pilot_reciprocal_sum
example : ∀ (K : ℕ),
    ∑ i ∈ Finset.range (K + 1), ((2 ^ (K + 1 + (i + 1) - 2) : ℕ) : ℝ) =
      (4 : ℝ) ^ (K + 1) / 2 - 2 ^ K := @pilot_geometric_sum
example : ∀ (K : ℕ),
    ((pilotSpan (K + 1) : ℕ) : ℝ) =
      (∑ i ∈ Finset.range (K + 1),
      ((⌈(4 : ℝ) ^ (K + 1) / (2 * (((i + 1 : ℕ) : ℝ)) * ((((i + 1 : ℕ) : ℝ)) + 1))⌉₊ : ℕ) : ℝ)) +
      ((4 : ℝ) ^ (K + 1) / 2 - 2 ^ K) := @pilotSpan_cast
example : ∀ {J : ℕ} (hJ : 1 ≤ J),
    pilotSpan J ≤ 4 ^ J := @pilotSpan_le
example : ∀ {J : ℕ} (hJ : 1 ≤ J),
    4 ^ J ≤ 2 * pilotSpan J := @le_two_mul_pilotSpan
example : ∀ {h : ℕ} (hh : h ≤ 1),
    probeResolved 1 0 h = false := @probeResolved_one_zero
example : ∀ {h : ℕ} (hh : h ≤ 4),
    probeResolved 1 1 h = false := @probeResolved_one_one
example : ∀ (M : ℕ) {st : ProbeState} (h : DepthOneState st) (b : Bool),
    DepthOneState (probeStep 1 M st b) := @depthOneState_step
example : ∀ (M : ℕ) (w : List Bool),
    DepthOneState (probeRun 1 M w) := @depthOneState_run
example : ∀ (M : ℕ) (w : List Bool),
    probeWordCompleted 1 M w ≤ 1 := @probeWordCompleted_depth_one
example :
    probeUpper 1 = 1 := @probeUpper_one
example : ∀ (m b M : ℕ) (w : List Bool),
    medianWordUpper 1 m b M w = 1 := @medianWordUpper_depth_one
example : ∀ (J m b M : ℕ) (w : List Bool),
    0 < medianWordUpper J m b M w := @medianWordUpper_pos
example : ∀ (J m b M : ℕ) (w : List Bool),
    medianWordUpper J m b M w ≤ 1 := @medianWordUpper_le_one
example : ∀ (J m : ℕ),
    pilotCost J m = m * pilotSpan J := @pilotCost_eq
example : ∀ {J : ℕ} (hJ : 1 ≤ J) (m : ℕ),
    pilotCost J m ≤ m * 4 ^ J := @pilotCost_le
example : ∀ (J m M : ℕ) (w : List Bool),
    pilotUpper J m M w 0 = 1 := @pilotUpper_zero
example : ∀ (J m M : ℕ) (w : List Bool) (i : ℕ),
    0 ≤ pilotUpper J m M w i := @pilotUpper_nonneg
example : ∀ (J m M : ℕ) (w : List Bool) (i : ℕ),
    pilotUpper J m M w i ≤ 1 := @pilotUpper_le_one
example : ∀ (J m M : ℕ) (s : Table) {i : ℕ} (hi : i < J),
    pilotUpper J m M (readBlock (pilotCost J m) (pilotReader J m M) s).1 i =
      medianUpper (i + 1) m (fun _ => pilotBudget J (i + 1)) (fun _ => M)
      (fun k c => s (Nat.pair i (Nat.pair k c))) := @pilotUpper_readBlock
example : ∀ {Y : Type*} (Bad : ℕ → Set Y) (n : ℕ),
    {ω : ℕ → Y | ∃ i, i < n ∧ ω i ∈ Bad i} =
      ⋃ i ∈ Finset.range n, (fun ω : ℕ → Y => ω i) ⁻¹' Bad i := @exists_lt_eq_biUnion
example : ∀ {Y : Type*} [MeasurableSpace Y] (Bad : ℕ → Set Y) (hmeas : ∀ i, MeasurableSet (Bad i)) (n : ℕ),
    MeasurableSet {ω : ℕ → Y | ∃ i, i < n ∧ ω i ∈ Bad i} := @measurableSet_exists_lt
example : ∀ {Y : Type*} [MeasurableSpace Y] (P : Measure Y) [IsProbabilityMeasure P] (Bad : ℕ → Set Y) (hmeas : ∀ i, MeasurableSet (Bad i)) (n : ℕ) {e : ℝ} (hbad : ∀ i, i < n → P.real (Bad i) ≤ e),
    (Measure.infinitePi (fun _ : ℕ => P)).real {ω | ∃ i, i < n ∧ ω i ∈ Bad i} ≤ n * e := @block_union_bound
example : ∀ {X : Type*} [MeasurableSpace X] (S : Measure X) [IsProbabilityMeasure S],
    (Measure.infinitePi (fun _ : ℕ => S)).map (fun (ω : ℕ → X) (i : ℕ) => ω (Nat.pair 0 i)) =
      Measure.infinitePi (fun _ : ℕ => S) := @infinitePi_map_first_block
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (J : ℕ) (ρ : ℝ) (j : ℕ),
    min 1 (128 * max (max (tailUnresolvedMass μ j)
      ((∫ d : Gap, tailWorkEnvelope j d ∂μ) / pilotBudget J j)) (1 / pilotCoinCap J ρ)) ≤
      pilotBound μ J ρ j := @capped_bound_le_pilotBound
example : ∀ (μ : Measure Gap) (J m : ℕ) (ρ : ℝ),
    MeasurableSet (pilotFailure μ J m ρ) := @measurableSet_pilotFailure
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {J m : ℕ} {ρ : ℝ} {z : ℕ → ℕ → ℕ → ℕ → Bool} (h : z ∉ pilotFailure μ J m ρ),
    PilotGood μ J m ρ z := @pilotGood_of_not_failure
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hm : 0 < m),
    (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))).real
      (pilotFailure μ J m ρ) ≤ J * (2 * exp (-(m : ℝ) / 8)) := @original_pilotFailure_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J m : ℕ) {ρ ε : ℝ} (hρ : 0 < ρ) (hJ : 1 ≤ J) (hm : 0 < m) (hε : 0 < ε) (hmε : 8 * log (2 * (J : ℝ) / ε) ≤ m) {f : (ℕ → ℕ → Bool) → ℕ → ℕ → ℕ → ℕ → Bool} (hf : Measurable f) (hlaw : (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map f = Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))),
    1 - ε ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | PilotGood μ J m ρ (f ω)} := @original_pilot_event
example :
    Measurable pilotStreams := @measurable_pilotStreams
example :
    Measurable stageStreams := @measurable_stageStreams
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map pilotStreams =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))) := @pilotStreams_law
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map stageStreams =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))) := @stageStreams_law
example : ∀ (J m : ℕ) (ρ : ℝ) (i : ℕ),
    PathwiseCap (pilotEstimator J m ρ i) (pilotCost J m) := @pilotEstimator_cap
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J m i₀ : ℕ) {ρ ε : ℝ} (hρ : 0 < ρ) (hJ : 1 ≤ J) (hm : 0 < m) (hε : 0 < ε) (hmε : 8 * log (2 * (J : ℝ) / ε) ≤ m),
    1 - ε ≤
      (experimentLaw μ (pilotEstimator J m ρ i₀) q).real
      {z | ∀ i, i < J →
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
      (pilotEstimator J m ρ i).output (z.1.1, z.2) ∧
      (pilotEstimator J m ρ i).output (z.1.1, z.2) ≤ pilotBound μ J ρ (i + 1)} := @observable_pilot_event
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (J m : ℕ) (ρ : ℝ),
    (pilotStage S J m ρ).cap = m * pilotSpan J + S.continuationCost := @pilotStage_cap
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) {J : ℕ} (hJ : 1 ≤ J) (m : ℕ) (ρ : ℝ),
    (pilotStage S J m ρ).cap ≤ m * 4 ^ J + S.continuationCost := @pilotStage_cap_le
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (upper : Bool),
    PathwiseCap ((pilotStage S J m ρ).endpoint upper)
      (m * pilotSpan J + S.continuationCost) := @pilotStage_pathwise
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (r : R) (s : Table),
    (pilotStage S J m ρ).tableInterval r s =
      S.interval ((pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ s)) r
      (readBlock S.continuationCost
      (S.continuation ((pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ s)) r)
      (fun i => s (Nat.pair 1 i))).1 := @pilotStage_tableInterval
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (s : Table) {i : ℕ} (hi : i < J),
    (pilotStage S J m ρ).upper (pilotStageWord J m ρ s) i =
      medianUpper (i + 1) m (fun _ => pilotBudget J (i + 1)) (fun _ => pilotCoinCap J ρ)
      (stageStreams s i) := @pilotStage_upper_word
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (xs : List Bool),
    IsProbabilityMeasure ((pilotStage S J m ρ).learnedLaw xs) := @pilotStage_learnedLaw_probability
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (xs : List Bool),
    (pilotStage S J m ρ).learnedLaw xs =
      ENNReal.ofReal (prefixMinimum (pilotUpper J m (pilotCoinCap J ρ) xs) (J - 1)) •
      Measure.dirac 0 +
      ∑ i : Fin (J - 1),
      ENNReal.ofReal (prefixMinimum (pilotUpper J m (pilotCoinCap J ρ) xs) i.val -
      prefixMinimum (pilotUpper J m (pilotCoinCap J ρ) xs) (i.val + 1)) •
      Measure.dirac (gridPoint (i.val + 1)) := @pilotStage_learnedLaw_eq
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (xs : List Bool),
    (pilotStage S J m ρ).learnedLaw xs {0} =
      ENNReal.ofReal (prefixMinimum (pilotUpper J m (pilotCoinCap J ρ) xs) (J - 1)) := @pilotStage_learnedLaw_zero
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (xs : List Bool) {j : ℕ} (hj : j + 1 < J),
    (pilotStage S J m ρ).learnedLaw xs (Set.Iic (gridPoint (j + 1))) =
      ENNReal.ofReal (prefixMinimum (pilotUpper J m (pilotCoinCap J ρ) xs) j) := @pilotStage_learnedLaw_grid
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R) {J : ℕ} (hJ : 1 ≤ J) (m : ℕ) (ρ : ℝ) (xs : List Bool) (hcover : ∀ i, i < J → μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤ pilotUpper J m (pilotCoinCap J ρ) xs i) (x : ℝ),
    (μ.map Subtype.val) (Set.Iic x) ≤ (pilotStage S J m ρ).learnedLaw xs (Set.Iic x) := @pilotStage_dominates
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (S : LearnedStage R) (J m : ℕ) {ρ ε : ℝ} (hρ : 0 < ρ) (hJ : 1 ≤ J) (hm : 0 < m) (hε : 0 < ε) (hmε : 8 * log (2 * (J : ℝ) / ε) ≤ m),
    1 - ε ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | (∀ i, i < J →
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
      (pilotStage S J m ρ).upper (pilotStageWord J m ρ ω) i ∧
      (pilotStage S J m ρ).upper (pilotStageWord J m ρ ω) i ≤
      pilotBound μ J ρ (i + 1)) ∧
      ∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
      (pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω) (Set.Iic x)} := @original_pilotStage_event
"""
    bind_restatements(source, NAMES)
    roots = {"ThresholdHC.ArbitraryLawAdaptation." + name for name in NAMES}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", MODULE], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
