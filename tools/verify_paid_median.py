"""Check every conditional capped-median and paid-stage coverage declaration and its transitive axioms.

The statements below are independent, fixed restatements. The audit rejects
unregistered declarations and missing reports and never changes evidence.
"""

import subprocess

from verify_blind_upper_components import (
    FORBIDDEN, LEAN, bind_restatements, registered_names, strip_comments, validate_reports,
)

MODULES = ["ThresholdHC.RobustContinuation." + name for name in
           ("ReferenceBase", "CappedMedian", "PaidCoverage", "PaidMedian")]
SOURCES = [LEAN / (name.replace(".", "/") + ".lean") for name in MODULES]
NAMES = [
    'ValidReference', 'referenceRadius', 'plannedCoefficient_ge_one',
    'referenceRadius_nonneg', 'ofReal_referenceRadius', 'reference_base_exists',
    'ReferenceSeed', 'referenceSeedMeasurableSpace', 'referenceBase',
    'referenceBase_valid', 'medianBaseBudget', 'medianCopyCap',
    'medianRadius', 'medianRadius_nonneg', 'medianRadius_le',
    'reference_median_coverage', 'measurable_median_reader', 'medianWord',
    'measurable_medianWord', 'medianWord_output', 'MedianSeed',
    'medianStage', 'medianStage_radius', 'intervalFailure',
    'measurableSet_intervalFailure', 'intervalFailure_center', 'measurable_tableInterval',
    'learnedStage_restrict_interval_law', 'original_restrict_interval_law', 'measurable_endpoints',
    'original_pilot_probability', 'original_conditional_interval_law', 'learnedStage_failure_le',
    'learnedLaw_support', 'learnedLaw_valid', 'medianStage_seed_law',
    'medianStage_fixed_interval_law', 'failureProbability_simulation', 'medianStage_fixed_failure',
    'paidMedianStage', 'median_reservations_le', 'paidMedianStage_cap',
    'paidMedianStage_reported_radius', 'paidMedianStage_fixed_failure', 'paidMedianStage_conditional_coverage',
    'paidMedianStage_pilot_failure', 'paidMedianStage_coverage', 'paidMedianStage_at_level',
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
        raise ValueError("Unregistered or missing paid-median declaration")
    source = """
import ThresholdHC.RobustContinuation.PaidMedian
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open ThresholdHC.RobustContinuation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.KnownLawPlanner
open ThresholdHC.HardBudget ThresholdHC.ConfidenceProgram ThresholdHC.Confidence
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper

example : ∀ (α : Measure ℝ) (ρ b : ℝ), ValidReference α ρ b ↔
    IsProbabilityMeasure α ∧ α (Set.Icc 0 (1/2))ᶜ = 0 ∧ 0 < ρ ∧ ρ ≤ 1/4 ∧ 0 < b := by intros; rfl
example : ∀ (α : Measure ℝ) (ρ b : ℝ), referenceRadius α ρ b =
    plannedCoefficient 28000 * (zeroSelection α ρ b).toReal := by intros; rfl
example : ∀ (α : Measure ℝ) (ρ b : ℝ), ReferenceSeed α ρ b =
    (reference_base_exists α ρ b).choose := by intros; rfl
example : ∀ (α : Measure ℝ) (ρ b : ℝ), referenceSeedMeasurableSpace α ρ b =
    (reference_base_exists α ρ b).choose_spec.choose := by intros; rfl
example : ∀ (α : Measure ℝ) (ρ b : ℝ), referenceBase α ρ b =
    (reference_base_exists α ρ b).choose_spec.choose_spec.choose := by intros; rfl
example : ∀ (B : ℝ) (m : ℕ), medianBaseBudget B m = B / (8 * (2 * (m : ℝ) + 1)) := by intros; rfl
example : ∀ (B : ℝ) (m : ℕ), medianCopyCap B m = ⌊B / (2 * (m : ℝ) + 1)⌋₊ := by intros; rfl
example : ∀ (α : Measure ℝ) (ρ B : ℝ) (m : ℕ), medianRadius α ρ B m =
    Real.sqrt 8 * referenceRadius α ρ (medianBaseBudget B m) := by intros; rfl
example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (m N : ℕ) (M : ℝ) (r : ℕ → R) (w : List Bool), medianWord A m N M r w =
    median m (fun i => (stageOutput A M (r i.val) (blockAt N i.val w)).getD (M/2)) := by intros; rfl
example : ∀ (ρ B : ℝ) (m : ℕ), MedianSeed ρ B m =
    (∀ α : Measure ℝ, ℕ → ReferenceSeed α ρ (medianBaseBudget B m)) := by intros; rfl
example : ∀ (ρ B : ℝ) (m : ℕ),
    (medianStage ρ B m).randomLaw = Measure.infinitePi (fun α : Measure ℝ =>
      (cappedMedian (referenceBase α ρ (medianBaseBudget B m)) m (medianCopyCap B m) ρ).randomLaw) ∧
    (medianStage ρ B m).pilotCost = 0 ∧
    (medianStage ρ B m).continuationCost = (2*m+1) * medianCopyCap B m ∧
    (medianStage ρ B m).depth = 0 ∧
    (medianStage ρ B m).pilot = (fun _ => 0) ∧
    (medianStage ρ B m).upper = (fun _ _ => 1) ∧
    (medianStage ρ B m).continuation = (fun α r => blockReader (medianCopyCap B m)
      (ThresholdHC.ConfidenceProgram.medianReader (referenceBase α ρ (medianBaseBudget B m)) (r α)) (2*m+1) 0) ∧
    (medianStage ρ B m).interval = (fun α r w =>
      let v := medianWord (referenceBase α ρ (medianBaseBudget B m)) m (medianCopyCap B m) ρ (r α) w
      (v - medianRadius α ρ B m, v + medianRadius α ρ B m)) := by
  intros; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
example : ∀ (θ : ℝ), intervalFailure θ = {I : ℝ × ℝ | θ < I.1 ∨ I.2 < θ} := by intros; rfl
example : ∀ (ρ B : ℝ) (m J k : ℕ), paidMedianStage ρ B m J k =
    pilotStage (medianStage ρ B m) J k ρ := by intros; rfl
example : 1 ≤ plannedCoefficient 28000 := @plannedCoefficient_ge_one

example : ∀ (α : Measure ℝ) (ρ b : ℝ),
    0 ≤ referenceRadius α ρ b := @referenceRadius_nonneg

example : ∀ (α : Measure ℝ) (ρ b : ℝ),
    ENNReal.ofReal (referenceRadius α ρ b) =
      ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection α ρ b := @ofReal_referenceRadius

example : ∀ (α : Measure ℝ) (ρ b : ℝ),
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      ValidReference α ρ b →
      (∀ z, 0 ≤ A.output z ∧ A.output z ≤ ρ) ∧
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        (∀ x, cdf (μ.map Subtype.val) x ≤ cdf α x) →
        RareBudget μ A ρ b ∧ rareRisk μ A ρ ≤ ENNReal.ofReal (referenceRadius α ρ b) := @reference_base_exists

example : ∀ (α : Measure ℝ) (ρ b : ℝ) (hv : ValidReference α ρ b),
    (∀ z, 0 ≤ (referenceBase α ρ b).output z ∧ (referenceBase α ρ b).output z ≤ ρ) ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      (∀ x, cdf (μ.map Subtype.val) x ≤ cdf α x) →
      RareBudget μ (referenceBase α ρ b) ρ b ∧
        rareRisk μ (referenceBase α ρ b) ρ ≤ ENNReal.ofReal (referenceRadius α ρ b) := @referenceBase_valid

example : ∀ (α : Measure ℝ) (ρ B : ℝ) (m : ℕ),
    0 ≤ medianRadius α ρ B m := @medianRadius_nonneg

example : ∀ (α : Measure ℝ) (ρ B : ℝ) (m : ℕ),
    medianRadius α ρ B m ≤ 6 * plannedCoefficient 28000 *
      (zeroSelection α ρ (medianBaseBudget B m)).toReal := @medianRadius_le

example : ∀ (α : Measure ℝ) (ρ B : ℝ) (m : ℕ)
    (hv : ValidReference α ρ (medianBaseBudget B m)) (hB : 0 < B)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (hq : RarePrior μ ρ q)
    (hdom : ∀ x, cdf (μ.map Subtype.val) x ≤ cdf α x),
    PathwiseCap (cappedMedian (referenceBase α ρ (medianBaseBudget B m)) m
      (medianCopyCap B m) ρ) ⌊B⌋₊ ∧
    failureProbability μ (cappedMedian (referenceBase α ρ (medianBaseBudget B m)) m
      (medianCopyCap B m) ρ) q (medianRadius α ρ B m) ≤ ENNReal.ofReal ((3/4:ℝ)^m/2) := @reference_median_coverage

example : ∀ {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) (N k start : ℕ) (w : List Bool),
    Measurable (fun r => blockReader N (medianReader A r) k start w) := @measurable_median_reader

example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (m N : ℕ) (M : ℝ) (w : List Bool),
    Measurable (fun r => medianWord A m N M r w) := @measurable_medianWord

example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (m N : ℕ) (M : ℝ) (r : ℕ → R) (s : Table),
    medianWord A m N M r (readBlock ((2*m+1)*N)
      (blockReader N (medianReader A r) (2*m+1) 0) s).1 =
      (cappedMedian A m N M).output (r, populationPath ((cappedMedian A m N M).policy r) s) := @medianWord_output

example : ∀ (ρ B : ℝ) (m : ℕ) (α : Measure ℝ)
    (r : MedianSeed ρ B m) (w : List Bool),
    ((medianStage ρ B m).interval α r w).2 - ((medianStage ρ B m).interval α r w).1 =
      2 * medianRadius α ρ B m := @medianStage_radius

example : ∀ (θ : ℝ),
    MeasurableSet (intervalFailure θ) := @measurableSet_intervalFailure

example : ∀ (v r θ : ℝ),
    (v-r, v+r) ∈ intervalFailure θ ↔ r < |v-θ| := @intervalFailure_center

example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R),
    Measurable (fun z : R × Table => S.tableInterval z.1 z.2) := @measurable_tableInterval

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R) (q : SignLaw)
    (xs : List Bool),
    ((originalSimulationLaw μ (S.endpoint false) q).restrict
      {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs}).map
      (fun z => S.tableInterval z.1 z.2) =
      ((originalSimulationLaw μ (S.endpoint false) q)
        {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs}) •
      (originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.interval (S.learnedLaw xs) z.1
          (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1) := @learnedStage_restrict_interval_law

example : ∀ {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (xs : List Bool),
    ((experimentLaw μ (S.endpoint false) q).restrict
      {z | (processHistory z.2 S.cap).take S.pilotCost = xs}).map
      (fun z => ((S.endpoint false).output (z.1.1,z.2),
        (S.endpoint true).output (z.1.1,z.2))) =
      ((originalSimulationLaw μ (S.endpoint false) q).restrict
        {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs}).map
        (fun z => S.tableInterval z.1 z.2) := @original_restrict_interval_law

example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R),
    Measurable (fun z : PopulationSeed R × ProcessTape =>
      ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))) := @measurable_endpoints

example : ∀ {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (xs : List Bool),
    (experimentLaw μ (S.endpoint false) q)
      {z | (processHistory z.2 S.cap).take S.pilotCost = xs} =
      (originalSimulationLaw μ (S.endpoint false) q)
        {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs} := @original_pilot_probability

example : ∀ {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (xs : List Bool)
    (hxs : (experimentLaw μ (S.endpoint false) q)
      {z | (processHistory z.2 S.cap).take S.pilotCost = xs} ≠ 0),
    (((experimentLaw μ (S.endpoint false) q)
      {z | (processHistory z.2 S.cap).take S.pilotCost = xs})⁻¹ •
      (experimentLaw μ (S.endpoint false) q).restrict
        {z | (processHistory z.2 S.cap).take S.pilotCost = xs}).map
      (fun z => ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))) =
      (originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.interval (S.learnedLaw xs) z.1
          (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1) := @original_conditional_interval_law

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R) (q : SignLaw)
    (good : List Bool → Prop) (θ : ℝ) (δ : ℝ≥0∞)
    (hf : ∀ xs, good xs →
      ((originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.interval (S.learnedLaw xs) z.1
          (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1))
        (intervalFailure θ) ≤ δ),
    ((experimentLaw μ (S.endpoint false) q).map (fun z =>
      ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))))
      (intervalFailure θ) ≤
      (originalSimulationLaw μ (S.endpoint false) q)
        {z | ¬good (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1} + δ := @learnedStage_failure_le

example : ∀ {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (xs : List Bool),
    S.learnedLaw xs (Set.Icc 0 (1/2))ᶜ = 0 := @learnedLaw_support

example : ∀ {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (xs : List Bool) {ρ B : ℝ} (m : ℕ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B),
    ValidReference (S.learnedLaw xs) ρ (medianBaseBudget B m) := @learnedLaw_valid

example : ∀ (ρ B : ℝ) (m : ℕ) (α : Measure ℝ)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (originalSimulationLaw μ ((medianStage ρ B m).endpoint false) q).map
      (fun z => (z.1 α, z.2)) =
      originalSimulationLaw μ (cappedMedian (referenceBase α ρ (medianBaseBudget B m))
        m (medianCopyCap B m) ρ) q := @medianStage_seed_law

example : ∀ (ρ B : ℝ) (m : ℕ) (α : Measure ℝ)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (originalSimulationLaw μ ((medianStage ρ B m).endpoint false) q).map
      (fun z => (medianStage ρ B m).interval α z.1
        (readBlock (medianStage ρ B m).continuationCost
          ((medianStage ρ B m).continuation α z.1) z.2).1) =
      (originalSimulationLaw μ (cappedMedian (referenceBase α ρ (medianBaseBudget B m))
        m (medianCopyCap B m) ρ) q).map (fun z =>
          let v := (cappedMedian (referenceBase α ρ (medianBaseBudget B m))
            m (medianCopyCap B m) ρ).output
              (z.1, populationPath ((cappedMedian (referenceBase α ρ (medianBaseBudget B m))
                m (medianCopyCap B m) ρ).policy z.1) z.2)
          (v - medianRadius α ρ B m, v + medianRadius α ρ B m)) := @medianStage_fixed_interval_law

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q : SignLaw) (r : ℝ),
    failureProbability μ A q r = (originalSimulationLaw μ A q)
      {z | r < |A.output (z.1,populationPath (A.policy z.1) z.2)-signMean μ q.val|} := @failureProbability_simulation

example : ∀ (ρ B : ℝ) (m : ℕ) (α : Measure ℝ)
    (hv : ValidReference α ρ (medianBaseBudget B m)) (hB : 0 < B)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (hq : RarePrior μ ρ q)
    (hdom : ∀ x, cdf (μ.map Subtype.val) x ≤ cdf α x),
    ((originalSimulationLaw μ ((medianStage ρ B m).endpoint false) q).map
      (fun z => (medianStage ρ B m).interval α z.1
        (readBlock (medianStage ρ B m).continuationCost
          ((medianStage ρ B m).continuation α z.1) z.2).1))
      (intervalFailure (signMean μ q.val)) ≤ ENNReal.ofReal ((3/4:ℝ)^m/2) := @medianStage_fixed_failure

example : ∀ {B : ℝ} (hB : 0 < B) (m : ℕ),
    (2*m+1) * medianCopyCap B m ≤ ⌊B⌋₊ := @median_reservations_le

example : ∀ {ρ B : ℝ} (hB : 0 < B) (m J k : ℕ) (upper : Bool),
    PathwiseCap ((paidMedianStage ρ B m J k).endpoint upper) (k * pilotSpan J + ⌊B⌋₊) := @paidMedianStage_cap

example : ∀ (ρ B : ℝ) (m J k : ℕ)
    (r : MedianSeed ρ B m) (w : List Bool),
    let S := paidMedianStage ρ B m J k
    (S.historyInterval r w).2 - (S.historyInterval r w).1 =
      2 * medianRadius (S.learnedLaw (w.take S.pilotCost)) ρ B m := @paidMedianStage_reported_radius

example : ∀ {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hB : 0 < B) (m J k : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (hq : RarePrior μ ρ q) (xs : List Bool)
    (hdom : ∀ x, (μ.map Subtype.val) (Set.Iic x) ≤
      (paidMedianStage ρ B m J k).learnedLaw xs (Set.Iic x)),
    let S := paidMedianStage ρ B m J k
    ((originalSimulationLaw μ (S.endpoint false) q).map
      (fun z => S.interval (S.learnedLaw xs) z.1
        (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1))
      (intervalFailure (signMean μ q.val)) ≤ ENNReal.ofReal ((3/4:ℝ)^m/2) := @paidMedianStage_fixed_failure

example : ∀ {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hB : 0 < B) (m J k : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (hq : RarePrior μ ρ q) (xs : List Bool)
    (hdom : ∀ x, (μ.map Subtype.val) (Set.Iic x) ≤
      (paidMedianStage ρ B m J k).learnedLaw xs (Set.Iic x))
    (hxs : (experimentLaw μ ((paidMedianStage ρ B m J k).endpoint false) q)
      {z | (processHistory z.2 (paidMedianStage ρ B m J k).cap).take
        (paidMedianStage ρ B m J k).pilotCost = xs} ≠ 0),
    let S := paidMedianStage ρ B m J k
    ((((experimentLaw μ (S.endpoint false) q)
      {z | (processHistory z.2 S.cap).take S.pilotCost = xs})⁻¹ •
      (experimentLaw μ (S.endpoint false) q).restrict
        {z | (processHistory z.2 S.cap).take S.pilotCost = xs}).map
      (fun z => ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))))
      (intervalFailure (signMean μ q.val)) ≤ ENNReal.ofReal ((3/4:ℝ)^m/2) := @paidMedianStage_conditional_coverage

example : ∀ {ρ B ε : ℝ} (hρ : 0 < ρ) (m J k : ℕ)
    (hJ : 1 ≤ J) (hk : 0 < k) (hε : 0 < ε) (hkε : 8 * Real.log (2 * (J : ℝ) / ε) ≤ k)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    let S := paidMedianStage ρ B m J k
    (originalSimulationLaw μ (S.endpoint false) q)
      {z | ¬∀ x, (μ.map Subtype.val) (Set.Iic x) ≤
        S.learnedLaw (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 (Set.Iic x)} ≤
      ENNReal.ofReal ε := @paidMedianStage_pilot_failure

example : ∀ {ρ B ε : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hB : 0 < B) (m J k : ℕ) (hJ : 1 ≤ J) (hk : 0 < k) (hε : 0 < ε)
    (hkε : 8 * Real.log (2 * (J : ℝ) / ε) ≤ k)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (hq : RarePrior μ ρ q),
    let S := paidMedianStage ρ B m J k
    ((experimentLaw μ (S.endpoint false) q).map (fun z =>
      ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))))
      (intervalFailure (signMean μ q.val)) ≤ ENNReal.ofReal ε + ENNReal.ofReal ((3/4:ℝ)^m/2) := @paidMedianStage_coverage

example : ∀ {ρ B ε δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hB : 0 < B) (hδ : 0 < δ) (J k : ℕ) (hJ : 1 ≤ J) (hk : 0 < k) (hε : 0 < ε)
    (hkε : 8 * Real.log (2 * (J : ℝ) / ε) ≤ k)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (hq : RarePrior μ ρ q),
    let S := paidMedianStage ρ B (groups δ) J k
    PathwiseCap (S.endpoint false) (k * pilotSpan J + ⌊B⌋₊) ∧
    ((experimentLaw μ (S.endpoint false) q).map (fun z =>
      ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))))
      (intervalFailure (signMean μ q.val)) ≤ ENNReal.ofReal (ε + δ) := @paidMedianStage_at_level
"""
    if source.count("example ") != len(NAMES):
        raise ValueError("Each paid-median declaration needs one restated statement")
    bind_restatements(source, NAMES)
    roots = {"ThresholdHC.RobustContinuation." + name for name in NAMES}
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
