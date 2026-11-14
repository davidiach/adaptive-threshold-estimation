"""Audit the median tail certificate of the arbitrary-law tail certificate.

Every definition and theorem of the three tail-median modules is restated in
full, so a changed definition, hypothesis or constant is an elaboration error,
and the transitive axioms of every declaration are reported. A declaration in
those modules that is not registered here is an error. Prints the kernel
report; writes nothing.
"""

import subprocess
from verify_blind_upper_components import (FORBIDDEN, LEAN, bind_restatements,
                                           registered_names, strip_comments,
                                           validate_reports)

MODULE = "ThresholdHC.ArbitraryLawAdaptation.TailMedianLaw"
SOURCES = [LEAN / "ThresholdHC/ArbitraryLawAdaptation" / (name + ".lean")
           for name in ("TailMedian", "TailMedianProbability", "TailMedianLaw")]
NAMES = [
    "blockCount", "blockMedian", "medianUpper", "medianFlips", "blockCount_le", "blockCount_mono",
    "card_le_blockCount", "blockCount_add_not", "blockMedian_zero", "blockMedian_eq_value",
    "blockMedian_le", "le_blockMedian", "medianUpper_pos", "medianUpper_le_one", "medianFlips_le",
    "medianFlips_le_common", "blockBits", "measurable_decide_mem", "measurable_blockBits",
    "tailHeads_blockBits", "map_decide_mem", "blockBits_law", "measurableSet_blockMajority",
    "blocks_fail_le", "blocks_majority", "measurableSet_blockMinority", "probeValidSet",
    "probeTightSet", "medianFailure", "measurableSet_probeValidSet", "measurableSet_probeTightSet",
    "measurableSet_medianFailure", "median_good_of_not_failure", "stream_medianFailure_le",
    "stream_median_certificate", "two_exp_le_of_log_le", "depth_weight_sum_le",
    "depth_union_bound", "infinitePi_map_blocks", "infinitePi_map_depth_blocks",
    "one_sub_le_real_preimage", "measurableSet_exists_depth", "tail_bound_uncapped",
    "original_medianFailure_le", "original_median_certificate_exp", "original_median_certificate",
    "original_tail_certificate", "original_depthFailure_le", "original_median_all_depths",
    "original_tail_certificate_array", "original_median_all_depths_array",
]


def declared_names():
    """Every declaration of the three modules, after rejecting proof escapes."""
    found = []
    for path in SOURCES:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        found += registered_names(source)
    return found


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing tail-median declaration")
    source = """
import ThresholdHC.ArbitraryLawAdaptation.TailMedianLaw
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.Tier2 ThresholdHC.Tier6
open ThresholdHC.Uniform713 ThresholdHC.EntropyTailUpper ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

open Classical in
example : ∀ (m : ℕ) (p : ℕ → Prop),
    blockCount m p = ((Finset.range m).filter p).card := fun _ _ => rfl
example : ∀ (m : ℕ) (v : ℕ → ℝ), blockMedian m v =
    if h : 0 < m then
      v (Tuple.sort (fun j : Fin m => v j) ⟨m / 2, Nat.div_lt_self h (by norm_num)⟩)
    else 1 := fun _ _ => rfl
example : ∀ (J m : ℕ) (b M : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → Bool), medianUpper J m b M ω =
    blockMedian m (fun j => probeUpper (probeCompleted J (b j) (M j) (ω j))) :=
  fun _ _ _ _ _ => rfl
example : ∀ (J m : ℕ) (b M : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → Bool), medianFlips J m b M ω =
    ∑ j ∈ Finset.range m, probeFlips J (b j) (M j) (ω j) := fun _ _ _ _ _ => rfl
open Classical in
example : ∀ {X : Type*} (B : Set X) (ω : ℕ → X) (j : ℕ),
    blockBits B ω j = decide (ω j ∈ B) := fun _ _ _ => rfl
example : ∀ (J : ℕ) (F : ℝ), probeValidSet J F =
    {s | ∀ b M, F ≤ probeUpper (probeCompleted J b M s)} := fun _ _ => rfl
example : ∀ (J b M : ℕ) (c : ℝ), probeTightSet J b M c =
    {s | probeUpper (probeCompleted J b M s) ≤ c} := fun _ _ _ _ => rfl
example : ∀ (J m b M : ℕ) (F c : ℝ), medianFailure J m b M F c =
    {ω | 2 * blockCount m (fun j => ω j ∈ probeValidSet J F) ≤ m} ∪
      {ω | 2 * blockCount m (fun j => ω j ∈ probeTightSet J b M c) ≤ m} :=
  fun _ _ _ _ _ _ => rfl

example : ∀ (m : ℕ) (p : ℕ → Prop),
    blockCount m p ≤ m := @blockCount_le
example : ∀ {m : ℕ} {p q : ℕ → Prop} (h : ∀ j < m, p j → q j),
    blockCount m p ≤ blockCount m q := @blockCount_mono
example : ∀ {m : ℕ} {p : ℕ → Prop} (T : Finset ℕ) (hT : ∀ j ∈ T, j < m ∧ p j),
    T.card ≤ blockCount m p := @card_le_blockCount
example : ∀ (m : ℕ) (p : ℕ → Prop),
    blockCount m p + blockCount m (fun j => ¬ p j) = m := @blockCount_add_not
example : ∀ (v : ℕ → ℝ),
    blockMedian 0 v = 1 := @blockMedian_zero
example : ∀ {m : ℕ} (hm : 0 < m) (v : ℕ → ℝ),
    ∃ j < m, blockMedian m v = v j := @blockMedian_eq_value
example : ∀ {m : ℕ} {v : ℕ → ℝ} {c : ℝ} (h : m < 2 * blockCount m (fun j => v j ≤ c)),
    blockMedian m v ≤ c := @blockMedian_le
example : ∀ {m : ℕ} {v : ℕ → ℝ} {a : ℝ} (h : m < 2 * blockCount m (fun j => a ≤ v j)),
    a ≤ blockMedian m v := @le_blockMedian
example : ∀ (J m : ℕ) (b M : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → Bool),
    0 < medianUpper J m b M ω := @medianUpper_pos
example : ∀ (J m : ℕ) (b M : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → Bool),
    medianUpper J m b M ω ≤ 1 := @medianUpper_le_one
example : ∀ (J m : ℕ) (b M : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → Bool),
    medianFlips J m b M ω ≤ ∑ j ∈ Finset.range m, b j := @medianFlips_le
example : ∀ (J m b : ℕ) (M : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → Bool),
    medianFlips J m (fun _ => b) M ω ≤ m * b := @medianFlips_le_common
open Classical in
example : ∀ {X : Type*} [MeasurableSpace X] {B : Set X} (hB : MeasurableSet B),
    Measurable (fun x : X => decide (x ∈ B)) := @measurable_decide_mem
example : ∀ {X : Type*} [MeasurableSpace X] {B : Set X} (hB : MeasurableSet B),
    Measurable (blockBits B) := @measurable_blockBits
example : ∀ {X : Type*} (m : ℕ) (B : Set X) (ω : ℕ → X),
    tailHeads m (blockBits B ω) = blockCount m (fun j => ω j ∈ B) := @tailHeads_blockBits
open Classical in
example : ∀ {X : Type*} [MeasurableSpace X] (S : Measure X) [IsProbabilityMeasure S] {B : Set X} (hB : MeasurableSet B),
    S.map (fun x : X => decide (x ∈ B)) =
      bernoulliMeasure true false ⟨S.real B, measureReal_nonneg, measureReal_le_one⟩ := @map_decide_mem
example : ∀ {X : Type*} [MeasurableSpace X] (S : Measure X) [IsProbabilityMeasure S] {B : Set X} (hB : MeasurableSet B),
    (Measure.infinitePi (fun _ : ℕ => S)).map (blockBits B) =
      tapeMeasure ⟨S.real B, measureReal_nonneg, measureReal_le_one⟩ := @blockBits_law
example : ∀ {X : Type*} [MeasurableSpace X] {B : Set X} (hB : MeasurableSet B) (m : ℕ),
    MeasurableSet {ω : ℕ → X | m ≤ 2 * blockCount m (fun j => ω j ∈ B)} := @measurableSet_blockMajority
example : ∀ {X : Type*} [MeasurableSpace X] (S : Measure X) [IsProbabilityMeasure S] {B : Set X} (hB : MeasurableSet B) (hp : S.real B ≤ 1 / 4) {m : ℕ} (hm : 0 < m),
    (Measure.infinitePi (fun _ : ℕ => S)).real
      {ω | m ≤ 2 * blockCount m (fun j => ω j ∈ B)} ≤ exp (-(m : ℝ) / 8) := @blocks_fail_le
example : ∀ {X : Type*} [MeasurableSpace X] (S : Measure X) [IsProbabilityMeasure S] {G : Set X} (hG : MeasurableSet G) (hp : 3 / 4 ≤ S.real G) {m : ℕ} (hm : 0 < m),
    (Measure.infinitePi (fun _ : ℕ => S)).real
      {ω | 2 * blockCount m (fun j => ω j ∈ G) ≤ m} ≤ exp (-(m : ℝ) / 8) := @blocks_majority
example : ∀ {X : Type*} [MeasurableSpace X] {G : Set X} (hG : MeasurableSet G) (m : ℕ),
    MeasurableSet {ω : ℕ → X | 2 * blockCount m (fun j => ω j ∈ G) ≤ m} := @measurableSet_blockMinority
example : ∀ (J : ℕ) (F : ℝ),
    MeasurableSet (probeValidSet J F) := @measurableSet_probeValidSet
example : ∀ (J b M : ℕ) (c : ℝ),
    MeasurableSet (probeTightSet J b M c) := @measurableSet_probeTightSet
example : ∀ (J m b M : ℕ) (F c : ℝ),
    MeasurableSet (medianFailure J m b M F c) := @measurableSet_medianFailure
example : ∀ {J m b M : ℕ} {F c : ℝ} {ω : ℕ → ℕ → ℕ → Bool} (h : ω ∉ medianFailure J m b M F c),
    (∀ b' M' : ℕ → ℕ, F ≤ medianUpper J m b' M' ω) ∧
      medianUpper J m (fun _ => b) (fun _ => M) ω ≤ c := @median_good_of_not_failure
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M) {F W : ℝ} (hF1 : F ≤ 1) (hFu : F ≤ 2 * ν.real {t | tailUnresolved J t}) (hW : ∫ t, (tailWork J t : ℝ) ∂ν ≤ W),
    (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν))).real
      (medianFailure J m b M F
      (min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M)))) ≤
      2 * exp (-(m : ℝ) / 8) := @stream_medianFailure_le
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M) {F W : ℝ} (hF1 : F ≤ 1) (hFu : F ≤ 2 * ν.real {t | tailUnresolved J t}) (hW : ∫ t, (tailWork J t : ℝ) ∂ν ≤ W),
    1 - 2 * exp (-(m : ℝ) / 8) ≤
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν))).real
      {ω | (∀ b' M' : ℕ → ℕ, F ≤ medianUpper J m b' M' ω) ∧
      medianUpper J m (fun _ => b) (fun _ => M) ω ≤
      min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M))} := @stream_median_certificate
example : ∀ {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (hm : 8 * log (2 / δ) ≤ m),
    2 * exp (-(m : ℝ) / 8) ≤ δ := @two_exp_le_of_log_le
example : ∀ {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ),
    ∑ J ∈ Finset.range n, δ / ((J : ℝ) * (J + 1)) ≤ δ := @depth_weight_sum_le
example : ∀ {Y : Type*} [MeasurableSpace Y] (P : Measure Y) [IsProbabilityMeasure P] (Bad : ℕ → Set Y) (hmeas : ∀ J, MeasurableSet (Bad J)) {δ : ℝ} (hδ : 0 ≤ δ) (hbad : ∀ J, 1 ≤ J → P.real (Bad J) ≤ δ / ((J : ℝ) * (J + 1))),
    (Measure.infinitePi (fun _ : ℕ => P)).real {ω | ∃ J, 1 ≤ J ∧ ω J ∈ Bad J} ≤ δ := @depth_union_bound
example : ∀ {X : Type*} [MeasurableSpace X] (S : Measure X) [IsProbabilityMeasure S],
    (Measure.infinitePi (fun _ : ℕ => S)).map (fun (ω : ℕ → X) (j i : ℕ) => ω (Nat.pair j i)) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => S)) := @infinitePi_map_blocks
example : ∀ {X : Type*} [MeasurableSpace X] (S : Measure X) [IsProbabilityMeasure S],
    (Measure.infinitePi (fun _ : ℕ => S)).map
      (fun (ω : ℕ → X) (J j i : ℕ) => ω (Nat.pair J (Nat.pair j i))) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => S))) := @infinitePi_map_depth_blocks
example : ∀ {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] (P : Measure Y) [IsProbabilityMeasure P] {f : Y → Z} (hf : Measurable f) {Bad Good : Set Z} (hBad : MeasurableSet Bad) (hcover : ∀ z, z ∉ Bad → z ∈ Good) {ε : ℝ} (h : (P.map f).real Bad ≤ ε),
    1 - ε ≤ P.real (f ⁻¹' Good) := @one_sub_le_real_preimage
example : ∀ {Y : Type*} [MeasurableSpace Y] (Bad : ℕ → Set Y) (hmeas : ∀ J, MeasurableSet (Bad J)),
    MeasurableSet {ω : ℕ → Y | ∃ J, 1 ≤ J ∧ ω J ∈ Bad J} := @measurableSet_exists_depth
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (J : ℕ),
    min 1 (128 * max (max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / ((4 ^ J : ℕ) : ℝ))) (1 / ((4 ^ J : ℕ) : ℝ))) =
      min 1 (128 * max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J)) := @tail_bound_uncapped
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M),
    (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).real
      (medianFailure J m b M (μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J})
      (min 1 (128 * max (max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M)))) ≤
      2 * exp (-(m : ℝ) / 8) := @original_medianFailure_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M),
    1 - 2 * exp (-(m : ℝ) / 8) ≤
      (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).real
      {ω | (∀ b' M' : ℕ → ℕ,
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' ω) ∧
      medianUpper J m (fun _ => b) (fun _ => M) ω ≤
      min 1 (128 * max (max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} := @original_median_certificate_exp
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).real
      {ω | (∀ b' M' : ℕ → ℕ,
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' ω) ∧
      medianUpper J m (fun _ => b) (fun _ => M) ω ≤
      min 1 (128 * max (max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} := @original_median_certificate
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).real
      {ω | (∀ b' M' : ℕ → ℕ,
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' ω) ∧
      medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J) ω ≤
      min 1 (128 * max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J))} := @original_tail_certificate
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (m b M : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J) (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J) (hb : ∀ J : ℕ, 1 ≤ J → 0 < b J) (hM : ∀ J : ℕ, 1 ≤ J → 0 < M J),
    (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))).real
      {ω | ∃ J, 1 ≤ J ∧ ω J ∈ medianFailure J (m J) (b J) (M J)
      (μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J})
      (min 1 (128 * max (max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J)))} ≤ δ := @original_depthFailure_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (m b M : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J) (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J) (hb : ∀ J : ℕ, 1 ≤ J → 0 < b J) (hM : ∀ J : ℕ, 1 ≤ J → 0 < M J),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))).real
      {ω | ∀ J, 1 ≤ J →
      (∀ b' M' : ℕ → ℕ,
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J (m J) b' M' (ω J)) ∧
      medianUpper J (m J) (fun _ => b J) (fun _ => M J) (ω J) ≤
      min 1 (128 * max (max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J))} := @original_median_all_depths
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianUpper J m b' M' (fun j i => ω (Nat.pair j i))) ∧
      medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J) (fun j i => ω (Nat.pair j i)) ≤
      min 1 (128 * max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J))} := @original_tail_certificate_array
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (m b M : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J) (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J) (hb : ∀ J : ℕ, 1 ≤ J → 0 < b J) (hM : ∀ J : ℕ, 1 ≤ J → 0 < M J),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | ∀ J, 1 ≤ J →
      (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianUpper J (m J) b' M' (fun j i => ω (Nat.pair J (Nat.pair j i)))) ∧
      medianUpper J (m J) (fun _ => b J) (fun _ => M J)
      (fun j i => ω (Nat.pair J (Nat.pair j i))) ≤
      min 1 (128 * max (max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J))} := @original_median_all_depths_array
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
