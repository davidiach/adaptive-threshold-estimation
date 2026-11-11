"""Audit the tail certificate in the observable experiment.

Every definition and theorem of the three modules that run the tail probes as
readers of observed flips is restated in full, so a changed definition,
hypothesis or constant is an elaboration error, and the transitive axioms of
every declaration are reported. A declaration in those modules that is not
registered here is an error. Prints the kernel report; writes nothing.
"""

import subprocess
from verify_blind_upper_components import (DECLARATION, FORBIDDEN, LEAN, strip_comments,
                                           validate_reports)

MODULE = "ThresholdHC.ArbitraryLawAdaptation.TailObservable"
SOURCES = [LEAN / "ThresholdHC/ArbitraryLawAdaptation" / (name + ".lean")
           for name in ("TailProbeReader", "TailBlockReader", "TailObservable")]
NAMES = [
    "ProbeState", "probeInit", "probeResolved", "probeStep", "probeRun", "probeReader",
    "probeWordCompleted", "probeRun_append", "probeResolved_iff", "tailHeads_succ",
    "tapeDrop_zero", "tapeDrop_one_drop", "readBlock_succ_snoc", "readBlock_take",
    "probeCompleted_zero", "probeCompleted_eq", "probeCompleted_step_unfinished",
    "probeCompleted_step_stopped", "probeAdmits_succ", "probeAdmits_one", "ProbeInv",
    "probeInv_zero", "probeInv_step", "probeInv_readBlock", "probeReader_schedule",
    "probeWordCompleted_readBlock", "probeWordCompleted_take", "seqOffset", "seqReader", "seqWord",
    "seqOffset_zero", "seqOffset_succ", "seqOffset_const", "seqOffset_mono",
    "seqReader_succ_of_lt", "seqReader_readBlock", "seqWord_take", "blockMedian_congr",
    "medianReader", "medianWordUpper", "medianWordUpper_readBlock", "medianWordUpper_take",
    "depthsCost", "depthsReader", "depthWordUpper", "depthWordUpper_readBlock",
    "depthWordUpper_take", "wordEstimator", "wordEstimator_cap", "wordEstimator_history",
    "wordEstimator_output", "original_word_event", "observable_of_array",
    "original_median_certificate_array", "tailEstimator", "tailEstimator_cap",
    "tailEstimator_output", "observable_median_certificate", "observable_tail_certificate",
    "observable_tail_oracle", "observable_tail_oracle_eventually", "depthsEstimator",
    "depthsEstimator_cap", "depthsEstimator_policy", "depthsEstimator_output",
    "observable_median_depths", "observable_tail_oracle_depths",
    "observable_tail_oracle_depths_eventually",
]


def declared_names():
    """Every declaration of the three modules, after rejecting proof escapes."""
    found = []
    for path in SOURCES:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        found += DECLARATION.findall(source)
    return found


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing tail-observable declaration")
    source = """
import ThresholdHC.ArbitraryLawAdaptation.TailObservable
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier6
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailQuantile
open ThresholdHC.HardBudget ThresholdHC.BlindUpper

example : ∀ (c l n h k : ℕ) (b : Bool),
    (ProbeState.mk c l n h k b).coin = c ∧ (ProbeState.mk c l n h k b).level = l ∧
      (ProbeState.mk c l n h k b).len = n ∧ (ProbeState.mk c l n h k b).heads = h ∧
      (ProbeState.mk c l n h k b).count = k ∧ (ProbeState.mk c l n h k b).stopped = b :=
  fun _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
example : ∀ (M : ℕ), probeInit M = ⟨0, 0, 0, 0, 0, decide (M = 0)⟩ := fun _ => rfl
example : ∀ (J k h : ℕ), probeResolved J k h =
    decide (2 * (tailThreshold J k : ℤ) < |2 * (h : ℤ) - ((4 ^ k : ℕ) : ℤ)|) := fun _ _ _ => rfl
example : ∀ (J M : ℕ) (st : ProbeState) (b : Bool), probeStep J M st b =
    if st.len + 1 = 4 ^ st.level then
      if J ≤ st.level ∨ probeResolved J st.level (st.heads + b.toNat) = true then
        { coin := st.coin + 1, level := 0, len := 0, heads := 0,
          count := if st.stopped = true then st.count else st.count + 1,
          stopped := st.stopped || !probeResolved J st.level (st.heads + b.toNat) ||
            decide (M < st.coin + 2) }
      else
        { st with level := st.level + 1, len := st.len + 1, heads := st.heads + b.toNat }
    else
      { st with len := st.len + 1, heads := st.heads + b.toNat } := fun _ _ _ _ => rfl
example : ∀ (J M : ℕ) (w : List Bool),
    probeRun J M w = w.foldl (probeStep J M) (probeInit M) := fun _ _ _ => rfl
example : ∀ (J M : ℕ), probeReader J M = fun w => (probeRun J M w).coin := fun _ _ => rfl
example : ∀ (J M : ℕ) (w : List Bool),
    probeWordCompleted J M w = (probeRun J M w).count := fun _ _ _ => rfl
example : ∀ (J M : ℕ) (s : Table) (t : ℕ) (st : ProbeState) (tbl : Table),
    ProbeInv J M s t st tbl ↔
      probeWork J s st.coin + st.len = t ∧ st.heads = tailHeads st.len (s st.coin) ∧
        st.len < 4 ^ st.level ∧ st.level ≤ tailStop J (s st.coin) ∧
        tbl st.coin = tapeDrop st.len (s st.coin) ∧ (∀ j, st.coin < j → tbl j = s j) ∧
        st.count = probeCompleted J t M s ∧
        (st.stopped = true ↔ ¬ probeAdmits J M s (st.coin + 1)) :=
  fun _ _ _ _ _ _ =>
    ⟨fun h => ⟨h.time, h.heads, h.len_lt, h.level_le, h.tape, h.fresh, h.count, h.stopped⟩,
      fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2⟩⟩
example : ∀ (len : ℕ → ℕ) (n : ℕ),
    seqOffset len n = ∑ k ∈ Finset.range n, len k := fun _ _ => rfl
example : ∀ (len : ℕ → ℕ) (p : ℕ → Reader),
    seqReader len p 0 = (fun _ => 0) ∧ ∀ n, seqReader len p (n + 1) =
      thenRead (seqOffset len n) (seqReader len p n) (Nat.pair n ∘ p n) :=
  fun _ _ => ⟨rfl, fun _ => rfl⟩
example : ∀ (len : ℕ → ℕ) (n : ℕ) (w : List Bool),
    seqWord len n w = (w.drop (seqOffset len n)).take (len n) := fun _ _ _ => rfl
example : ∀ (J M b m : ℕ),
    medianReader J M b m = seqReader (fun _ => b) (fun _ => probeReader J M) m :=
  fun _ _ _ _ => rfl
example : ∀ (J m b M : ℕ) (w : List Bool), medianWordUpper J m b M w =
    blockMedian m (fun j => probeUpper (probeWordCompleted J M (seqWord (fun _ => b) j w))) :=
  fun _ _ _ _ _ => rfl
example : ∀ (m b : ℕ → ℕ) (N : ℕ),
    depthsCost m b N = seqOffset (fun J => m J * b J) N := fun _ _ _ => rfl
example : ∀ (m b M : ℕ → ℕ) (N : ℕ), depthsReader m b M N =
    seqReader (fun J => m J * b J) (fun J => medianReader J (M J) (b J) (m J)) N :=
  fun _ _ _ _ => rfl
example : ∀ (m b M : ℕ → ℕ) (J : ℕ) (w : List Bool), depthWordUpper m b M J w =
    medianWordUpper J (m J) (b J) (M J) (seqWord (fun J => m J * b J) J w) :=
  fun _ _ _ _ _ => rfl
example : ∀ (n : ℕ) (p : Reader) (out : List Bool → ℝ),
    (wordEstimator n p out).randomLaw = Measure.dirac () ∧
      (wordEstimator n p out).policy = (fun _ => stopAt n p) ∧
      (wordEstimator n p out).output = fun z => out (processHistory z.2 n) :=
  fun _ _ _ => ⟨rfl, rfl, rfl⟩
example : ∀ (J m b M : ℕ), tailEstimator J m b M =
    wordEstimator (m * b) (medianReader J M b m) (medianWordUpper J m b M) :=
  fun _ _ _ _ => rfl
example : ∀ (m b M : ℕ → ℕ) (L J₀ : ℕ), depthsEstimator m b M L J₀ =
    wordEstimator (depthsCost m b (L + 1)) (depthsReader m b M (L + 1))
      (depthWordUpper m b M J₀) := fun _ _ _ _ _ => rfl

example : ∀ (J M : ℕ) (w : List Bool) (b : Bool),
    probeRun J M (w ++ [b]) = probeStep J M (probeRun J M w) b := @probeRun_append
example : ∀ (J k : ℕ) (ω : ℕ → Bool),
    probeResolved J k (tailHeads (4 ^ k) ω) = true ↔ tailResolvedAt J k ω := @probeResolved_iff
example : ∀ (n : ℕ) (ω : ℕ → Bool),
    tailHeads (n + 1) ω = tailHeads n ω + (ω n).toNat := @tailHeads_succ
example : ∀ (ω : ℕ → Bool),
    tapeDrop 0 ω = ω := @tapeDrop_zero
example : ∀ (n : ℕ) (ω : ℕ → Bool),
    tapeDrop 1 (tapeDrop n ω) = tapeDrop (n + 1) ω := @tapeDrop_one_drop
example : ∀ (n : ℕ) (p : Reader) (s : Table),
    readBlock (n + 1) p s =
      ((readBlock n p s).1 ++ [(readBlock n p s).2 (p (readBlock n p s).1) 0],
      Function.update (readBlock n p s).2 (p (readBlock n p s).1)
      (tapeDrop 1 ((readBlock n p s).2 (p (readBlock n p s).1)))) := @readBlock_succ_snoc
example : ∀ (p : Reader) (s : Table) {n m : ℕ} (h : n ≤ m),
    ((readBlock m p s).1).take n = (readBlock n p s).1 := @readBlock_take
example : ∀ (J M : ℕ) (s : Table),
    probeCompleted J 0 M s = 0 := @probeCompleted_zero
example : ∀ {J M t n : ℕ} {s : Table} (hadm : probeAdmits J M s n) (h1 : probeWork J s n ≤ t) (h2 : t < probeWork J s (n + 1)),
    probeCompleted J t M s = n := @probeCompleted_eq
example : ∀ {J M t i : ℕ} {s : Table} (h1 : probeWork J s i ≤ t) (h2 : t + 1 < probeWork J s (i + 1)),
    probeCompleted J (t + 1) M s = probeCompleted J t M s := @probeCompleted_step_unfinished
example : ∀ {J M t i : ℕ} {s : Table} (h1 : probeWork J s i ≤ t) (hstop : ¬ probeAdmits J M s (i + 1)),
    probeCompleted J (t + 1) M s = probeCompleted J t M s := @probeCompleted_step_stopped
example : ∀ (J M : ℕ) (s : Table) (n : ℕ),
    probeAdmits J M s (n + 2) ↔
      probeAdmits J M s (n + 1) ∧ n + 2 ≤ M ∧ ¬ tailUnresolved J (s n) := @probeAdmits_succ
example : ∀ (J M : ℕ) (s : Table),
    probeAdmits J M s 1 ↔ 1 ≤ M := @probeAdmits_one
example : ∀ (J M : ℕ) (s : Table),
    ProbeInv J M s 0 (probeInit M) s := @probeInv_zero
example : ∀ {J M : ℕ} {s : Table} {t : ℕ} {st : ProbeState} {tbl : Table} (h : ProbeInv J M s t st tbl),
    ProbeInv J M s (t + 1) (probeStep J M st (tbl st.coin 0))
      (Function.update tbl st.coin (tapeDrop 1 (tbl st.coin))) := @probeInv_step
example : ∀ (J M : ℕ) (s : Table) (t : ℕ),
    ProbeInv J M s t (probeRun J M (readBlock t (probeReader J M) s).1)
      (readBlock t (probeReader J M) s).2 := @probeInv_readBlock
example : ∀ (J M : ℕ) (s : Table) (t : ℕ),
    probeWork J s (probeReader J M (readBlock t (probeReader J M) s).1) ≤ t ∧
      t < probeWork J s (probeReader J M (readBlock t (probeReader J M) s).1 + 1) := @probeReader_schedule
example : ∀ (J M b : ℕ) (s : Table),
    probeWordCompleted J M (readBlock b (probeReader J M) s).1 = probeCompleted J b M s := @probeWordCompleted_readBlock
example : ∀ (J M : ℕ) (s : Table) {t b : ℕ} (h : t ≤ b),
    probeWordCompleted J M (((readBlock b (probeReader J M) s).1).take t) =
      probeCompleted J t M s := @probeWordCompleted_take
example : ∀ (len : ℕ → ℕ),
    seqOffset len 0 = 0 := @seqOffset_zero
example : ∀ (len : ℕ → ℕ) (n : ℕ),
    seqOffset len (n + 1) = seqOffset len n + len n := @seqOffset_succ
example : ∀ (b n : ℕ),
    seqOffset (fun _ => b) n = n * b := @seqOffset_const
example : ∀ (len : ℕ → ℕ),
    Monotone (seqOffset len) := @seqOffset_mono
example : ∀ (len : ℕ → ℕ) (p : ℕ → Reader) (n : ℕ) {xs : List Bool} (h : xs.length < seqOffset len n),
    seqReader len p (n + 1) xs = seqReader len p n xs := @seqReader_succ_of_lt
example : ∀ (len : ℕ → ℕ) (p : ℕ → Reader) (s : Table) (N : ℕ),
    (∀ n, n < N → seqWord len n (readBlock (seqOffset len N) (seqReader len p N) s).1 =
      (readBlock (len n) (p n) (fun i => s (Nat.pair n i))).1) ∧
      ∀ n, N ≤ n → ∀ i,
      (readBlock (seqOffset len N) (seqReader len p N) s).2 (Nat.pair n i) =
      s (Nat.pair n i) := @seqReader_readBlock
example : ∀ (len : ℕ → ℕ) (n t : ℕ) (w : List Bool),
    seqWord len n (w.take t) = (seqWord len n w).take (t - seqOffset len n) := @seqWord_take
example : ∀ {m : ℕ} {v v' : ℕ → ℝ} (h : ∀ j, j < m → v j = v' j),
    blockMedian m v = blockMedian m v' := @blockMedian_congr
example : ∀ (J m b M : ℕ) (s : Table),
    medianWordUpper J m b M (readBlock (m * b) (medianReader J M b m) s).1 =
      medianUpper J m (fun _ => b) (fun _ => M) (fun j i => s (Nat.pair j i)) := @medianWordUpper_readBlock
example : ∀ (J m b M t : ℕ) (s : Table),
    medianWordUpper J m b M ((readBlock (m * b) (medianReader J M b m) s).1.take t) =
      medianUpper J m (fun j => min (t - j * b) b) (fun _ => M)
      (fun j i => s (Nat.pair j i)) := @medianWordUpper_take
example : ∀ (m b M : ℕ → ℕ) (N : ℕ) (s : Table) {J : ℕ} (hJ : J < N),
    depthWordUpper m b M J (readBlock (depthsCost m b N) (depthsReader m b M N) s).1 =
      medianUpper J (m J) (fun _ => b J) (fun _ => M J)
      (fun j i => s (Nat.pair J (Nat.pair j i))) := @depthWordUpper_readBlock
example : ∀ (m b M : ℕ → ℕ) (N : ℕ) (s : Table) {J : ℕ} (hJ : J < N) (t : ℕ),
    depthWordUpper m b M J
      ((readBlock (depthsCost m b N) (depthsReader m b M N) s).1.take t) =
      medianUpper J (m J) (fun j => min (t - depthsCost m b J - j * b J) (b J))
      (fun _ => M J) (fun j i => s (Nat.pair J (Nat.pair j i))) := @depthWordUpper_take
example : ∀ (n : ℕ) (p : Reader) (out : List Bool → ℝ),
    PathwiseCap (wordEstimator n p out) n := @wordEstimator_cap
example : ∀ (n : ℕ) (p : Reader) (s : Table),
    processHistory (populationPath (stopAt n p) s) n = (readBlock n p s).1 := @wordEstimator_history
example : ∀ (n : ℕ) (p : Reader) (out : List Bool → ℝ) (s : Table),
    (wordEstimator n p out).output
      ((), populationPath ((wordEstimator n p out).policy ()) s) =
      out (readBlock n p s).1 := @wordEstimator_output
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (n : ℕ) (p : Reader) (out : List Bool → ℝ) (S : Set (List Bool)),
    (experimentLaw μ (wordEstimator n p out) q).real {z | processHistory z.2 n ∈ S} =
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | (readBlock n p ω).1 ∈ S} := @original_word_event
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (n : ℕ) (p : Reader) (out : List Bool → ℝ) (S : Set (List Bool)) {c : ℝ} {G : Set (ℕ → ℕ → Bool)} (hG : G ⊆ {ω | (readBlock n p ω).1 ∈ S}) (h : c ≤ (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real G),
    c ≤ (experimentLaw μ (wordEstimator n p out) q).real {z | processHistory z.2 n ∈ S} := @observable_of_array
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianUpper J m b' M' (fun j i => ω (Nat.pair j i))) ∧
      medianUpper J m (fun _ => b) (fun _ => M) (fun j i => ω (Nat.pair j i)) ≤
      min 1 (128 * max (max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} := @original_median_certificate_array
example : ∀ (J m b M : ℕ),
    PathwiseCap (tailEstimator J m b M) (m * b) := @tailEstimator_cap
example : ∀ (J m b M : ℕ) (s : Table),
    (tailEstimator J m b M).output
      ((), populationPath ((tailEstimator J m b M).policy ()) s) =
      medianUpper J m (fun _ => b) (fun _ => M) (fun j i => s (Nat.pair j i)) := @tailEstimator_output
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m),
    1 - δ ≤
      (experimentLaw μ (tailEstimator J m b M) q).real
      {z | (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianWordUpper J m b M ((processHistory z.2 (m * b)).take t)) ∧
      (tailEstimator J m b M).output (z.1.1, z.2) ≤
      min 1 (128 * max (max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} := @observable_median_certificate
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m),
    1 - δ ≤
      (experimentLaw μ (tailEstimator J m (4 ^ J) (4 ^ J)) q).real
      {z | (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianWordUpper J m (4 ^ J) (4 ^ J) ((processHistory z.2 (m * 4 ^ J)).take t)) ∧
      (tailEstimator J m (4 ^ J) (4 ^ J)).output (z.1.1, z.2) ≤
      min 1 (128 * max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J))} := @observable_tail_certificate
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m) (hon : TailOnset μ ρ J),
    1 - δ ≤
      (experimentLaw μ (tailEstimator J m (4 ^ J) (4 ^ J)) q).real
      {z | (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianWordUpper J m (4 ^ J) (4 ^ J) ((processHistory z.2 (m * 4 ^ J)).take t)) ∧
      ENNReal.ofReal ((tailEstimator J m (4 ^ J) (4 ^ J)).output (z.1.1, z.2)) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)} := @observable_tail_oracle
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4),
    ∃ J₀ : ℕ, ∀ (J m : ℕ) (δ : ℝ), J₀ ≤ J → 0 < m → 0 < δ → 8 * log (2 / δ) ≤ m →
      1 - δ ≤
      (experimentLaw μ (tailEstimator J m (4 ^ J) (4 ^ J)) q).real
      {z | (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianWordUpper J m (4 ^ J) (4 ^ J)
      ((processHistory z.2 (m * 4 ^ J)).take t)) ∧
      ENNReal.ofReal ((tailEstimator J m (4 ^ J) (4 ^ J)).output (z.1.1, z.2)) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)} := @observable_tail_oracle_eventually
example : ∀ (m b M : ℕ → ℕ) (L J₀ : ℕ),
    PathwiseCap (depthsEstimator m b M L J₀) (depthsCost m b (L + 1)) := @depthsEstimator_cap
example : ∀ (m b M : ℕ → ℕ) (L J₀ J₁ : ℕ),
    (depthsEstimator m b M L J₀).policy = (depthsEstimator m b M L J₁).policy := @depthsEstimator_policy
example : ∀ (m b M : ℕ → ℕ) (L : ℕ) {J₀ : ℕ} (hJ : J₀ ≤ L) (s : Table),
    (depthsEstimator m b M L J₀).output
      ((), populationPath ((depthsEstimator m b M L J₀).policy ()) s) =
      medianUpper J₀ (m J₀) (fun _ => b J₀) (fun _ => M J₀)
      (fun j i => s (Nat.pair J₀ (Nat.pair j i))) := @depthsEstimator_output
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (m b M : ℕ → ℕ) (L J₀ : ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J) (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J) (hb : ∀ J : ℕ, 1 ≤ J → 0 < b J) (hM : ∀ J : ℕ, 1 ≤ J → 0 < M J),
    1 - δ ≤
      (experimentLaw μ (depthsEstimator m b M L J₀) q).real
      {z | ∀ J, 1 ≤ J → J ≤ L →
      (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      depthWordUpper m b M J ((processHistory z.2 (depthsCost m b (L + 1))).take t)) ∧
      (depthsEstimator m b M L J).output (z.1.1, z.2) ≤
      min 1 (128 * max (max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J))} := @observable_median_depths
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (m : ℕ → ℕ) (L J₀ : ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J) (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J),
    1 - δ ≤
      (experimentLaw μ (depthsEstimator m (fun J => 4 ^ J) (fun J => 4 ^ J) L J₀) q).real
      {z | ∀ J, 1 ≤ J → J ≤ L →
      (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      depthWordUpper m (fun J => 4 ^ J) (fun J => 4 ^ J) J
      ((processHistory z.2 (depthsCost m (fun J => 4 ^ J) (L + 1))).take t)) ∧
      (TailOnset μ ρ J →
      ENNReal.ofReal ((depthsEstimator m (fun J => 4 ^ J) (fun J => 4 ^ J) L J).output
      (z.1.1, z.2)) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J))} := @observable_tail_oracle_depths
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4),
    ∃ J₀ : ℕ, ∀ (m : ℕ → ℕ) (L J₁ : ℕ) (δ : ℝ), 0 < δ → (∀ J : ℕ, 1 ≤ J → 0 < m J) →
      (∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J) →
      1 - δ ≤
      (experimentLaw μ (depthsEstimator m (fun J => 4 ^ J) (fun J => 4 ^ J) L J₁) q).real
      {z | ∀ J, 1 ≤ J → J ≤ L →
      (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      depthWordUpper m (fun J => 4 ^ J) (fun J => 4 ^ J) J
      ((processHistory z.2 (depthsCost m (fun J => 4 ^ J) (L + 1))).take t)) ∧
      (J₀ ≤ J →
      ENNReal.ofReal ((depthsEstimator m (fun J => 4 ^ J) (fun J => 4 ^ J) L J).output
      (z.1.1, z.2)) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J))} := @observable_tail_oracle_depths_eventually
"""
    if source.count("example ") != len(NAMES):
        raise ValueError("Each tail-observable declaration needs exactly one restated statement")
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
