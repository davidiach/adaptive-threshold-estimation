import ThresholdHC.Tier3.Stopping
import ThresholdHC.Tier4.Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace ThresholdHC.Tier4
open ThresholdHC.Tier3

/-- Extend a finite observation by the stopped symbol. -/
def padPrefix (n : ℕ) (w : Prefix n) : ProcessTape :=
  fun k => if h : k < n then w ⟨k, h⟩ else none

def padJoint {Seed : Type} (n : ℕ) (z : Seed × Prefix n) : Seed × ProcessTape :=
  (z.1, padPrefix n z.2)

def stoppedPrefixSet {Seed : Type} {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (n : ℕ) : Set (Seed × Prefix n) :=
  {z | acceptedBy pol (fun _ _ => true) n z.1 z.2}

def stoppedFullSet {Seed : Type} {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (n : ℕ) : Set (Seed × ProcessTape) :=
  {z | ∃ k ≤ n, pol z.1 (processHistory z.2 k) = none}

theorem measurable_padPrefix (n : ℕ) : Measurable (padPrefix n) :=
  measurable_of_countable _

theorem measurable_padJoint {Seed : Type} [MeasurableSpace Seed] (n : ℕ) :
    Measurable (@padJoint Seed n) :=
  measurable_fst.prodMk ((measurable_padPrefix n).comp measurable_snd)

theorem stoppedFullSet_prefix {Seed : Type} {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (n : ℕ) (z : Seed × ProcessTape) :
    z ∈ stoppedFullSet pol n ↔ (z.1, processPrefix n z.2) ∈ stoppedPrefixSet pol n := by
  simp only [stoppedFullSet, stoppedPrefixSet, Set.mem_ofPred_eq,
    acceptedBy_processPrefix_iff, and_true]

theorem stoppedFullSet_mono {Seed : Type} {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) : Monotone (stoppedFullSet pol) := by
  intro n N h z hz
  obtain ⟨k, hk, hstop⟩ := hz
  exact ⟨k, hk.trans h, hstop⟩

theorem measurableSet_stoppedPrefix {Seed : Type} [MeasurableSpace Seed] {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (hp : MeasurablePolicy pol) (n : ℕ) :
    MeasurableSet (stoppedPrefixSet pol n) := by
  classical
  have hm : Measurable (fun z : Seed × Prefix n =>
      if acceptedBy pol (fun _ _ => true) n z.1 z.2 then (true : Bool) else false) := by
    apply measurable_from_prod_countable_left
    intro w
    exact measurable_const.ite
      (measurableSet_acceptedBy pol (fun _ _ => true) hp (fun _ => measurable_const) n w)
      measurable_const
  simpa [stoppedPrefixSet] using measurableSet_eq_fun hm
    (measurable_const : Measurable (fun _ : Seed × Prefix n => true))

theorem measurable_jointPrefix {Seed : Type} [MeasurableSpace Seed] (n : ℕ) :
    Measurable (fun z : Seed × ProcessTape => (z.1, processPrefix n z.2)) := by
  apply measurable_fst.prodMk
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply i.val).comp measurable_snd

theorem measurableSet_stoppedFull {Seed : Type} [MeasurableSpace Seed] {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (hp : MeasurablePolicy pol) (n : ℕ) :
    MeasurableSet (stoppedFullSet pol n) := by
  have heq : stoppedFullSet pol n =
      (fun z : Seed × ProcessTape => (z.1, processPrefix n z.2)) ⁻¹' stoppedPrefixSet pol n := by
    ext z
    exact stoppedFullSet_prefix pol n z
  rw [heq]
  exact (measurableSet_stoppedPrefix pol hp n).preimage (measurable_jointPrefix n)

theorem processHistory_succ_of_none (x : ProcessTape) (n : ℕ) (hn : x n = none) :
    processHistory x (n+1) = processHistory x n := by
  unfold processHistory
  rw [List.ofFn_succ']
  simp [processPrefix, List.concat_eq_append, hn]
  rfl

theorem stopped_valid_tail {m : ℕ} (pol : List Bool → Option (Fin m))
    (x : ProcessTape)
    (hv : ∀ k, (x k).isSome = (pol (processHistory x k)).isSome)
    (n : ℕ) (hn : pol (processHistory x n) = none) :
    ∀ k, n ≤ k → x k = none := by
  have hs : ∀ j, pol (processHistory x (n+j)) = none := by
    intro j
    induction j with
    | zero => simpa using hn
    | succ j ih =>
      have hx : x (n+j) = none := by
        have h := hv (n+j)
        rw [ih] at h
        cases hx : x (n+j) <;> simp_all
      rw [Nat.add_succ, processHistory_succ_of_none x (n+j) hx]
      exact ih
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h := hv (n+j)
  rw [hs j] at h
  cases hx : x (n+j) <;> simp_all

theorem padPrefix_eq_of_tail_none (x : ProcessTape) (n : ℕ)
    (htail : ∀ k, n ≤ k → x k = none) : padPrefix n (processPrefix n x) = x := by
  funext k
  simp only [padPrefix]
  split_ifs with h
  · rfl
  · exact (htail k (Nat.le_of_not_gt h)).symm

theorem stopped_valid_reconstruction {Seed : Type} {m : ℕ}
    (pol : Seed → List Bool → Option (Fin m)) (z : Seed × ProcessTape)
    (hv : ∀ k, (z.2 k).isSome = (pol z.1 (processHistory z.2 k)).isSome)
    (n : ℕ) (hz : z ∈ stoppedFullSet pol n) :
    padJoint n (z.1, processPrefix n z.2) = z := by
  obtain ⟨k, hk, hstop⟩ := hz
  have ht := stopped_valid_tail (pol z.1) z.2 hv k hstop
  have heq := padPrefix_eq_of_tail_none z.2 n (fun j hj => ht j (hk.trans hj))
  exact Prod.ext rfl heq

theorem measurable_processTape {Ω : Type} [MeasurableSpace Ω] (tape : Ω → ProcessTape)
    (htape : ∀ n b, MeasurableSet {ω | tape ω n = b}) : Measurable tape := by
  apply Measurable.of_eval
  intro n
  exact measurable_to_countable' (htape n)

theorem infiniteTranscriptLaw_map_prefix {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω] (ν : Measure Ω)
    (seed : Ω → Seed) (tape : Ω → ProcessTape) (hs : Measurable seed)
    (htape : ∀ n b, MeasurableSet {ω | tape ω n = b}) (n : ℕ) :
    (infiniteTranscriptLaw ν seed tape).map
      (fun z => (z.1, processPrefix n z.2)) = prefixTranscriptLaw ν seed tape n := by
  rw [infiniteTranscriptLaw, Measure.map_map (measurable_jointPrefix n)
    (hs.prodMk (measurable_processTape tape htape))]
  rfl

theorem measurableSet_reconstructed {Seed : Type} [MeasurableSpace Seed] (n : ℕ) :
    MeasurableSet {z : Seed × ProcessTape |
      padJoint n (z.1, processPrefix n z.2) = z} := by
  have heq : {z : Seed × ProcessTape | padJoint n (z.1, processPrefix n z.2) = z} =
      {z | ∀ k, padPrefix n (processPrefix n z.2) k = z.2 k} := by
    ext z
    rcases z with ⟨u, x⟩
    simp only [Set.mem_ofPred_eq, padJoint, Prod.mk.injEq, true_and]
    exact funext_iff
  rw [heq]
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_eq_fun
    (((measurable_pi_apply k).comp (measurable_padPrefix n)).comp
      ((measurable_jointPrefix n).snd))
    ((measurable_pi_apply k).comp measurable_snd)

theorem realized_stopped_reconstruction {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) [IsProbabilityMeasure ν] {m : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (hs : Measurable seed) (htape : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurablePolicy pol) (hr : RealizesPrefixes μ ν seed tape pol d q)
    (n : ℕ) :
    ∀ᵐ z ∂infiniteTranscriptLaw ν seed tape,
      z ∈ stoppedFullSet pol n → padJoint n (z.1, processPrefix n z.2) = z := by
  apply (ae_map_iff (hs.prodMk (measurable_processTape tape htape)).aemeasurable ?_).mpr
  · have hv : ∀ᵐ ω ∂ν, ∀ k, (tape ω k).isSome =
        (pol (seed ω) (processHistory (tape ω) k)).isSome :=
      ae_all_iff.2 (fun k => realized_valid_step μ ν seed tape pol d q hs htape hp hr k)
    filter_upwards [hv] with ω hvalid hz
    exact stopped_valid_reconstruction pol (seed ω, tape ω) hvalid n hz
  · exact (measurableSet_stoppedFull pol hp n).imp
      (measurableSet_reconstructed n)

theorem realized_stopped_cover {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) [IsProbabilityMeasure ν] {m : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (hs : Measurable seed) (htape : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurablePolicy pol) (hr : RealizesPrefixes μ ν seed tape pol d q)
    (hstop : ∀ᵐ ω ∂ν, ∃ n, pol (seed ω) (processHistory (tape ω) n) = none) :
    ∀ᵐ z ∂infiniteTranscriptLaw ν seed tape, ∃ n, z ∈ stoppedFullSet pol n := by
  apply (ae_map_iff (hs.prodMk (measurable_processTape tape htape)).aemeasurable ?_).mpr
  · filter_upwards [hstop] with ω hω
    obtain ⟨n, hn⟩ := hω
    exact ⟨n, n, le_rfl, hn⟩
  · convert MeasurableSet.iUnion (fun n => measurableSet_stoppedFull pol hp n) using 1
    ext z
    simp

theorem realized_eventual_reconstruction {Seed Ω : Type}
    [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) [IsProbabilityMeasure ν] {m : ℕ}
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (hs : Measurable seed) (htape : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : MeasurablePolicy pol) (hr : RealizesPrefixes μ ν seed tape pol d q)
    (hstop : ∀ᵐ ω ∂ν, ∃ n, pol (seed ω) (processHistory (tape ω) n) = none) :
    ∀ᵐ z ∂infiniteTranscriptLaw ν seed tape,
      ∀ᶠ n in atTop, padJoint n (z.1, processPrefix n z.2) = z := by
  have hcover := realized_stopped_cover μ ν seed tape pol d q hs htape hp hr hstop
  have hrec := ae_all_iff.2 (fun n =>
    realized_stopped_reconstruction μ ν seed tape pol d q hs htape hp hr n)
  filter_upwards [hcover, hrec] with z hz hvalid
  obtain ⟨N, hN⟩ := hz
  exact eventually_atTop.mpr ⟨N, fun n hn => hvalid n (stoppedFullSet_mono pol hn hN)⟩

end ThresholdHC.Tier4
