import ThresholdHC.EarlyPilot.ProbeStop

/-! The early-stopping pilot as an observable estimator.

The pilot of target depth `J` runs `J m` probes one after another. Probe
`n` is probe `k = n % m` of depth `j + 1` with `j = n / m`: it reads the coins
`Nat.pair j (Nat.pair k c)` with the probe's reader of depth `j + 1` and coin
cap `M`, and it stops on its first unresolved coin, on completing `M` coins or
on exhausting its budget `b_(j+1)`. The next probe starts at once, so no flip
is bought after a probe has stopped. The certificate of depth `i + 1` is the
median of the probes' certificates computed from the words they observed.

On every table of coin tapes the pilot buys exactly the sum of the probes'
tape-level charges `probeFlips`, and its certificates are the tape-level
medians of the full pilot. On every admissible path it buys at most the full
pilot's `m sum_j b_j` flips. No probability enters here. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EarlyPilot
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget
open ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation ThresholdHC.BlindUpper

/-- The coins of probe `n`: coin `c` of probe `n % m` of depth `n / m + 1`. -/
def pilotLab (m n c : ℕ) : ℕ := Nat.pair (n / m) (Nat.pair (n % m) c)

/-- The stopping rule of probe `n`. -/
def pilotFin (J m M n : ℕ) (w : List Bool) : Bool :=
  probeFin (n / m + 1) (pilotBudget J (n / m + 1)) M w

/-- The reader of probe `n`. -/
def pilotProbe (m M n : ℕ) : Reader := probeReader (n / m + 1) M

/-- The early pilot's policy: the `J m` probes one after another. -/
def earlyPolicy (J m M : ℕ) : List Bool → Option ℕ :=
  varPolicy (J * m) (pilotFin J m M) (pilotLab m) (pilotProbe m M)

/-- The certificate of depth `i + 1` computed from an observed word: the median
of the probes' certificates, probe `k` of that depth being probe `i m + k`. -/
def earlyUpper (J m M i : ℕ) (w : List Bool) : ℝ :=
  blockMedian m (fun k => probeUpper (probeWordCompleted (i + 1) M
    (((varRun (pilotFin J m M) w).done[i * m + k]?).getD [])))

/-- The early pilot reporting the certificate of depth `i + 1`. It has no
private randomness and reads the first `m sum_j b_j` observed flips. -/
def earlyEstimator (J m : ℕ) (ρ : ℝ) (i : ℕ) : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy _ := earlyPolicy J m (pilotCoinCap J ρ)
  policy_measurable := by
    intro xs a
    exact measurableSet_eq_fun measurable_const measurable_const
  output z := earlyUpper J m (pilotCoinCap J ρ) i (processHistory z.2 (pilotCost J m))
  output_measurable :=
    (measurable_from_top (f := earlyUpper J m (pilotCoinCap J ρ) i)).comp
      ((measurable_processHistory_fixed (pilotCost J m)).comp measurable_snd)

/-- A double sum over depths and probes, as a sum over the probes in order. -/
theorem sum_range_mul_div_mod (f : ℕ → ℕ → ℕ) (J m : ℕ) :
    ∑ n ∈ Finset.range (J * m), f (n / m) (n % m) =
      ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range m, f j k := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < m := Finset.mem_range.mp hk
    have hm : 0 < m := by omega
    have hd : (J * m + k) / m = J := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hk', zero_add]
    have hr : (J * m + k) % m = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk']
    rw [hd, hr]

theorem pilotLab_inj (m : ℕ) : ∀ n c n' c', pilotLab m n c = pilotLab m n' c' → n = n' ∧ c = c' := by
  intro n c n' c' h
  unfold pilotLab at h
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h
  obtain ⟨h3, h4⟩ := Nat.pair_eq_pair.mp h2
  refine ⟨?_, h4⟩
  rw [← Nat.div_add_mod n m, ← Nat.div_add_mod n' m, h1, h3]

/-- The pilot's cap `m sum_j b_j` as a sum over the probes in order. -/
theorem pilotCost_eq_seqOffset (J m : ℕ) :
    seqOffset (fun n => pilotBudget J (n / m + 1)) (J * m) = pilotCost J m := by
  unfold seqOffset
  rw [sum_range_mul_div_mod (fun j _ => pilotBudget J (j + 1)) J m]
  unfold pilotCost seqOffset pilotLength
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- On every admissible path the early pilot buys at most `m sum_j b_j` flips. -/
theorem earlyEstimator_cap (J m : ℕ) (ρ : ℝ) (i : ℕ) :
    PathwiseCap (earlyEstimator J m ρ i) (pilotCost J m) := by
  apply pathwiseCap_of_length
  intro r xs h
  rw [← pilotCost_eq_seqOffset]
  exact varPolicy_length_lt (J * m) (pilotFin J m (pilotCoinCap J ρ)) (pilotLab m)
    (pilotProbe m (pilotCoinCap J ρ)) (fun n => pilotBudget J (n / m + 1))
    (fun n => pilotBudget_pos J _) (fun n w hw => probeFin_of_le _ _ _ hw) h

/-- Flips probe `n` buys on the table `s`: its tape-level charge. -/
def earlyLength (J m M : ℕ) (s : Table) (n : ℕ) : ℕ :=
  probeFlips (n / m + 1) (pilotBudget J (n / m + 1)) M (blockTable (pilotLab m) s n)

/-- The word the early pilot observes on the table `s`. -/
def earlyWord (J m M : ℕ) (s : Table) : List Bool :=
  (readBlock (seqOffset (earlyLength J m M s) (J * m))
    (varReader (pilotFin J m M) (pilotLab m) (pilotProbe m M)) s).1

theorem earlyFin_iff (J m M : ℕ) (s : Table) :
    ∀ n, n < J * m → ∀ u, pilotFin J m M n
      (readBlock u (pilotProbe m M n) (blockTable (pilotLab m) s n)).1 = true ↔
        earlyLength J m M s n ≤ u :=
  fun _ _ u => probeFin_iff _ _ _ _ u

theorem earlyLength_pos (J m : ℕ) {M : ℕ} (hM : 0 < M) (s : Table) :
    ∀ n, n < J * m → 0 < earlyLength J m M s n :=
  fun _ _ => probeFlips_pos _ (pilotBudget_pos J _) hM _

/-- The path of the early pilot on a table: its observed word, then stop symbols. -/
theorem earlyPolicy_path (J m : ℕ) {M : ℕ} (hM : 0 < M) (s : Table) :
    populationPath (earlyPolicy J m M) s = fun k => (earlyWord J m M s)[k]? :=
  populationPath_varPolicy (pilotFin J m M) (pilotLab_inj m) (earlyFin_iff J m M s)
    (earlyLength_pos J m hM s)

/-- The finished probes' words on a table: probe `n` observes what its reader
observes alone, stopped at its charge. -/
theorem earlyWord_done (J m : ℕ) {M : ℕ} (hM : 0 < M) (s : Table) :
    (varRun (pilotFin J m M) (earlyWord J m M s)).done =
      (List.range (J * m)).map (fun n => (readBlock (earlyLength J m M s n) (pilotProbe m M n)
        (blockTable (pilotLab m) s n)).1) :=
  (varRun_readBlock_total (pilotFin J m M) (pilotLab_inj m) (earlyFin_iff J m M s)
    (earlyLength_pos J m hM s)).2

/-- The early pilot buys the sum of the probes' tape-level charges. -/
theorem earlyWord_length (J m M : ℕ) (s : Table) :
    (earlyWord J m M s).length =
      ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range m,
        probeFlips (j + 1) (pilotBudget J (j + 1)) M (pilotStreams s j k) := by
  unfold earlyWord
  rw [readBlock_length]
  exact sum_range_mul_div_mod
    (fun j k => probeFlips (j + 1) (pilotBudget J (j + 1)) M (pilotStreams s j k)) J m

theorem earlyWord_length_le (J m M : ℕ) (s : Table) :
    (earlyWord J m M s).length ≤ pilotCost J m := by
  unfold earlyWord
  rw [readBlock_length, ← pilotCost_eq_seqOffset]
  unfold seqOffset
  exact Finset.sum_le_sum fun n _ => probeFlips_le _ _ _ _

/-- On every table, the early pilot buys exactly the sum of the probes'
tape-level charges. -/
theorem earlyEstimator_work (J m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) (s : Table) :
    totalProcessWork (populationPath ((earlyEstimator J m ρ i).policy ()) s) =
      ((∑ j ∈ Finset.range J, ∑ k ∈ Finset.range m,
        probeFlips (j + 1) (pilotBudget J (j + 1)) (pilotCoinCap J ρ) (pilotStreams s j k) : ℕ) :
          ℝ≥0∞) := by
  change totalProcessWork (populationPath (earlyPolicy J m (pilotCoinCap J ρ)) s) = _
  rw [earlyPolicy_path J m (pilotCoinCap_pos J hρ), totalProcessWork_word, earlyWord_length]

/-- On every table, the certificate of depth `i + 1 ≤ J` computed from the
early pilot's word is the tape-level median of the probes of that depth. -/
theorem earlyUpper_word (J m : ℕ) {M : ℕ} (hM : 0 < M) (s : Table) {i : ℕ} (hi : i < J) :
    earlyUpper J m M i (earlyWord J m M s) =
      medianUpper (i + 1) m (fun _ => pilotBudget J (i + 1)) (fun _ => M) (pilotStreams s i) := by
  unfold earlyUpper medianUpper
  apply blockMedian_congr
  intro k hk
  have hm : 0 < m := by omega
  have hlt : i * m + k < J * m := by
    calc i * m + k < i * m + m := by omega
      _ = (i + 1) * m := by ring
      _ ≤ J * m := Nat.mul_le_mul_right _ hi
  have hd : (i * m + k) / m = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hk, zero_add]
  have hr : (i * m + k) % m = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  rw [earlyWord_done J m hM s, List.getElem?_map, List.getElem?_range hlt]
  change probeUpper (probeWordCompleted (i + 1) M
      (readBlock (probeFlips ((i * m + k) / m + 1) (pilotBudget J ((i * m + k) / m + 1)) M
          (fun c => s (Nat.pair ((i * m + k) / m) (Nat.pair ((i * m + k) % m) c))))
        (probeReader ((i * m + k) / m + 1) M)
        (fun c => s (Nat.pair ((i * m + k) / m) (Nat.pair ((i * m + k) % m) c)))).1) =
    probeUpper (probeCompleted (i + 1) (pilotBudget J (i + 1)) M (pilotStreams s i k))
  rw [hd, hr, probeWordCompleted_readBlock]
  exact congrArg probeUpper (probeCompleted_flips _ _ _ _)

/-- On every table, the early pilot reports at index `i < J` the tape-level
median certificate of depth `i + 1` of the full pilot. -/
theorem earlyEstimator_output (J m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (s : Table) {i : ℕ} (hi : i < J) :
    (earlyEstimator J m ρ i).output ((), populationPath ((earlyEstimator J m ρ i).policy ()) s) =
      medianUpper (i + 1) m (fun _ => pilotBudget J (i + 1)) (fun _ => pilotCoinCap J ρ)
        (pilotStreams s i) := by
  change earlyUpper J m (pilotCoinCap J ρ) i
      (processHistory (populationPath (earlyPolicy J m (pilotCoinCap J ρ)) s) (pilotCost J m)) = _
  rw [earlyPolicy_path J m (pilotCoinCap_pos J hρ),
    processHistory_word_le _ (earlyWord_length_le J m _ s)]
  exact earlyUpper_word J m (pilotCoinCap_pos J hρ) s hi

/-- The early pilot meets the predicate `IsEarlyPilot`. -/
theorem earlyEstimator_isEarlyPilot (J m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    IsEarlyPilot J m ρ (earlyEstimator J m ρ) :=
  ⟨fun _ => rfl, earlyEstimator_cap J m ρ, fun s i => earlyEstimator_work J m hρ i s,
    fun s _ hi => earlyEstimator_output J m hρ s hi⟩

end ThresholdHC.EarlyPilot
