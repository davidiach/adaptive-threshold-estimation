import ThresholdHC.EarlyPilot.VarReader

/-! The stopping rule of one tail probe, read off its observed word.

The probe's reader keeps a flag that is set once the probe will not count
another coin: it has completed an unresolved coin or `M` coins. After `u`
flips of a table the flag is set exactly when the work of the coins up to the
probe's stop with an unlimited budget is at most `u`. A copy with flip budget
`b` stops when the flag is set or when it has `b` flips, which happens exactly
when `u` reaches the tape-level charge `probeFlips = min(b, work up to the
stop)`. Stopped there, it has completed the same coins as at the full budget.
No probability enters here. -/

noncomputable section
namespace ThresholdHC.EarlyPilot
open ThresholdHC.HardBudget ThresholdHC.ArbitraryLawAdaptation

/-- The probe's rule: stop when the reader's flag is set or `b` flips are bought. -/
def probeFin (J b M : ℕ) (w : List Bool) : Bool :=
  (probeRun J M w).stopped || decide (b ≤ w.length)

/-- After `u` flips the reader's flag is set exactly when the coins up to the
probe's stop cost at most `u` flips. -/
theorem probeStopped_iff (J M : ℕ) (ω : Table) (u : ℕ) :
    (probeRun J M (readBlock u (probeReader J M) ω).1).stopped = true ↔
      probeWork J ω (probeHorizon J M ω) ≤ u := by
  have hinv := probeInv_readBlock J M ω u
  have hsch := probeReader_schedule J M ω u
  change probeWork J ω (probeRun J M (readBlock u (probeReader J M) ω).1).coin ≤ u ∧
      u < probeWork J ω ((probeRun J M (readBlock u (probeReader J M) ω).1).coin + 1) at hsch
  rw [hinv.stopped, ← le_probeHorizon_iff, not_le]
  constructor
  · intro h
    exact (probeWork_mono J ω (Nat.lt_succ_iff.mp h)).trans hsch.1
  · intro h
    by_contra hc
    have := probeWork_mono J ω (not_lt.mp hc)
    omega

/-- The copy with flip budget `b` has stopped after `u` flips exactly when `u`
reaches its charge. -/
theorem probeFin_iff (J b M : ℕ) (ω : Table) (u : ℕ) :
    probeFin J b M (readBlock u (probeReader J M) ω).1 = true ↔ probeFlips J b M ω ≤ u := by
  unfold probeFin probeFlips
  rw [Bool.or_eq_true, probeStopped_iff, decide_eq_true_iff, readBlock_length, min_le_iff]
  exact Or.comm

/-- The rule holds once the copy has `b` flips. -/
theorem probeFin_of_le (J b M : ℕ) {w : List Bool} (h : b ≤ w.length) : probeFin J b M w = true := by
  unfold probeFin
  rw [Bool.or_eq_true, decide_eq_true_iff]
  exact Or.inr h

/-- With a positive budget and a positive coin cap the copy buys at least one
flip. -/
theorem probeFlips_pos (J : ℕ) {b M : ℕ} (hb : 0 < b) (hM : 0 < M) (ω : Table) :
    0 < probeFlips J b M ω := by
  have h1 : 1 ≤ probeHorizon J M ω :=
    (le_probeHorizon_iff J M ω 1).2 ((probeAdmits_one J M ω).2 hM)
  have h2 : probeHorizon J M ω ≤ probeWork J ω (probeHorizon J M ω) := le_probeWork J ω _
  unfold probeFlips
  exact lt_min hb (by omega)

/-- Stopped at its charge, the copy has completed the coins it completes at
the full budget. -/
theorem probeCompleted_flips (J b M : ℕ) (ω : Table) :
    probeCompleted J (probeFlips J b M ω) M ω = probeCompleted J b M ω := by
  apply le_antisymm
  · exact probeCompleted_mono J ω (probeFlips_le J b M ω) le_rfl
  · have hr := probeCompleted_reaches J b M ω
    exact (le_probeCompleted_iff J _ M ω _).2
      ⟨hr.1, probeWork_completed_le_flips J b M ω⟩

end ThresholdHC.EarlyPilot
