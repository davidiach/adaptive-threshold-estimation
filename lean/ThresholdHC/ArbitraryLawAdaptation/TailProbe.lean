import ThresholdHC.ArbitraryLawAdaptation.TailTest

/-! The capped tail probe: inverse sampling over fresh coins.

Fresh persistent coins are tested one after another with the sign-neutral tail
test. The probe stops when it completes an unresolved coin, when it has
completed `M` coins, or when its physical flip budget `b` is exhausted. A coin
that the budget interrupts is charged and is not counted as completed. After
`n` completed coins the probe returns `V = min{1, 8/n}`, with `V = 1` at
`n = 0`.

This module defines the probe on a stream of tapes, one tape for each fresh
coin, and proves its pathwise properties: the caps, the accounting of an
interrupted coin, monotonicity in the budget, and dependence on the bought
flips only. No probability enters here. -/

noncomputable section
namespace ThresholdHC.ArbitraryLawAdaptation

/-- Flips needed to complete the first `n` coins of a stream. -/
def probeWork (J : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, tailWork J (ω i)

/-- With an unlimited budget the probe completes at least `n` coins: `n` is
within the coin cap `M`, and every coin before the last of the `n` is resolved. -/
def probeAdmits (J M : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ) : Prop :=
  n ≤ M ∧ ∀ i, i + 1 < n → ¬ tailUnresolved J (ω i)

/-- Coins the probe completes with an unlimited budget: it stops on its first
unresolved coin or at the coin cap. -/
def probeHorizon (J M : ℕ) (ω : ℕ → ℕ → Bool) : ℕ := sSup {n | probeAdmits J M ω n}

/-- The probe completes at least `n` coins within the flip budget `b`. -/
def probeReaches (J b M : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ) : Prop :=
  probeAdmits J M ω n ∧ probeWork J ω n ≤ b

/-- Coins completed within the flip budget `b` and the coin cap `M`. -/
def probeCompleted (J b M : ℕ) (ω : ℕ → ℕ → Bool) : ℕ := sSup {n | probeReaches J b M ω n}

/-- Flips charged at budget `b`: every flip of every completed coin, and the
flips bought on a coin that the budget interrupts. -/
def probeFlips (J b M : ℕ) (ω : ℕ → ℕ → Bool) : ℕ :=
  min b (probeWork J ω (probeHorizon J M ω))

/-- The probe ended on an unresolved coin. -/
def probeUnresolved (J b M : ℕ) (ω : ℕ → ℕ → Bool) : Prop :=
  0 < probeCompleted J b M ω ∧ tailUnresolved J (ω (probeCompleted J b M ω - 1))

/-- The certificate `V = min{1, 8/n}` after `n` completed coins, and `V = 1`
when no coin is completed. -/
def probeUpper (n : ℕ) : ℝ := if n = 0 then 1 else min 1 (8 / n)

theorem probeWork_zero (J : ℕ) (ω : ℕ → ℕ → Bool) : probeWork J ω 0 = 0 := by
  simp [probeWork]

theorem probeWork_succ (J : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ) :
    probeWork J ω (n + 1) = probeWork J ω n + tailWork J (ω n) := by
  unfold probeWork
  rw [Finset.sum_range_succ]

theorem probeWork_mono (J : ℕ) (ω : ℕ → ℕ → Bool) {n n' : ℕ} (h : n ≤ n') :
    probeWork J ω n ≤ probeWork J ω n' := by
  unfold probeWork
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- Each coin costs at least one flip. -/
theorem le_probeWork (J : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ) : n ≤ probeWork J ω n := by
  unfold probeWork
  calc n = ∑ _i ∈ Finset.range n, 1 := by simp
    _ ≤ ∑ i ∈ Finset.range n, tailWork J (ω i) :=
        Finset.sum_le_sum fun i _ => tailWork_pos J (ω i)

/-- Each coin costs at most `N = 4^J` flips. -/
theorem probeWork_le (J : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ) : probeWork J ω n ≤ n * 4 ^ J := by
  unfold probeWork
  calc ∑ i ∈ Finset.range n, tailWork J (ω i) ≤ ∑ _i ∈ Finset.range n, 4 ^ J :=
        Finset.sum_le_sum fun i _ => tailWork_le J (ω i)
    _ = n * 4 ^ J := by simp

theorem probeWork_strictMono (J : ℕ) (ω : ℕ → ℕ → Bool) {n n' : ℕ} (h : n < n') :
    probeWork J ω n < probeWork J ω n' := by
  have h1 : probeWork J ω (n + 1) ≤ probeWork J ω n' := probeWork_mono J ω h
  have h2 := probeWork_succ J ω n
  have h3 := tailWork_pos J (ω n)
  omega

/-- The work of the first `n` coins reads only the bought flips of those coins. -/
theorem probeWork_congr {J n : ℕ} {ω ω' : ℕ → ℕ → Bool}
    (h : ∀ i < n, ∀ k < tailWork J (ω i), ω i k = ω' i k) :
    probeWork J ω' n = probeWork J ω n := by
  unfold probeWork
  exact Finset.sum_congr rfl fun i hi => tailWork_congr (h i (Finset.mem_range.mp hi))

theorem probeAdmits_zero (J M : ℕ) (ω : ℕ → ℕ → Bool) : probeAdmits J M ω 0 :=
  ⟨Nat.zero_le M, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem probeAdmits_of_le {J M : ℕ} {ω : ℕ → ℕ → Bool} {n n' : ℕ} (h : probeAdmits J M ω n)
    (hn : n' ≤ n) : probeAdmits J M ω n' :=
  ⟨hn.trans h.1, fun i hi => h.2 i (hi.trans_le hn)⟩

theorem probeReaches_zero (J b M : ℕ) (ω : ℕ → ℕ → Bool) : probeReaches J b M ω 0 :=
  ⟨probeAdmits_zero J M ω, by simp [probeWork_zero]⟩

theorem probeReaches_of_le {J b M : ℕ} {ω : ℕ → ℕ → Bool} {n n' : ℕ}
    (h : probeReaches J b M ω n) (hn : n' ≤ n) : probeReaches J b M ω n' :=
  ⟨probeAdmits_of_le h.1 hn, (probeWork_mono J ω hn).trans h.2⟩

theorem bddAbove_probeAdmits (J M : ℕ) (ω : ℕ → ℕ → Bool) :
    BddAbove {n | probeAdmits J M ω n} := ⟨M, fun _ h => h.1⟩

theorem bddAbove_probeReaches (J b M : ℕ) (ω : ℕ → ℕ → Bool) :
    BddAbove {n | probeReaches J b M ω n} := ⟨M, fun _ h => h.1.1⟩

/-- The probe would complete at least `n` coins exactly when `n` is admitted. -/
theorem le_probeHorizon_iff (J M : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ) :
    n ≤ probeHorizon J M ω ↔ probeAdmits J M ω n :=
  ⟨fun h => probeAdmits_of_le
      (Nat.sSup_mem ⟨0, probeAdmits_zero J M ω⟩ (bddAbove_probeAdmits J M ω)) h,
    fun h => le_csSup (bddAbove_probeAdmits J M ω) h⟩

/-- The probe completes at least `n` coins exactly when it reaches `n`. -/
theorem le_probeCompleted_iff (J b M : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ) :
    n ≤ probeCompleted J b M ω ↔ probeReaches J b M ω n :=
  ⟨fun h => probeReaches_of_le
      (Nat.sSup_mem ⟨0, probeReaches_zero J b M ω⟩ (bddAbove_probeReaches J b M ω)) h,
    fun h => le_csSup (bddAbove_probeReaches J b M ω) h⟩

theorem probeHorizon_admits (J M : ℕ) (ω : ℕ → ℕ → Bool) :
    probeAdmits J M ω (probeHorizon J M ω) := (le_probeHorizon_iff J M ω _).1 le_rfl

theorem probeCompleted_reaches (J b M : ℕ) (ω : ℕ → ℕ → Bool) :
    probeReaches J b M ω (probeCompleted J b M ω) := (le_probeCompleted_iff J b M ω _).1 le_rfl

theorem probeHorizon_le (J M : ℕ) (ω : ℕ → ℕ → Bool) : probeHorizon J M ω ≤ M :=
  (probeHorizon_admits J M ω).1

/-- Below the coin cap the unlimited probe ends on an unresolved coin. -/
theorem probeHorizon_unresolved {J M : ℕ} {ω : ℕ → ℕ → Bool} (h : probeHorizon J M ω < M) :
    0 < probeHorizon J M ω ∧ tailUnresolved J (ω (probeHorizon J M ω - 1)) := by
  have hnot : ¬ probeAdmits J M ω (probeHorizon J M ω + 1) := fun ha =>
    absurd ((le_probeHorizon_iff J M ω _).2 ha) (Nat.not_succ_le_self _)
  have hex : ∃ i, i + 1 < probeHorizon J M ω + 1 ∧ tailUnresolved J (ω i) := by
    by_contra hc
    push Not at hc
    exact hnot ⟨h, hc⟩
  obtain ⟨i, hi, hu⟩ := hex
  have hge : probeHorizon J M ω ≤ i + 1 := by
    by_contra hlt
    exact (probeHorizon_admits J M ω).2 i (not_le.mp hlt) hu
  have heq : probeHorizon J M ω - 1 = i := by omega
  exact ⟨by omega, heq ▸ hu⟩

theorem probeCompleted_le_horizon (J b M : ℕ) (ω : ℕ → ℕ → Bool) :
    probeCompleted J b M ω ≤ probeHorizon J M ω :=
  (le_probeHorizon_iff J M ω _).2 (probeCompleted_reaches J b M ω).1

/-- At most `M` coins are completed. -/
theorem probeCompleted_le_cap (J b M : ℕ) (ω : ℕ → ℕ → Bool) : probeCompleted J b M ω ≤ M :=
  (probeCompleted_reaches J b M ω).1.1

/-- The completed coins fit the flip budget. -/
theorem probeWork_completed_le (J b M : ℕ) (ω : ℕ → ℕ → Bool) :
    probeWork J ω (probeCompleted J b M ω) ≤ b := (probeCompleted_reaches J b M ω).2

/-- At most `b` coins are completed with `b` flips. -/
theorem probeCompleted_le_budget (J b M : ℕ) (ω : ℕ → ℕ → Bool) : probeCompleted J b M ω ≤ b :=
  (le_probeWork J ω _).trans (probeWork_completed_le J b M ω)

/-- Raising the flip budget or the coin cap never loses a completed coin. -/
theorem probeCompleted_mono (J : ℕ) (ω : ℕ → ℕ → Bool) {b b' M M' : ℕ} (hb : b ≤ b')
    (hM : M ≤ M') : probeCompleted J b M ω ≤ probeCompleted J b' M' ω := by
  have h := probeCompleted_reaches J b M ω
  exact (le_probeCompleted_iff J b' M' ω _).2 ⟨⟨h.1.1.trans hM, h.1.2⟩, h.2.trans hb⟩

/-- A coin cap of at least the flip budget is inactive. -/
theorem probeCompleted_cap_inactive (J : ℕ) (ω : ℕ → ℕ → Bool) {b M : ℕ} (h : b ≤ M) :
    probeCompleted J b M ω = probeCompleted J b b ω := by
  apply le_antisymm
  · have hr := probeCompleted_reaches J b M ω
    exact (le_probeCompleted_iff J b b ω _).2
      ⟨⟨probeCompleted_le_budget J b M ω, hr.1.2⟩, hr.2⟩
  · exact probeCompleted_mono J ω le_rfl h

/-- The flip budget is a pathwise cap. -/
theorem probeFlips_le (J b M : ℕ) (ω : ℕ → ℕ → Bool) : probeFlips J b M ω ≤ b :=
  min_le_left _ _

/-- The coin cap bounds the flips by `M · 4^J` on every path. -/
theorem probeFlips_le_cap (J b M : ℕ) (ω : ℕ → ℕ → Bool) : probeFlips J b M ω ≤ M * 4 ^ J :=
  (min_le_right _ _).trans ((probeWork_le J ω _).trans
    (Nat.mul_le_mul_right _ (probeHorizon_le J M ω)))

/-- Every flip of every completed coin is charged. -/
theorem probeWork_completed_le_flips (J b M : ℕ) (ω : ℕ → ℕ → Bool) :
    probeWork J ω (probeCompleted J b M ω) ≤ probeFlips J b M ω :=
  le_min (probeWork_completed_le J b M ω)
    (probeWork_mono J ω (probeCompleted_le_horizon J b M ω))

/-- A probe that has stopped is charged exactly its completed coins. -/
theorem probeFlips_of_stopped {J b M : ℕ} {ω : ℕ → ℕ → Bool}
    (h : probeCompleted J b M ω = probeHorizon J M ω) :
    probeFlips J b M ω = probeWork J ω (probeCompleted J b M ω) := by
  unfold probeFlips
  rw [← h]
  exact min_eq_right (probeWork_completed_le J b M ω)

/-- A probe that the budget interrupts is charged the whole budget, and its
next coin is paid for in part and is not counted as completed. -/
theorem probeFlips_of_running {J b M : ℕ} {ω : ℕ → ℕ → Bool}
    (h : probeCompleted J b M ω < probeHorizon J M ω) :
    probeFlips J b M ω = b ∧ b < probeWork J ω (probeCompleted J b M ω + 1) := by
  have hlt : b < probeWork J ω (probeCompleted J b M ω + 1) := by
    by_contra hc
    have hr : probeReaches J b M ω (probeCompleted J b M ω + 1) :=
      ⟨(le_probeHorizon_iff J M ω _).1 h, not_lt.mp hc⟩
    exact absurd ((le_probeCompleted_iff J b M ω _).2 hr) (Nat.not_succ_le_self _)
  refine ⟨?_, hlt⟩
  unfold probeFlips
  exact min_eq_left (hlt.le.trans (probeWork_mono J ω h))

/-- The charge never decreases when the budget grows. -/
theorem probeFlips_mono (J M : ℕ) (ω : ℕ → ℕ → Bool) {b b' : ℕ} (h : b ≤ b') :
    probeFlips J b M ω ≤ probeFlips J b' M ω :=
  min_le_min_right _ h

/-- The probe reads only the flips it bought. Flip `k` of coin `i` is bought
when it lies within the coin's own test and its position in the stream of
bought flips is below the charge. Two streams that agree on the bought flips
have the same completed count, the same charge and the same final verdict. -/
theorem probe_congr {J b M : ℕ} {ω ω' : ℕ → ℕ → Bool}
    (h : ∀ i k, k < tailWork J (ω i) → probeWork J ω i + k < probeFlips J b M ω →
      ω i k = ω' i k) :
    probeCompleted J b M ω' = probeCompleted J b M ω ∧
      probeFlips J b M ω' = probeFlips J b M ω ∧
      (probeUnresolved J b M ω' ↔ probeUnresolved J b M ω) := by
  set n := probeCompleted J b M ω with hn
  have hreach : probeReaches J b M ω n := probeCompleted_reaches J b M ω
  have hcharge : probeWork J ω n ≤ probeFlips J b M ω := probeWork_completed_le_flips J b M ω
  -- Completed coins are bought in full.
  have hfull : ∀ i < n, ∀ k < tailWork J (ω i), ω i k = ω' i k := by
    intro i hi k hk
    refine h i k hk ?_
    have h1 : probeWork J ω (i + 1) ≤ probeWork J ω n := probeWork_mono J ω hi
    have h2 := probeWork_succ J ω i
    omega
  have hwork : ∀ j ≤ n, probeWork J ω' j = probeWork J ω j := fun j hj =>
    probeWork_congr fun i hi => hfull i (hi.trans_le hj)
  have hres : ∀ i < n, (tailUnresolved J (ω' i) ↔ tailUnresolved J (ω i)) := fun i hi =>
    tailUnresolved_congr (hfull i hi)
  -- The interrupted coin cannot be completed on the other stream either.
  have hpartial : n < probeHorizon J M ω → b < probeWork J ω' (n + 1) := by
    intro hrun
    obtain ⟨hfl, hlt⟩ : probeFlips J b M ω = b ∧ b < probeWork J ω (n + 1) :=
      probeFlips_of_running hrun
    by_contra hc
    have hle : probeWork J ω' (n + 1) ≤ b := not_lt.mp hc
    rw [probeWork_succ, hwork n le_rfl] at hle
    rw [probeWork_succ] at hlt
    have hagree : ∀ k < tailWork J (ω' n), ω' n k = ω n k := by
      intro k hk
      have hk' : k < tailWork J (ω n) := by omega
      exact (h n k hk' (by rw [hfl]; omega)).symm
    have := tailWork_congr hagree
    omega
  have hadm : ∀ m ≤ n + 1, (probeAdmits J M ω' m ↔ probeAdmits J M ω m) := by
    intro m hm
    unfold probeAdmits
    refine and_congr Iff.rfl (forall_congr' fun i => imp_congr_right fun hi => ?_)
    exact not_congr (hres i (by omega))
  have hcomp : probeCompleted J b M ω' = n := by
    apply le_antisymm
    · by_contra hc
      have hr : probeReaches J b M ω' (n + 1) :=
        (le_probeCompleted_iff J b M ω' _).1 (not_le.mp hc)
      have hrun : n < probeHorizon J M ω :=
        (le_probeHorizon_iff J M ω _).2 ((hadm _ le_rfl).1 hr.1)
      exact absurd hr.2 (not_le.mpr (hpartial hrun))
    · exact (le_probeCompleted_iff J b M ω' _).2
        ⟨(hadm n (Nat.le_succ n)).2 hreach.1, by rw [hwork n le_rfl]; exact hreach.2⟩
  refine ⟨hcomp, ?_, ?_⟩
  · have hle : n ≤ probeHorizon J M ω := probeCompleted_le_horizon J b M ω
    rcases hle.eq_or_lt with heq | hrun
    · -- Stopped: both streams have the same horizon.
      have hhor : probeHorizon J M ω' = n := by
        apply le_antisymm
        · by_contra hc
          have hadm' : probeAdmits J M ω' (n + 1) :=
            (le_probeHorizon_iff J M ω' _).1 (not_le.mp hc)
          have := (le_probeHorizon_iff J M ω _).2 ((hadm _ le_rfl).1 hadm')
          omega
        · exact (le_probeHorizon_iff J M ω' _).2 ((hadm n (Nat.le_succ n)).2 hreach.1)
      unfold probeFlips
      rw [hhor, ← heq, hwork n le_rfl]
    · obtain ⟨hfl, -⟩ : probeFlips J b M ω = b ∧ b < probeWork J ω (n + 1) :=
        probeFlips_of_running hrun
      have hhor : n + 1 ≤ probeHorizon J M ω' :=
        (le_probeHorizon_iff J M ω' _).2
          ((hadm _ le_rfl).2 ((le_probeHorizon_iff J M ω _).1 hrun))
      rw [hfl]
      unfold probeFlips
      exact min_eq_left ((hpartial hrun).le.trans (probeWork_mono J ω' hhor))
  · unfold probeUnresolved
    rw [hcomp, ← hn]
    refine and_congr_right fun hpos => ?_
    exact hres (n - 1) (by omega)

theorem probeUpper_zero : probeUpper 0 = 1 := by simp [probeUpper]

theorem probeUpper_pos (n : ℕ) : 0 < probeUpper n := by
  unfold probeUpper
  split_ifs with h
  · exact one_pos
  · have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
    exact lt_min one_pos (by positivity)

/-- The certificate lies in `[0,1]`. -/
theorem probeUpper_le_one (n : ℕ) : probeUpper n ≤ 1 := by
  unfold probeUpper
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem probeUpper_le_div {n : ℕ} (h : 0 < n) : probeUpper n ≤ 8 / n := by
  unfold probeUpper
  rw [ite_eq_right (Nat.pos_iff_ne_zero.mp h)]
  exact min_le_right _ _

/-- More completed coins give a smaller certificate. -/
theorem probeUpper_antitone {n n' : ℕ} (h : n ≤ n') : probeUpper n' ≤ probeUpper n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, probeUpper_zero]
    exact probeUpper_le_one n'
  · have hpos' : 0 < n' := hpos.trans_le h
    unfold probeUpper
    rw [ite_eq_right (Nat.pos_iff_ne_zero.mp hpos), ite_eq_right (Nat.pos_iff_ne_zero.mp hpos')]
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hpos
    have hle : (n : ℝ) ≤ n' := Nat.cast_le.mpr h
    exact min_le_min_left _ (div_le_div_of_nonneg_left (by norm_num) hn hle)

end ThresholdHC.ArbitraryLawAdaptation
