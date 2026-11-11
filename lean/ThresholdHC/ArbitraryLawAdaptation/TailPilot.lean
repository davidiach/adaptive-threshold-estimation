import ThresholdHC.ArbitraryLawAdaptation.TailBlockReader

/-! The capped multi-depth pilot: budgets, caps and its reader.

For a target depth `J ≥ 1` with `N = 4^J`, the pilot runs `m` probes at every
depth `j = 1, …, J`. Each probe of depth `j` has the flip budget

  `b_j = ⌈N / (2 j (j+1))⌉ + 2^(J+j-2)`

and every probe has the completed-coin cap `M = ⌈√(64 N / ρ)⌉`. This is (A6)
of the adaptation proof. The budgets satisfy `N/2 ≤ ∑_j b_j ≤ N`, which is
(A10), so the pilot buys `m ∑_j b_j ≤ m N` flips.

Block `i` of the pilot's reader runs the `m` probes of depth `i + 1`, and
probe `k` of that block reads the coins `Nat.pair i (Nat.pair k c)`. The
certificate of depth `i + 1` is computed from the observed word. At depth one
no check can resolve a coin, so that certificate is one for every word. No
probability enters here. -/

noncomputable section
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.HardBudget ThresholdHC.CriticalEntropy

/-- The flip budget of each probe of depth `j` in the pilot of target depth
`J`: `⌈4^J / (2 j (j+1))⌉ + 2^(J+j-2)`. -/
def pilotBudget (J j : ℕ) : ℕ :=
  ⌈(4 : ℝ) ^ J / (2 * (j : ℝ) * ((j : ℝ) + 1))⌉₊ + 2 ^ (J + j - 2)

/-- The completed-coin cap of every probe: `⌈√(64 · 4^J / ρ)⌉`. -/
def pilotCoinCap (J : ℕ) (ρ : ℝ) : ℕ := ⌈Real.sqrt (64 * (4 : ℝ) ^ J / ρ)⌉₊

/-- Flips of one probe at every depth `1, …, J`: `∑_j b_j`. -/
def pilotSpan (J : ℕ) : ℕ := ∑ i ∈ Finset.range J, pilotBudget J (i + 1)

theorem pilotBudget_pos (J j : ℕ) : 0 < pilotBudget J j :=
  Nat.add_pos_right _ (pow_pos (by norm_num) _)

theorem pilotCoinCap_pos (J : ℕ) {ρ : ℝ} (hρ : 0 < ρ) : 0 < pilotCoinCap J ρ := by
  unfold pilotCoinCap
  exact Nat.ceil_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem sum_inv_consecutive (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 2)) = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

theorem sum_two_pow (n : ℕ) : ∑ i ∈ Finset.range n, (2 : ℝ) ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- The reciprocal parts of the budgets, before rounding up, sum to
`(N/2)(1 - 1/(J+1))`. -/
theorem pilot_reciprocal_sum (J : ℕ) :
    ∑ i ∈ Finset.range J,
        (4 : ℝ) ^ J / (2 * (((i + 1 : ℕ) : ℝ)) * ((((i + 1 : ℕ) : ℝ)) + 1)) =
      (4 : ℝ) ^ J / 2 * (1 - 1 / ((J : ℝ) + 1)) := by
  rw [← sum_inv_consecutive J, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  field_simp
  ring

/-- The geometric parts of the budgets sum to `N/2 - 2^(J-1)`, here with
`J = K + 1`. -/
theorem pilot_geometric_sum (K : ℕ) :
    ∑ i ∈ Finset.range (K + 1), ((2 ^ (K + 1 + (i + 1) - 2) : ℕ) : ℝ) =
      (4 : ℝ) ^ (K + 1) / 2 - 2 ^ K := by
  have hterm : ∀ i : ℕ, ((2 ^ (K + 1 + (i + 1) - 2) : ℕ) : ℝ) = 2 ^ K * 2 ^ i := by
    intro i
    have he : K + 1 + (i + 1) - 2 = K + i := by omega
    rw [he, pow_add]
    push_cast
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_two_pow]
  have h4 : (4 : ℝ) ^ (K + 1) = 2 ^ K * 2 ^ (K + 1) * 2 := by
    have h : (4 : ℝ) ^ (K + 1) = (2 : ℝ) ^ (K + 1) * 2 ^ (K + 1) := by
      rw [← mul_pow]
      norm_num
    rw [h, pow_succ]
    ring
  rw [h4]
  ring

/-- The span of the budgets as a real sum, with `J = K + 1`. -/
theorem pilotSpan_cast (K : ℕ) :
    ((pilotSpan (K + 1) : ℕ) : ℝ) =
      (∑ i ∈ Finset.range (K + 1),
        ((⌈(4 : ℝ) ^ (K + 1) / (2 * (((i + 1 : ℕ) : ℝ)) * ((((i + 1 : ℕ) : ℝ)) + 1))⌉₊ : ℕ) : ℝ)) +
        ((4 : ℝ) ^ (K + 1) / 2 - 2 ^ K) := by
  rw [← pilot_geometric_sum K, ← Finset.sum_add_distrib]
  unfold pilotSpan pilotBudget
  push_cast
  rfl

/-- (A10), upper half: the budgets of one probe at every depth sum to at most
`N = 4^J`. Hence the pilot with `m` probes at every depth buys at most `m N`
flips. -/
theorem pilotSpan_le {J : ℕ} (hJ : 1 ≤ J) : pilotSpan J ≤ 4 ^ J := by
  obtain ⟨K, rfl⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  have hceil : ∑ i ∈ Finset.range (K + 1),
      ((⌈(4 : ℝ) ^ (K + 1) / (2 * (((i + 1 : ℕ) : ℝ)) * ((((i + 1 : ℕ) : ℝ)) + 1))⌉₊ : ℕ) : ℝ) ≤
      ∑ i ∈ Finset.range (K + 1),
        ((4 : ℝ) ^ (K + 1) / (2 * (((i + 1 : ℕ) : ℝ)) * ((((i + 1 : ℕ) : ℝ)) + 1)) + 1) :=
    Finset.sum_le_sum fun i _ => (Nat.ceil_lt_add_one (by positivity)).le
  rw [Finset.sum_add_distrib, pilot_reciprocal_sum (K + 1)] at hceil
  have hK : ((K : ℝ) + 1) ≤ 2 ^ K := by
    have h := Nat.lt_two_pow_self (n := K)
    exact_mod_cast h
  have hpos : (0 : ℝ) < (4 : ℝ) ^ (K + 1) := by positivity
  have hfrac : (0 : ℝ) ≤ (4 : ℝ) ^ (K + 1) / 2 * (1 / ((K : ℝ) + 1 + 1)) := by positivity
  have hreal : ((pilotSpan (K + 1) : ℕ) : ℝ) ≤ ((4 ^ (K + 1) : ℕ) : ℝ) := by
    rw [pilotSpan_cast]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hceil
    push_cast at hceil ⊢
    rw [mul_sub, mul_one] at hceil
    linarith
  exact_mod_cast hreal

/-- (A10), lower half: the budgets of one probe at every depth sum to at least
`N/2`. -/
theorem le_two_mul_pilotSpan {J : ℕ} (hJ : 1 ≤ J) : 4 ^ J ≤ 2 * pilotSpan J := by
  obtain ⟨K, rfl⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  have hceil : ∑ i ∈ Finset.range (K + 1),
      (4 : ℝ) ^ (K + 1) / (2 * (((i + 1 : ℕ) : ℝ)) * ((((i + 1 : ℕ) : ℝ)) + 1)) ≤
      ∑ i ∈ Finset.range (K + 1),
        ((⌈(4 : ℝ) ^ (K + 1) / (2 * (((i + 1 : ℕ) : ℝ)) * ((((i + 1 : ℕ) : ℝ)) + 1))⌉₊ : ℕ) : ℝ) :=
    Finset.sum_le_sum fun i _ => Nat.le_ceil _
  rw [pilot_reciprocal_sum (K + 1)] at hceil
  have h2K : (2 : ℝ) ^ K ≤ 4 ^ K := pow_le_pow_left₀ (by norm_num) (by norm_num) K
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hfrac : 1 / ((K : ℝ) + 1 + 1) ≤ 1 / 2 := by
    rw [div_le_div_iff_of_pos_left (by norm_num) (by positivity) (by norm_num)]
    linarith
  have h4 : (4 : ℝ) ^ (K + 1) = 4 * 4 ^ K := by rw [pow_succ]; ring
  have hpos : (0 : ℝ) < (4 : ℝ) ^ (K + 1) := by positivity
  have hprod := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ (K + 1) / 2)
  have hreal : ((4 ^ (K + 1) : ℕ) : ℝ) ≤ ((2 * pilotSpan (K + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, pilotSpan_cast]
    push_cast at hceil ⊢
    rw [mul_sub, mul_one] at hceil
    linarith
  exact_mod_cast hreal

/-- At depth one the first check cannot resolve a coin. -/
theorem probeResolved_one_zero {h : ℕ} (hh : h ≤ 1) : probeResolved 1 0 h = false := by
  have hT : 1 ≤ tailThreshold 1 0 := by
    by_contra hlt
    have h0 : tailThreshold 1 0 ≤ 0 := by omega
    rw [tailThreshold_le_iff] at h0
    norm_num [tailScale] at h0
  have habs : |2 * (h : ℤ) - ((4 ^ 0 : ℕ) : ℤ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> push_cast <;> omega
  unfold probeResolved
  rw [decide_eq_false_iff_not]
  omega

/-- At depth one the terminal check cannot resolve a coin. -/
theorem probeResolved_one_one {h : ℕ} (hh : h ≤ 4) : probeResolved 1 1 h = false := by
  have hT : tailThreshold 1 1 = 4 := by
    rw [tailThreshold_terminal]
    norm_num
  have habs : |2 * (h : ℤ) - ((4 ^ 1 : ℕ) : ℤ)| ≤ 4 := by
    rw [abs_le]
    constructor <;> push_cast <;> omega
  unfold probeResolved
  rw [decide_eq_false_iff_not, hT]
  omega

/-- What holds of the state of a depth-one reader after every word: it is at
most at the terminal check, and it has counted at most one coin, after which
the probe has stopped. -/
def DepthOneState (st : ProbeState) : Prop :=
  st.level ≤ 1 ∧ st.len < 4 ^ st.level ∧ st.heads ≤ st.len ∧ st.count ≤ 1 ∧
    (st.count = 1 → st.stopped = true)

theorem depthOneState_step (M : ℕ) {st : ProbeState} (h : DepthOneState st) (b : Bool) :
    DepthOneState (probeStep 1 M st b) := by
  obtain ⟨hlev, hlen, hheads, hcount, hstop⟩ := h
  have hb : b.toNat ≤ 1 := by cases b <;> simp
  unfold DepthOneState probeStep
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hlev with h0 | h1
  · have hlen0 : st.len = 0 := by
      rw [h0] at hlen
      omega
    have hcheck : st.len + 1 = 4 ^ st.level := by
      rw [h0, hlen0]
      norm_num
    have hres : probeResolved 1 st.level (st.heads + b.toNat) = false := by
      rw [h0]
      exact probeResolved_one_zero (by omega)
    have hcond : ¬ (1 ≤ st.level ∨ probeResolved 1 st.level (st.heads + b.toNat) = true) := by
      rw [hres, h0]
      simp
    rw [ite_eq_left hcheck, ite_eq_right hcond]
    refine ⟨?_, ?_, ?_, hcount, hstop⟩
    · change st.level + 1 ≤ 1
      omega
    · change st.len + 1 < 4 ^ (st.level + 1)
      rw [h0, hlen0]
      norm_num
    · change st.heads + b.toNat ≤ st.len + 1
      omega
  · by_cases hcheck : st.len + 1 = 4 ^ st.level
    · have hfour : st.len + 1 = 4 := by
        rw [h1] at hcheck
        simpa using hcheck
      have hres : probeResolved 1 st.level (st.heads + b.toNat) = false := by
        rw [h1]
        exact probeResolved_one_one (by omega)
      have hcond : 1 ≤ st.level ∨ probeResolved 1 st.level (st.heads + b.toNat) = true :=
        Or.inl (by omega)
      rw [ite_eq_left hcheck, ite_eq_left hcond]
      refine ⟨Nat.zero_le _, by norm_num, le_refl _, ?_, ?_⟩
      · change (if st.stopped = true then st.count else st.count + 1) ≤ 1
        by_cases hs : st.stopped = true
        · rw [ite_eq_left hs]
          exact hcount
        · rw [ite_eq_right hs]
          have hne : st.count ≠ 1 := fun hc => hs (hstop hc)
          omega
      · intro _
        change (st.stopped || !probeResolved 1 st.level (st.heads + b.toNat) ||
          decide (M < st.coin + 2)) = true
        rw [hres]
        simp
    · rw [ite_eq_right hcheck]
      refine ⟨hlev, ?_, ?_, hcount, hstop⟩
      · change st.len + 1 < 4 ^ st.level
        omega
      · change st.heads + b.toNat ≤ st.len + 1
        omega

theorem depthOneState_run (M : ℕ) (w : List Bool) : DepthOneState (probeRun 1 M w) := by
  induction w using List.reverseRecOn with
  | nil =>
    unfold DepthOneState
    change (0 : ℕ) ≤ 1 ∧ (0 : ℕ) < 4 ^ 0 ∧ (0 : ℕ) ≤ 0 ∧ (0 : ℕ) ≤ 1 ∧
      ((0 : ℕ) = 1 → decide (M = 0) = true)
    refine ⟨by norm_num, by norm_num, le_refl _, by norm_num, fun h => absurd h (by norm_num)⟩
  | append_singleton w b ih =>
    rw [probeRun_append]
    exact depthOneState_step M ih b

/-- A depth-one probe counts at most one coin, on every word of flips. -/
theorem probeWordCompleted_depth_one (M : ℕ) (w : List Bool) : probeWordCompleted 1 M w ≤ 1 :=
  (depthOneState_run M w).2.2.2.1

theorem probeUpper_one : probeUpper 1 = 1 := by
  unfold probeUpper
  norm_num

/-- Depth one returns the trivial certificate on every word of flips: no
check of a depth-one test can resolve a coin, so the first coin stops the
probe. -/
theorem medianWordUpper_depth_one (m b M : ℕ) (w : List Bool) :
    medianWordUpper 1 m b M w = 1 := by
  unfold medianWordUpper
  have hv : ∀ j, j < m →
      probeUpper (probeWordCompleted 1 M (seqWord (fun _ => b) j w)) =
        (fun _ : ℕ => (1 : ℝ)) j := by
    intro j _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
      (probeWordCompleted_depth_one M (seqWord (fun _ => b) j w)) with h0 | h1
    · rw [h0, probeUpper_zero]
    · rw [h1, probeUpper_one]
  rw [blockMedian_congr hv]
  by_cases hm : 0 < m
  · obtain ⟨j, -, hj⟩ := blockMedian_eq_value hm (fun _ : ℕ => (1 : ℝ))
    rw [hj]
  · have hz : m = 0 := by omega
    subst hz
    exact blockMedian_zero _

/-- The certificate computed from a word lies in `(0, 1]`. -/
theorem medianWordUpper_pos (J m b M : ℕ) (w : List Bool) : 0 < medianWordUpper J m b M w := by
  unfold medianWordUpper
  by_cases hm : 0 < m
  · obtain ⟨j, -, hj⟩ := blockMedian_eq_value hm
      (fun j => probeUpper (probeWordCompleted J M (seqWord (fun _ => b) j w)))
    rw [hj]
    exact probeUpper_pos _
  · have hz : m = 0 := by omega
    subst hz
    rw [blockMedian_zero]
    norm_num

theorem medianWordUpper_le_one (J m b M : ℕ) (w : List Bool) :
    medianWordUpper J m b M w ≤ 1 := by
  unfold medianWordUpper
  by_cases hm : 0 < m
  · obtain ⟨j, -, hj⟩ := blockMedian_eq_value hm
      (fun j => probeUpper (probeWordCompleted J M (seqWord (fun _ => b) j w)))
    rw [hj]
    exact probeUpper_le_one _
  · have hz : m = 0 := by omega
    subst hz
    rw [blockMedian_zero]

/-- Flips of block `i` of the pilot: the `m` probes of depth `i + 1`. -/
def pilotLength (J m i : ℕ) : ℕ := m * pilotBudget J (i + 1)

/-- The pilot's reader. Block `i` runs the `m` probes of depth `i + 1`, each
with flip budget `b_(i+1)` and coin cap `M`; probe `k` of that block reads the
coins `Nat.pair i (Nat.pair k c)`. -/
def pilotReader (J m M : ℕ) : Reader :=
  seqReader (pilotLength J m) (fun i => medianReader (i + 1) M (pilotBudget J (i + 1)) m) J

/-- Flips the pilot buys. -/
def pilotCost (J m : ℕ) : ℕ := seqOffset (pilotLength J m) J

/-- The certificate of depth `i + 1` computed from an observed word of the
pilot. -/
def pilotUpper (J m M : ℕ) (w : List Bool) (i : ℕ) : ℝ :=
  medianWordUpper (i + 1) m (pilotBudget J (i + 1)) M (seqWord (pilotLength J m) i w)

/-- The pilot buys `m ∑_j b_j` flips. -/
theorem pilotCost_eq (J m : ℕ) : pilotCost J m = m * pilotSpan J := by
  unfold pilotCost seqOffset pilotSpan pilotLength
  rw [Finset.mul_sum]

/-- The pilot buys at most `m N` flips. -/
theorem pilotCost_le {J : ℕ} (hJ : 1 ≤ J) (m : ℕ) : pilotCost J m ≤ m * 4 ^ J := by
  rw [pilotCost_eq]
  exact Nat.mul_le_mul_left m (pilotSpan_le hJ)

/-- Depth one returns one on every word of flips. -/
theorem pilotUpper_zero (J m M : ℕ) (w : List Bool) : pilotUpper J m M w 0 = 1 :=
  medianWordUpper_depth_one m _ M _

theorem pilotUpper_nonneg (J m M : ℕ) (w : List Bool) (i : ℕ) : 0 ≤ pilotUpper J m M w i :=
  (medianWordUpper_pos _ _ _ _ _).le

theorem pilotUpper_le_one (J m M : ℕ) (w : List Bool) (i : ℕ) : pilotUpper J m M w i ≤ 1 :=
  medianWordUpper_le_one _ _ _ _ _

/-- The certificate of depth `i + 1 ≤ J` computed from the observed word of
the pilot is the tape-level median certificate of the `m` probes of that
depth, probe `k` reading the coins `Nat.pair i (Nat.pair k c)`. -/
theorem pilotUpper_readBlock (J m M : ℕ) (s : Table) {i : ℕ} (hi : i < J) :
    pilotUpper J m M (readBlock (pilotCost J m) (pilotReader J m M) s).1 i =
      medianUpper (i + 1) m (fun _ => pilotBudget J (i + 1)) (fun _ => M)
        (fun k c => s (Nat.pair i (Nat.pair k c))) := by
  have h := (seqReader_readBlock (pilotLength J m)
    (fun i => medianReader (i + 1) M (pilotBudget J (i + 1)) m) s J).1 i hi
  unfold pilotUpper
  change medianWordUpper (i + 1) m (pilotBudget J (i + 1)) M (seqWord (pilotLength J m) i
    (readBlock (seqOffset (pilotLength J m) J) (seqReader (pilotLength J m)
      (fun i => medianReader (i + 1) M (pilotBudget J (i + 1)) m) J) s).1) = _
  rw [h]
  exact medianWordUpper_readBlock (i + 1) m (pilotBudget J (i + 1)) M (fun c => s (Nat.pair i c))

end ThresholdHC.ArbitraryLawAdaptation
