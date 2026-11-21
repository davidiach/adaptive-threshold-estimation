import ThresholdHC.Statements2

/-! The capped two-boundary walk on finite words.

States are natural numbers. The walk starts at a state `k`, moves up on a one bit
and down on a zero bit, and stops at the lower boundary `0`, at the upper boundary
`K` (or above), or when the word is exhausted. `walkRun` returns the number of
bits read and the final state. `walkSum p` is the expectation of a statistic of
the run under independent bits with success probability `p`. -/

noncomputable section
namespace ThresholdHC.RadialUpper

/-- One step of the walk. -/
def walkStep (k : ℕ) (x : Bool) : ℕ := if x then k+1 else k-1

/-- The capped walk on a word: the number of bits read and the final state. -/
def walkRun (K : ℕ) : (n : ℕ) → ℕ → (Fin n → Bool) → ℕ × ℕ
  | 0, k, _ => (0, k)
  | n+1, k, w =>
    if 0 < k ∧ k < K then
      ((walkRun K n (walkStep k (w 0)) (Fin.tail w)).1+1,
        (walkRun K n (walkStep k (w 0)) (Fin.tail w)).2)
    else (0, k)

/-- Expectation of a statistic of the run under independent bits of mean `p`. -/
def walkSum (p : ℝ) (K n k : ℕ) (g : ℕ × ℕ → ℝ) : ℝ :=
  ∑ w : Fin n → Bool, streamProb p w * g (walkRun K n k w)

/-- The upper-hit indicator of a final state. -/
def walkHit (K k : ℕ) : ℝ := if K ≤ k then 1 else 0

theorem walkHit_nonneg (K k : ℕ) : 0 ≤ walkHit K k := by
  unfold walkHit; split <;> norm_num

theorem walkHit_le_one (K k : ℕ) : walkHit K k ≤ 1 := by
  unfold walkHit; split <;> norm_num

theorem walkHit_sq (K k : ℕ) : walkHit K k ^ 2 = walkHit K k := by
  unfold walkHit; split <;> norm_num

theorem walkRun_cons (K n k : ℕ) (x : Bool) (t : Fin n → Bool) :
    walkRun K (n+1) k (Fin.cons x t) =
      if 0 < k ∧ k < K then
        ((walkRun K n (walkStep k x) t).1+1, (walkRun K n (walkStep k x) t).2)
      else (0, k) := by
  simp only [walkRun, Fin.cons_zero, Fin.tail_cons]

private theorem radial_sum_words {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) :
    ∑ s, f s = (∑ t, f (Fin.cons false t)) + ∑ t, f (Fin.cons true t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool]
  exact add_comm ..

theorem streamProb_cons (p : ℝ) {n : ℕ} (x : Bool) (t : Fin n → Bool) :
    streamProb p (Fin.cons x t : Fin (n+1) → Bool) = (if x then p else 1-p) * streamProb p t := by
  simp only [streamProb, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem streamProb_sum (p : ℝ) (n : ℕ) : ∑ w : Fin n → Bool, streamProb p w = 1 := by
  induction n with
  | zero => simp [streamProb]
  | succ n ih =>
    rw [radial_sum_words]
    simp only [streamProb_cons, Bool.false_eq_true, ite_false, ite_true, ← Finset.mul_sum, ih]
    ring

theorem streamProb_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {n : ℕ} (w : Fin n → Bool) :
    0 ≤ streamProb p w :=
  Finset.prod_nonneg fun i _ => by split <;> linarith

theorem walkSum_zero (p : ℝ) (K k : ℕ) (g : ℕ × ℕ → ℝ) : walkSum p K 0 k g = g (0, k) := by
  simp [walkSum, walkRun, streamProb]

theorem walkSum_stop (p : ℝ) (K n k : ℕ) (g : ℕ × ℕ → ℝ) (hk : ¬(0 < k ∧ k < K)) :
    walkSum p K (n+1) k g = g (0, k) := by
  unfold walkSum
  simp only [walkRun, ite_eq_right hk]
  rw [← Finset.sum_mul, streamProb_sum, one_mul]

theorem walkSum_move (p : ℝ) (K n k : ℕ) (g : ℕ × ℕ → ℝ) (hk : 0 < k ∧ k < K) :
    walkSum p K (n+1) k g =
      p * walkSum p K n (k+1) (fun r => g (r.1+1, r.2)) +
        (1-p) * walkSum p K n (k-1) (fun r => g (r.1+1, r.2)) := by
  unfold walkSum
  rw [radial_sum_words, add_comm]
  simp only [walkRun_cons, ite_eq_left hk, streamProb_cons, walkStep, Bool.false_eq_true, ite_false,
    ite_true, Finset.mul_sum, mul_assoc]

theorem walkSum_mono {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (K n k : ℕ) {g h : ℕ × ℕ → ℝ}
    (hgh : ∀ w : Fin n → Bool, g (walkRun K n k w) ≤ h (walkRun K n k w)) :
    walkSum p K n k g ≤ walkSum p K n k h :=
  Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hgh w) (streamProb_nonneg h0 h1 w)

theorem walkSum_add (p : ℝ) (K n k : ℕ) (g h : ℕ × ℕ → ℝ) :
    walkSum p K n k (fun r => g r + h r) = walkSum p K n k g + walkSum p K n k h := by
  unfold walkSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => mul_add _ _ _

theorem walkSum_const_mul (p : ℝ) (K n k : ℕ) (c : ℝ) (g : ℕ × ℕ → ℝ) :
    walkSum p K n k (fun r => c * g r) = c * walkSum p K n k g := by
  unfold walkSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem walkSum_const (p : ℝ) (K n k : ℕ) (c : ℝ) :
    walkSum p K n k (fun _ => c) = c := by
  unfold walkSum
  rw [← Finset.sum_mul, streamProb_sum, one_mul]

theorem walkSum_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (K n k : ℕ) {g : ℕ × ℕ → ℝ}
    (hg : ∀ r, 0 ≤ g r) : 0 ≤ walkSum p K n k g :=
  Finset.sum_nonneg fun w _ => mul_nonneg (streamProb_nonneg h0 h1 w) (hg _)

theorem walkSum_le_const {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (K n k : ℕ) {g : ℕ × ℕ → ℝ} {c : ℝ}
    (hg : ∀ r, g r ≤ c) : walkSum p K n k g ≤ c := by
  have h := walkSum_mono h0 h1 K n k (g := g) (h := fun _ => c) (fun w => hg _)
  rwa [walkSum_const] at h

/-- A function harmonic at interior states has constant expectation. -/
theorem walkSum_harmonic (p : ℝ) (K : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k, 0 < k → k < K → p * f (k+1) + (1-p) * f (k-1) = f k) (n k : ℕ) :
    walkSum p K n k (fun r => f r.2) = f k := by
  induction n generalizing k with
  | zero => simp [walkSum_zero]
  | succ n ih =>
    by_cases hk : 0 < k ∧ k < K
    · rw [walkSum_move _ _ _ _ _ hk]
      simp only
      rw [ih, ih]
      exact hf k hk.1 hk.2
    · rw [walkSum_stop _ _ _ _ _ hk]

/-- A function superharmonic at interior states bounds its expectation. -/
theorem walkSum_superharmonic {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (K : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k, 0 < k → k < K → p * f (k+1) + (1-p) * f (k-1) ≤ f k) (n k : ℕ) :
    walkSum p K n k (fun r => f r.2) ≤ f k := by
  induction n generalizing k with
  | zero => simp [walkSum_zero]
  | succ n ih =>
    by_cases hk : 0 < k ∧ k < K
    · rw [walkSum_move _ _ _ _ _ hk]
      simp only
      calc _ ≤ p * f (k+1) + (1-p) * f (k-1) :=
            add_le_add (mul_le_mul_of_nonneg_left (ih _) h0)
              (mul_le_mul_of_nonneg_left (ih _) (by linarith))
        _ ≤ f k := hf k hk.1 hk.2
    · rw [walkSum_stop _ _ _ _ _ hk]

/-- Expected number of bits read, bounded by a nonnegative solution of the step inequality. -/
theorem walkSum_steps_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (K : ℕ) (W : ℕ → ℝ)
    (hW0 : ∀ k, k ≤ K → 0 ≤ W k)
    (hW : ∀ k, 0 < k → k < K → 1 + p * W (k+1) + (1-p) * W (k-1) ≤ W k) (n k : ℕ)
    (hk : k ≤ K) : walkSum p K n k (fun r => (r.1 : ℝ)) ≤ W k := by
  induction n generalizing k with
  | zero => simpa [walkSum_zero] using hW0 k hk
  | succ n ih =>
    by_cases hi : 0 < k ∧ k < K
    · rw [walkSum_move _ _ _ _ _ hi]
      have hs (j : ℕ) : walkSum p K n j (fun r => (((r.1+1 : ℕ)) : ℝ)) =
          walkSum p K n j (fun r => (r.1 : ℝ)) + 1 := by
        rw [← walkSum_const p K n j 1, ← walkSum_add]
        simp only [Nat.cast_succ]
      simp only
      rw [hs, hs]
      have ha := ih (k+1) (by omega)
      have hb := ih (k-1) (by omega)
      calc _ = 1 + p * walkSum p K n (k+1) (fun r => (r.1 : ℝ)) +
            (1-p) * walkSum p K n (k-1) (fun r => (r.1 : ℝ)) := by ring
        _ ≤ 1 + p * W (k+1) + (1-p) * W (k-1) :=
            add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left ha h0))
              (mul_le_mul_of_nonneg_left hb (by linarith))
        _ ≤ W k := hW k hi.1 hi.2
    · rw [walkSum_stop _ _ _ _ _ hi]
      simpa using hW0 k hk

theorem walkRun_steps_le (K n k : ℕ) (w : Fin n → Bool) : (walkRun K n k w).1 ≤ n := by
  induction n generalizing k with
  | zero => simp [walkRun]
  | succ n ih =>
    simp only [walkRun]
    split
    · exact Nat.succ_le_succ (ih _ _)
    · exact Nat.zero_le _

/-- A run that ends at an interior state has read the whole word. -/
theorem walkRun_alive (K n k : ℕ) (w : Fin n → Bool)
    (h : 0 < (walkRun K n k w).2 ∧ (walkRun K n k w).2 < K) : (walkRun K n k w).1 = n := by
  induction n generalizing k with
  | zero => simp [walkRun]
  | succ n ih =>
    simp only [walkRun] at h ⊢
    split at h
    · rw [ite_eq_left (by assumption)]
      exact congrArg (· + 1) (ih _ _ h)
    · rename_i hk
      exact absurd h hk

theorem walkRun_steps_pos (K n k : ℕ) (w : Fin n → Bool) (hk : 0 < k ∧ k < K) (hn : 0 < n) :
    0 < (walkRun K n k w).1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  simp only [walkRun, ite_eq_left hk]
  exact Nat.succ_pos _

/-- The run depends only on the bits it reads. -/
theorem walkRun_prefix (K n k : ℕ) (w w' : Fin n → Bool)
    (h : ∀ i : Fin n, i.val < (walkRun K n k w).1 → w i = w' i) :
    walkRun K n k w' = walkRun K n k w := by
  induction n generalizing k with
  | zero => simp [walkRun]
  | succ n ih =>
    by_cases hk : 0 < k ∧ k < K
    · simp only [walkRun, ite_eq_left hk] at h ⊢
      have h0 : w 0 = w' 0 := h 0 (by simp)
      have ht : ∀ i : Fin n,
          i.val < (walkRun K n (walkStep k (w 0)) (Fin.tail w)).1 → Fin.tail w i = Fin.tail w' i :=
        fun i hi => h i.succ (by simp only [Fin.val_succ]; omega)
      rw [← h0, ih _ _ _ ht]
    · simp only [walkRun, ite_eq_right hk]

end ThresholdHC.RadialUpper
