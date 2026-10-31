import ThresholdHC.StoppingProgram.Bellman
import ThresholdHC.StoppingProgram.Model

/-! A finite triangular array of linear Bellman inequalities is an exact
certificate for the nonpositive root-surplus condition. -/

noncomputable section
namespace ThresholdHC.Genie
open ThresholdHC.StoppingProgram

def BellmanEnvelope {N : ℕ} (r w : ℕ → ℕ → ℝ) (η : ℝ) (X : CountState N → ℝ) : Prop :=
  (∀ n k, 1 ≤ n → n ≤ N → k ≤ n → r n k ≤ arrayAt X n k) ∧
  (∀ n k, 1 ≤ n → n < N → k ≤ n →
    arrayAt X (n+1) k+arrayAt X (n+1) (k+1)-η*w n k ≤ arrayAt X n k) ∧
  arrayAt X 1 0+arrayAt X 1 1-η ≤ 0

theorem bellman_le_envelope {N : ℕ} (r w : ℕ → ℕ → ℝ) (η : ℝ)
    (X : CountState N → ℝ) (hX : BellmanEnvelope r w η X)
    (d n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (hnd : n+d = N) :
    bellman r w η d n k ≤ arrayAt X n k := by
  induction d generalizing n k with
  | zero => exact hX.1 n k hn (by omega) hk
  | succ d ih =>
    apply max_le (hX.1 n k hn (by omega) hk)
    exact (sub_le_sub_right (add_le_add (ih (n+1) k (by omega) (by omega) (by omega))
      (ih (n+1) (k+1) (by omega) (by omega) (by omega))) _).trans
        (hX.2.1 n k hn (by omega) hk)

theorem envelope_root {N : ℕ} (r w : ℕ → ℕ → ℝ) (η : ℝ)
    (hN : 0 < N) (X : CountState N → ℝ) (hX : BellmanEnvelope r w η X) :
    rootBellman r w η (N-1) ≤ 0 := by
  exact (sub_le_sub_right (add_le_add
    (bellman_le_envelope r w η X hX (N-1) 1 0 (by omega) (by omega) (by omega))
    (bellman_le_envelope r w η X hX (N-1) 1 1 (by omega) (by omega) (by omega))) _).trans hX.2.2

def bellmanEnvelopeArray (N : ℕ) (r w : ℕ → ℕ → ℝ) (η : ℝ) : CountState N → ℝ :=
  fun s => bellman r w η (N-s.1.val) s.1.val s.2.val

theorem arrayAt_bellmanEnvelopeArray (N : ℕ) (r w : ℕ → ℕ → ℝ) (η : ℝ)
    (n k : ℕ) (hn : n ≤ N) (hk : k ≤ n) :
    arrayAt (bellmanEnvelopeArray N r w η) n k = bellman r w η (N-n) n k := by
  simp [arrayAt,bellmanEnvelopeArray,hn,hk]

theorem exists_bellmanEnvelope_iff (N : ℕ) (r w : ℕ → ℕ → ℝ) (η : ℝ) (hN : 0 < N) :
    (∃ X : CountState N → ℝ, BellmanEnvelope r w η X) ↔ rootBellman r w η (N-1) ≤ 0 := by
  constructor
  · rintro ⟨X,hX⟩
    exact envelope_root r w η hN X hX
  · intro hroot
    refine ⟨bellmanEnvelopeArray N r w η,?_,?_,?_⟩
    · intro n k hn hnN hk
      rw [arrayAt_bellmanEnvelopeArray _ _ _ _ _ _ hnN hk]
      cases hd : N-n with
      | zero => exact le_rfl
      | succ d => exact le_max_left _ _
    · intro n k hn hnN hk
      rw [arrayAt_bellmanEnvelopeArray _ _ _ _ _ _ (by omega) (by omega),
        arrayAt_bellmanEnvelopeArray _ _ _ _ _ _ (by omega) (by omega),
        arrayAt_bellmanEnvelopeArray _ _ _ _ _ _ (by omega) hk]
      have hd : N-n = (N-(n+1))+1 := by omega
      rw [hd,bellman]
      exact le_max_right _ _
    · simpa only [rootBellman,arrayAt_bellmanEnvelopeArray _ _ _ _ _ _ (by omega : 1 ≤ N) (by omega : 0 ≤ 1),
        arrayAt_bellmanEnvelopeArray _ _ _ _ _ _ (by omega : 1 ≤ N) (by omega : 1 ≤ 1)] using hroot

theorem bellman_scale (r w : ℕ → ℕ → ℝ) (κ c : ℝ) (hc : 0 ≤ c) (d n k : ℕ) :
    bellman (fun n k => c*r n k) w (c*κ) d n k = c*bellman r w κ d n k := by
  induction d generalizing n k with
  | zero => rfl
  | succ d ih =>
    simp only [bellman,ih]
    rw [mul_max_of_nonneg _ _ hc]
    congr 1
    ring

theorem rootBellman_scale (r w : ℕ → ℕ → ℝ) (κ c : ℝ) (hc : 0 ≤ c) (d : ℕ) :
    rootBellman (fun n k => c*r n k) w (c*κ) d = c*rootBellman r w κ d := by
  simp only [rootBellman,bellman_scale r w κ c hc]
  ring

end ThresholdHC.Genie
