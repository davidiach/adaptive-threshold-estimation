import ThresholdHC.Tier5.CreationBase
import ThresholdHC.Tier5.CreationProduct

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.Tier5
open ThresholdHC.Proofs ThresholdHC.Tier3

def freshTruncatedPrefix {m : ℕ} (N n : ℕ) (hn : n ≤ m) (s : Fin m → Bool) : Prefix n :=
  fun i => if i.val < N+1 then some (s (Fin.castLE hn i)) else none

theorem freshTruncatedPrefix_snoc {m : ℕ} (N n : ℕ) (hn : n+1 ≤ m) (s : Fin m → Bool) :
    freshTruncatedPrefix N (n+1) hn s =
      Fin.snoc (freshTruncatedPrefix N n (Nat.le_of_succ_le hn) s)
        (if n < N+1 then some (s ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩) else none) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [freshTruncatedPrefix]
    rfl
  · simp [freshTruncatedPrefix]

theorem freshTruncatedPrefix_hist_length {m : ℕ} (N n : ℕ) (hn : n ≤ m)
    (s : Fin m → Bool) :
    (fullHist (freshTruncatedPrefix N n hn s)).length = min n (N+1) := by
  induction n with
  | zero => simp [freshTruncatedPrefix, fullHist]
  | succ n ih =>
    rw [freshTruncatedPrefix_snoc, fullHist_snoc_example, List.length_append,
      ih (Nat.le_of_succ_le hn)]
    by_cases h : n < N+1 <;> simp [h] <;> omega

theorem fresh_path_expect {m : ℕ} (N : ℕ) (s : Fin m → Bool) (n : ℕ) (hn : n ≤ m)
    (f : Prefix n → ℝ) :
    (∑ w : Prefix n, pathProb (capPolicy m (freshPolicy N))
      (fun i => if s i then 1 else 0) w * f w) =
      f (freshTruncatedPrefix N n hn s) := by
  induction n with
  | zero =>
    simp [pathProb]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    rw [sum_snoc]
    simp_rw [pathProb_snoc, mul_assoc, ← Finset.mul_sum]
    rw [ih (Nat.le_of_succ_le hn)]
    rw [freshTruncatedPrefix_snoc]
    have hnm : n < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    have hpol : capPolicy m (freshPolicy N)
        (fullHist (freshTruncatedPrefix N n (Nat.le_of_succ_le hn) s)) =
        if n < N+1 then some (⟨n,hnm⟩ : Fin m) else none := by
      unfold capPolicy freshPolicy
      rw [freshTruncatedPrefix_hist_length]
      by_cases h : n < N+1
      · have hm : min n (N+1) = n := min_eq_left h.le
        simp [hm, h, hnm]
      · have hm : min n (N+1) = N+1 := min_eq_right (Nat.le_of_not_gt h)
        simp [hm, h]
    by_cases h : n < N+1
    · rw [if_pos h] at hpol ⊢
      cases hs : s ⟨n,hnm⟩ <;>
        simp [stepProb, hpol, hs, Fintype.sum_option, Fintype.sum_bool]
    · rw [if_neg h] at hpol ⊢
      simp [stepProb, hpol, Fintype.sum_option]

theorem fresh_coinCap_le (N n : ℕ) : coinCap n (freshPolicy N) ≤ n+1 := by
  unfold coinCap
  apply Nat.add_le_add_right
  apply Finset.sup_le
  intro wt hwt
  have hlen := histBefore_length_le wt.1 wt.2
  unfold freshPolicy
  split_ifs <;> simp only [Option.getD_some, Option.getD_none]
  · exact hlen.trans wt.2.isLt.le
  · exact Nat.zero_le _

theorem fresh_transcript_expect (N n : ℕ) (q : ℝ) (f : Prefix n → ℝ) :
    (∑ w : Prefix n, creationLaw (freshPolicy N) (fun _ => 1/2) (fun _ => q) w * f w) =
      ∑ s : Fin (n+1) → Bool, (∏ i, if s i then q else 1-q) *
        f (freshTruncatedPrefix N n (Nat.le_succ n) s) := by
  simp_rw [creationLaw_eq_capped (freshPolicy N) (fun _ => 1/2) (fun _ => q) _ (n+1)
    (fresh_coinCap_le N n)]
  unfold transcriptLaw
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  have hcoin : (fun i : Fin (n+1) => (1/2:ℝ) + if s i then (1/2:ℝ) else -(1/2:ℝ)) =
      (fun i => if s i then (1:ℝ) else 0) := by
    funext i
    cases s i <;> norm_num
  rw [hcoin]
  exact fresh_path_expect N s n (Nat.le_succ n) f

end ThresholdHC.Tier5
