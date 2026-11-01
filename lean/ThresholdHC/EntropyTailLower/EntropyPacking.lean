import ThresholdHC.EntropyTailLower.FiniteSelection

noncomputable section
namespace ThresholdHC.EntropyTailLower
open Real ThresholdHC.EntropyTailQuantile
open scoped BigOperators

theorem costEntropy_partition {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (a : I → ℝ) (p : I → J) :
    costEntropy a =
      (∑ j, costEntropy (fun i => if p i = j then a i else 0)) +
        costEntropy (fun j => costTotal (fun i => if p i = j then a i else 0)) -
        costTotal a := by
  have ht : (∑ j, costTotal (fun i => if p i = j then a i else 0)) = costTotal a := by
    simp only [costTotal]
    rw [Finset.sum_comm]
    simp
  have hn : (∑ j, ∑ i, negMulLog (if p i = j then a i else 0)) =
      ∑ i, negMulLog (a i) := by
    simp_rw [apply_ite negMulLog,negMulLog_zero]
    rw [Finset.sum_comm]
    simp
  simp only [costEntropy,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  change _ = _ + ((∑ j, costTotal (fun i => if p i = j then a i else 0)) + _ -
    negMulLog (∑ j, costTotal (fun i => if p i = j then a i else 0))) - _
  rw [ht,hn]
  ring

theorem costEntropy_partition_reference {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (a : I → ℝ) (p : I → J) (q : J → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hq : ∀ j, 0 < q j) (hqsum : (∑ j, q j) ≤ 1) :
    costEntropy a ≤ (∑ j, costEntropy (fun i => if p i = j then a i else 0)) +
      ∑ j, costTotal (fun i => if p i = j then a i else 0) * (-log (q j)) := by
  have hg (j) : 0 ≤ costTotal (fun i => if p i = j then a i else 0) := by
    apply costTotal_nonneg
    intro i
    split_ifs
    · exact ha i
    · exact le_rfl
  have hb := costEntropy_le_reference hg hq hqsum
  have ht : (∑ j, costTotal (fun i => if p i = j then a i else 0)) = costTotal a := by
    simp only [costTotal]
    rw [Finset.sum_comm]
    simp
  have hs : (∑ j, costTotal (fun i => if p i = j then a i else 0)*(1-log (q j))) =
      costTotal a + ∑ j, costTotal (fun i => if p i = j then a i else 0)*(-log (q j)) := by
    simp only [mul_sub,mul_one,mul_neg,Finset.sum_sub_distrib,Finset.sum_neg_distrib,ht]
    ring
  rw [hs] at hb
  rw [costEntropy_partition a p]
  linarith only [hb]

theorem sum_half_pow_prefix (n : ℕ) :
    (∑ i : Fin n, (1/2:ℝ)^(i.val+1)) = 1-(1/2:ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih,pow_succ]
    ring

theorem sum_weighted_half_pow_prefix (n : ℕ) :
    (∑ i : Fin n, (i.val+1:ℝ)*(1/2:ℝ)^i.val) =
      4-(2*n+4)*(1/2:ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,ih,pow_succ,Nat.cast_add,Nat.cast_one]
    ring

theorem sum_weighted_half_pow_le_four (n : ℕ) :
    (∑ i : Fin n, (i.val+1:ℝ)*(1/2:ℝ)^i.val) ≤ 4 := by
  rw [sum_weighted_half_pow_prefix]
  have h : 0 ≤ (2*(n:ℝ)+4)*(1/2:ℝ)^n := by positivity
  linarith

theorem costEntropy_geometric_reference (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    costEntropy a ≤ costTotal a + ∑ i, a i*(i.val+1:ℝ)*log 2 := by
  have hp : (∑ i : Fin n, (1/2:ℝ)^(i.val+1)) ≤ 1 := by
    rw [sum_half_pow_prefix]
    have h : 0 ≤ (1/2:ℝ)^n := by positivity
    linarith
  have hb := costEntropy_le_reference ha (fun i => by positivity : ∀ i : Fin n, (0:ℝ)<(1/2:ℝ)^(i.val+1)) hp
  have he (i : Fin n) : a i*(1-log ((1/2:ℝ)^(i.val+1))) =
      a i + a i*(i.val+1:ℝ)*log 2 := by
    rw [log_pow]
    simp only [one_div,log_inv,Nat.cast_add,Nat.cast_one]
    ring
  simp_rw [he] at hb
  simpa only [Finset.sum_add_distrib,costTotal] using hb

theorem nat_le_two_pow_pred (n : ℕ) (hn : 1 ≤ n) : n ≤ 2^(n-1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hpow := pow_succ (2:ℕ) (n-1)
    rw [Nat.sub_add_cancel hn] at hpow
    simpa only [Nat.add_sub_cancel] using
      (show n+1 ≤ 2^n by nlinarith only [ih,hpow,hn])

theorem clog_four_le_half (n : ℕ) (hn : 2 ≤ n) : Nat.clog 4 n ≤ n/2 := by
  apply Nat.clog_le_of_le_pow
  have h := nat_le_two_pow_pred n (by omega)
  have he : n-1 ≤ 2*(n/2) := by omega
  have hp := Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) he
  have heq : (2:ℕ)^(2*(n/2)) = 4^(n/2) := by rw [pow_mul]; norm_num
  rw [heq] at hp
  exact h.trans hp

theorem clog_four_trim_size (n : ℕ) (hn : 0 < n) :
    0 < n - Nat.clog 4 n ∧ (n:ℝ)/2 ≤ (n - Nat.clog 4 n:ℕ) := by
  by_cases h1 : n = 1
  · subst n; norm_num
  · have hc := clog_four_le_half n (by omega)
    constructor
    · omega
    · have hh : n ≤ 2*(n - Nat.clog 4 n) := by omega
      have hh' : (n:ℝ) ≤ 2*(n - Nat.clog 4 n:ℕ) := by exact_mod_cast hh
      linarith

theorem trimmed_gap_amplification (n t : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (b : Fin n → ℝ) (hb : ∀ i, δ ≤ b i) (ht : n ≤ 4^t)
    (hsep : ∀ (i : Fin n) (k : ℕ) (hik : i.val+k < n),
      (4:ℝ)^k * b ⟨i.val+k,hik⟩ ≤ b i)
    (i : Fin (n-t)) :
    (n:ℝ)*δ ≤ b ⟨i.val,by omega⟩ := by
  have hi : i.val+t < n := by omega
  have hs := hsep ⟨i.val,by omega⟩ t hi
  have hh := mul_le_mul_of_nonneg_left (hb ⟨i.val+t,hi⟩)
    (show (0:ℝ) ≤ 4^t by positivity)
  have ht' : (n:ℝ) ≤ 4^t := by exact_mod_cast ht
  have hm := mul_le_mul_of_nonneg_right ht' hδ
  exact hm.trans (hh.trans hs)

theorem costEntropy_const {I : Type} [Fintype I] (c : ℝ) :
    costEntropy (fun _ : I => c) = c * (Fintype.card I:ℝ) * (1 + log (Fintype.card I)) := by
  have he : (fun _ : I => c) = (fun _ : I => c*(1:ℝ)) := by funext i; ring
  rw [he,costEntropy_smul]
  simp only [costEntropy,costTotal,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_one,negMulLog,log_one,mul_zero,neg_zero,add_zero]
  ring

theorem comparable_cost_entropy_bounds {I : Type} [Fintype I]
    (a : I → ℝ) (c : ℝ) (hc : 0 ≤ c) (ha : ∀ i, c ≤ a i)
    (ha4 : ∀ i, a i ≤ 4*c) :
    c*(Fintype.card I:ℝ)*(1+log (Fintype.card I)) ≤ costEntropy a ∧
      costEntropy a ≤ 4*c*(Fintype.card I:ℝ)*(1+log (Fintype.card I)) := by
  constructor
  · have hm := costEntropy_mono (a := fun _ : I => c) (fun _ => hc) ha
    rwa [costEntropy_const] at hm
  · have hm := costEntropy_mono (fun i => hc.trans (ha i)) ha4
    rwa [costEntropy_const] at hm

theorem log_card_half_bound (n m : ℝ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n/2 ≤ m) :
    n*(1+log n) ≤ 16*m*(1+log m) := by
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  have hln : 0 ≤ log n := log_nonneg hn
  have hlm : 0 ≤ log m := log_nonneg hm
  have hl := log_le_log (show 0 < n/2 by positivity) hnm
  rw [log_div hn0.ne' (by norm_num : (2:ℝ) ≠ 0)] at hl
  have hlog2 : log (2:ℝ) ≤ 7/8 := by linarith only [log_two_lt_d9]
  have hlog : 1+log n ≤ 8*(1+log m) := by linarith
  have h1 := mul_le_mul_of_nonneg_right (show n ≤ 2*m by linarith) (show 0 ≤ 1+log n by linarith)
  have h2 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*m by positivity)
  nlinarith only [h1,h2]

theorem comparable_entropy_trim_bound (c n m F G : ℝ)
    (hc : 0 ≤ c) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n/2 ≤ m)
    (hF : F ≤ 4*c*n*(1+log n)) (hG : c*m*(1+log m) ≤ G) :
    F ≤ 64*G := by
  have h := mul_le_mul_of_nonneg_left (log_card_half_bound n m hn hm hnm) hc
  nlinarith only [h,hF,hG]

theorem comparable_entropy_subfamily {I J : Type} [Fintype I] [Fintype J]
    (a : I → ℝ) (b : J → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ i, 0 ≤ a i) (ha4 : ∀ i, a i ≤ 4*c) (hb : ∀ j, c ≤ b j)
    (hI : 0 < Fintype.card I) (hJ : 0 < Fintype.card J)
    (hhalf : (Fintype.card I:ℝ)/2 ≤ Fintype.card J) :
    costEntropy a ≤ 64*costEntropy b := by
  have hupper := costEntropy_mono ha ha4
  rw [costEntropy_const] at hupper
  have hlower := costEntropy_mono (a := fun _ : J => c) (fun _ => hc) hb
  rw [costEntropy_const] at hlower
  exact comparable_entropy_trim_bound c (Fintype.card I) (Fintype.card J)
    (costEntropy a) (costEntropy b) hc (by exact_mod_cast hI) (by exact_mod_cast hJ)
    hhalf hupper hlower

theorem comparable_group_log_bound (n x : ℝ) (hn : 0 < n) (hx : 1 ≤ x)
    (hnx : n ≤ 4*x) : 1+log n ≤ 4*(1+log x) := by
  have hx0 : 0 < x := by linarith
  have hl := log_le_log hn hnx
  rw [log_mul (by norm_num : (4:ℝ) ≠ 0) hx0.ne'] at hl
  have hlog4 : log (4:ℝ) ≤ 2 := by
    have he : log (4:ℝ) = 2*log 2 := by
      have h := log_pow (2:ℝ) 2
      norm_num at h
      exact h
    rw [he]
    have h := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h
    linarith
  have hlx : 0 ≤ log x := log_nonneg hx
  linarith

end ThresholdHC.EntropyTailLower
