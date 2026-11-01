import Mathlib

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.EntropyTailLower

def upperMass {n : ℕ} (v : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ i, if k < i then v i else 0

theorem upperMass_nonneg {n : ℕ} (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (k : Fin n) :
    0 ≤ upperMass v k := Finset.sum_nonneg (fun i _ => by split_ifs; exact hv i; exact le_rfl)

theorem upperMass_last {n : ℕ} (v : Fin (n+1) → ℝ) : upperMass v (Fin.last n) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (not_lt.mpr (Fin.le_last i))

theorem upperMass_castSucc {n : ℕ} (v : Fin (n+1) → ℝ) (k : Fin n) :
    upperMass v k.castSucc = upperMass (fun i => v i.castSucc) k + v (Fin.last n) := by
  unfold upperMass
  rw [Fin.sum_univ_castSucc]
  simp

theorem exists_upper_mass_cut {n : ℕ} (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (s : ℝ) (hs : 0 < s) (htotal : s ≤ ∑ i, v i) :
    ∃ k : Fin n, upperMass v k ≤ s ∧ s ≤ upperMass v k+v k := by
  induction n generalizing s with
  | zero => simp at htotal; linarith
  | succ n ih =>
    by_cases hh : s ≤ v (Fin.last n)
    · exact ⟨Fin.last n,by rw [upperMass_last]; exact hs.le,by simpa [upperMass_last] using hh⟩
    · have hs' : 0 < s-v (Fin.last n) := by linarith
      have hsum : s-v (Fin.last n) ≤ ∑ i : Fin n, v i.castSucc := by
        rw [Fin.sum_univ_castSucc] at htotal
        linarith
      obtain ⟨k,hk1,hk2⟩ := ih (fun i => v i.castSucc) (fun i => hv i.castSucc) (s-v (Fin.last n)) hs' hsum
      refine ⟨k.castSucc,?_,?_⟩ <;> rw [upperMass_castSucc] <;> linarith

theorem exists_fractional_upper_cut {n : ℕ} (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (s : ℝ) (hs : 0 < s) (htotal : s ≤ ∑ i, v i) :
    ∃ (k : Fin n) (c : ℝ), 0 ≤ c ∧ c ≤ 1 ∧ upperMass v k + c*v k = s := by
  obtain ⟨k,hk1,hk2⟩ := exists_upper_mass_cut v hv s hs htotal
  by_cases hz : v k = 0
  · exact ⟨k,0,le_rfl,by norm_num,by simp [hz] at hk2 ⊢; linarith⟩
  · have hkpos : 0 < v k := lt_of_le_of_ne (hv k) (Ne.symm hz)
    refine ⟨k,(s-upperMass v k)/v k,div_nonneg (by linarith) (hv k),?_,?_⟩
    · exact (div_le_one hkpos).mpr (by linarith)
    · rw [div_mul_cancel₀ _ hz]
      ring

def upperCutPrior {n : ℕ} (k : Fin n) (c : ℝ) (i : Fin n) : ℝ :=
  if k < i then 1 else if i = k then c else 0

theorem upperCutPrior_bounds {n : ℕ} (k : Fin n) (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (i : Fin n) : 0 ≤ upperCutPrior k c i ∧ upperCutPrior k c i ≤ 1 := by
  unfold upperCutPrior
  split_ifs <;> simp_all

theorem weighted_upperCut_sum {n : ℕ} (v f : Fin n → ℝ) (k : Fin n) (c : ℝ) :
    (∑ i, v i*upperCutPrior k c i*f i) =
      (∑ i, if k < i then v i*f i else 0)+c*v k*f k := by
  have he (i) : v i*upperCutPrior k c i*f i =
      (if k < i then v i*f i else 0)+(if i = k then c*v i*f i else 0) := by
    by_cases hki : k < i
    · have hik : i ≠ k := ne_of_gt hki
      simp [upperCutPrior,hki,hik]
    · by_cases hik : i = k
      · subst i
        simp only [upperCutPrior,lt_self_iff_false,ite_false,ite_true,zero_add]
        ring
      · simp only [upperCutPrior,hki,hik,ite_false,mul_zero,zero_mul,add_zero]
  simp_rw [he]
  simp [Finset.sum_add_distrib]

theorem upperCut_mass {n : ℕ} (v : Fin n → ℝ) (k : Fin n) (c : ℝ) :
    (∑ i, v i*upperCutPrior k c i) = upperMass v k+c*v k := by
  simpa [upperMass] using weighted_upperCut_sum v (fun _ => 1) k c

theorem sum_dyadic_powers (n : ℕ) :
    (∑ i : Fin n, (2:ℝ)^(i.val+1)) = 2^(n+1)-2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih]
    simp only [pow_succ]
    ring

theorem lower_dyadic_sum {n : ℕ} (k : Fin n) :
    (∑ i : Fin n, if i < k then (2:ℝ)^(i.val+1) else 0) = 2^(k.val+1)-2 := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) k
    · rw [Fin.sum_univ_castSucc]
      simpa using sum_dyadic_powers n
    · rw [Fin.sum_univ_castSucc]
      have hh : ¬Fin.last n < j.castSucc := not_lt.mpr (Fin.le_last _)
      simpa [hh] using ih j

theorem weighted_order_partition {n : ℕ} (v f : Fin n → ℝ) (k : Fin n) :
    (∑ i, v i*f i) = (∑ i, if k < i then v i*f i else 0)+
      (∑ i, if i < k then v i*f i else 0)+v k*f k := by
  have he (i) : v i*f i = (if k < i then v i*f i else 0)+
      (if i < k then v i*f i else 0)+(if i = k then v i*f i else 0) := by
    rcases lt_trichotomy i k with h | h | h
    · simp [h,not_lt.mpr h.le,ne_of_lt h]
    · subst i; simp
    · simp [h,not_lt.mpr h.le,ne_of_gt h]
  calc
    _ = ∑ i, ((if k < i then v i*f i else 0)+
        (if i < k then v i*f i else 0)+(if i = k then v i*f i else 0)) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = _ := by simp [Finset.sum_add_distrib]

theorem dyadic_top_mass {n : ℕ} (v : Fin n → ℝ) (s : ℝ)
    (hv : ∀ i, 0 ≤ v i) (hs : 0 < s) (hcap : ∀ i, v i ≤ s) :
    ∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i ∧ q i ≤ 1) ∧
      (∑ i, v i*q i) ≤ s ∧
      (∑ i, v i*(2:ℝ)^(i.val+1)) ≤ 2*∑ i, v i*q i*(2:ℝ)^(i.val+1) := by
  let f : Fin n → ℝ := fun i => (2:ℝ)^(i.val+1)
  have hf (i) : 0 ≤ f i := by dsimp [f]; positivity
  by_cases htotal : (∑ i, v i) ≤ s
  · refine ⟨fun _ => 1,fun _ => by norm_num,by simpa using htotal,?_⟩
    simp only [mul_one]
    have hn : 0 ≤ ∑ i, v i*f i := Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hf i))
    change (∑ i, v i*f i) ≤ 2*∑ i, v i*f i
    linarith
  · obtain ⟨k,c,hc,hc1,hcut⟩ := exists_fractional_upper_cut v hv s hs (le_of_not_ge htotal)
    let U := ∑ i, if k < i then v i*f i else 0
    let L := ∑ i, if i < k then v i*f i else 0
    have hL : L ≤ s*f k := by
      calc
        _ ≤ ∑ i, if i < k then s*f i else 0 := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs
          · exact mul_le_mul_of_nonneg_right (hcap i) (hf i)
          · exact le_rfl
        _ = s*∑ i, if i < k then f i else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> ring
        _ = s*(f k-2) := by rw [lower_dyadic_sum]
        _ ≤ s*f k := by nlinarith
    have hU : 2*f k*upperMass v k ≤ U := by
      unfold upperMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      by_cases hki : k < i
      · simp only [hki,ite_true]
        have hp : 2*f k ≤ f i := by
          calc
            _ = (2:ℝ)^((k.val+1)+1) := by dsimp [f]; rw [pow_succ]; ring
            _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by have hh : k.val < i.val := hki; omega)
        nlinarith [mul_nonneg (hv i) (sub_nonneg.mpr hp)]
      · simp [hki]
    have hvk := mul_le_mul_of_nonneg_right (hcap k) (hf k)
    have hcutw := congrArg (fun x : ℝ => 2*x*f k) hcut
    refine ⟨upperCutPrior k c,upperCutPrior_bounds k c hc hc1,?_,?_⟩
    · rw [upperCut_mass,hcut]
    · rw [weighted_upperCut_sum,weighted_order_partition v (fun i => (2:ℝ)^(i.val+1)) k]
      change U+L+v k*f k ≤ 2*(U+c*v k*f k)
      nlinarith only [hL,hU,hvk,hcutw]

end ThresholdHC.EntropyTailLower
