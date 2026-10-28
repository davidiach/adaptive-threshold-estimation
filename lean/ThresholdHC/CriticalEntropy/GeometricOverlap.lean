import Mathlib

/-! Counting windows at geometrically separated scales. -/

noncomputable section
open Real

namespace ThresholdHC.CriticalEntropy

theorem geometric_separation_of_adjacent {K : ℕ} (t : Fin K → ℝ)
    (hstep : ∀ i j, j.val = i.val+1 → 4*t i ≤ t j) :
    ∀ i j, i ≤ j → (4 : ℝ)^(j.val-i.val)*t i ≤ t j := by
  intro i j hij
  have aux : ∀ m : ℕ, ∀ k : Fin K, k.val = i.val+m → (4 : ℝ)^m*t i ≤ t k := by
    intro m
    induction m with
    | zero =>
      intro k hk
      have he : k = i := Fin.ext (by simpa using hk)
      simp [he]
    | succ m ih =>
      intro k hk
      let l : Fin K := ⟨i.val+m, by omega⟩
      have h1 := ih l rfl
      have h2 := hstep l k (by dsimp [l]; omega)
      rw [pow_succ]
      nlinarith
  exact aux (j.val-i.val) j (by have h : i.val ≤ j.val := hij; omega)

/-- At least half of a finite nonnegative cost list is at most twice its
arithmetic mean. The zero-mean case is handled without division. -/
theorem half_low_cost {K : ℕ} (cost : Fin K → ℝ) (hc : ∀ i, 0 ≤ cost i)
    (c : ℝ) (hc0 : 0 ≤ c) (hmean : ∑ i, cost i = (K : ℝ)*c) :
    ∃ G : Finset (Fin K), (K : ℝ)/2 ≤ G.card ∧ ∀ i ∈ G, cost i ≤ 2*c := by
  classical
  let G := Finset.univ.filter (fun i => cost i ≤ 2*c)
  let H := Finset.univ.filter (fun i => ¬ cost i ≤ 2*c)
  refine ⟨G, ?_, fun i hi => (Finset.mem_filter.mp hi).2⟩
  have hcard : G.card + H.card = K := by
    simpa only [G, H, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin K => cost i ≤ 2*c)
  by_cases hz : c = 0
  · have hsum : ∑ i, cost i = 0 := by simpa [hz] using hmean
    have hi : ∀ i : Fin K, cost i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hc j)).mp hsum i (Finset.mem_univ i)
    have hG : G = Finset.univ := by ext i; simp [G, hi, hz]
    simp only [hG, Finset.card_univ, Fintype.card_fin]
    linarith [show (0 : ℝ) ≤ K from Nat.cast_nonneg K]
  · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hz)
    have hsumH : (H.card : ℝ)*(2*c) ≤ ∑ i ∈ H, cost i := by
      calc
        _ = ∑ _i ∈ H, (2*c) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i hi => (lt_of_not_ge (Finset.mem_filter.mp hi).2).le)
    have hsub : ∑ i ∈ H, cost i ≤ ∑ i, cost i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => hc i)
    have hcardreal : (G.card : ℝ)+(H.card : ℝ)=K := by exact_mod_cast hcard
    rw [hmean] at hsub
    nlinarith

/-- A finite family of intervals with scales increasing by at least four
has logarithmically bounded overlap. The estimate applies to arbitrary
subsets of indices, not just contiguous blocks. -/
theorem geometric_interval_card {K : ℕ} (s : Finset (Fin K)) (t : Fin K → ℝ)
    (ht : ∀ i, 0 < t i)
    (hsep : ∀ i j, i ≤ j → (4 : ℝ)^(j.val-i.val)*t i ≤ t j)
    (L U x : ℝ) (hL : 0 < L) (hLU : L ≤ U)
    (hwindow : ∀ i ∈ s, L*t i ≤ x ∧ x ≤ U*t i) :
    (s.card : ℝ) ≤ 1 + log (U/L)/log 4 := by
  classical
  have hlog4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
  have hratio : 1 ≤ U/L := (one_le_div hL).mpr hLU
  have hlogratio : 0 ≤ log (U/L) := log_nonneg hratio
  by_cases hs : s.Nonempty
  · let i := s.min' hs
    let j := s.max' hs
    have hi : i ∈ s := s.min'_mem hs
    have hj : j ∈ s := s.max'_mem hs
    have hij : i ≤ j := s.min'_le j hj
    have hspan : s.card ≤ j.val+1-i.val := by
      have hsub : s ⊆ Finset.Icc i j := by
        intro k hk
        exact Finset.mem_Icc.mpr ⟨s.min'_le k hk, s.le_max' k hk⟩
      simpa only [Fin.card_Icc] using Finset.card_le_card hsub
    have hpower : (4 : ℝ)^(j.val-i.val) ≤ U/L := by
      apply (le_div_iff₀ hL).mpr
      have hprod := mul_le_mul_of_nonneg_left (hsep i j hij) hL.le
      have hbounds := le_trans (hwindow j hj).1 (hwindow i hi).2
      have hmul : ((4 : ℝ)^(j.val-i.val)*L)*t i ≤ U*t i := by
        nlinarith
      exact (mul_le_mul_iff_left₀ (ht i)).mp hmul
    have hlog := log_le_log (pow_pos (by norm_num : (0 : ℝ) < 4) _) hpower
    rw [log_pow] at hlog
    have hdiff : (j.val-i.val : ℕ)+1 = j.val+1-i.val := by
      have hij' : i.val ≤ j.val := hij
      omega
    have hcard : (s.card : ℝ) ≤ (j.val-i.val : ℕ)+1 := by
      exact_mod_cast (hdiff.symm ▸ hspan)
    have hdiv : ((j.val-i.val : ℕ) : ℝ) ≤ log (U/L)/log 4 :=
      (le_div_iff₀ hlog4).mpr hlog
    linarith
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [he, Finset.card_empty, Nat.cast_zero]
    positivity

end ThresholdHC.CriticalEntropy
