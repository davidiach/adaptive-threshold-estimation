import ThresholdHC.EntropyTailQuantile.MeasureEntropy

/-! Dyadic partition geometry and the geometric reference probabilities. -/

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators ENNReal

namespace ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6

theorem bandEdge_succ (j : ℕ) : bandEdge (j+1) = bandEdge j / 2 := by
  simp [bandEdge, pow_succ, div_eq_mul_inv]

theorem bands_disjoint : Pairwise (fun i j => Disjoint (band i) (band j)) := by
  intro i j hij
  have hlt (i j : ℕ) (h : i < j) : Disjoint (band i) (band j) := by
    apply Set.disjoint_left.mpr
    intro d hi hj
    have hbj : bandEdge j ≤ bandEdge i / 2 := by
      rw [← bandEdge_succ]
      exact bandEdge_antitone h
    exact (not_lt_of_ge (hj.2.trans hbj)) hi.1
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact (hlt j i h).symm

theorem exists_band_cutoff {t : ℝ} (ht : 0 < t) :
    ∃ N : ℕ, bandEdge N < t ∧ ∀ j < N, t ≤ bandEdge j := by
  have hex : ∃ N : ℕ, bandEdge N < t := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (2:ℝ)⁻¹ < 1)
    exact ⟨N, (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.le_succ N)).trans_lt hN⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro j hj
  exact le_of_not_gt (Nat.find_min hex hj)

theorem dyadic_reference_sum (t : ℝ) (n : ℕ) :
    ∑ i : Fin n, t * (2:ℝ) ^ (i:ℕ) = t * ((2:ℝ)^n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, ih, pow_succ]
    ring

theorem dyadic_reference_sum_le_one {t : ℝ} (ht : 0 ≤ t) {n : ℕ}
    (hn : ∀ j < n, t ≤ bandEdge j) : ∑ i : Fin n, t * (2:ℝ)^ (i:ℕ) ≤ 1 := by
  rw [dyadic_reference_sum]
  cases n with
  | zero => simp
  | succ n =>
    have h := mul_le_mul_of_nonneg_right (hn n (Nat.lt_succ_self n))
      (by positivity : (0:ℝ) ≤ 2^(n+1))
    have he : bandEdge n * (2:ℝ)^(n+1) = 1 := by
      rw [bandEdge, inv_pow, inv_mul_cancel₀ (by positivity)]
    rw [he] at h
    nlinarith

theorem dyadic_reference_coefficient {t : ℝ} (ht : 0 < t) (j : ℕ) (d : Gap)
    (hd : d ∈ band j) : 1 - log (t * (2:ℝ)^j) ≤ (4/t) * (d:ℝ) := by
  have hp : 0 < t * (2:ℝ)^j := by positivity
  have hlog := log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [log_inv] at hlog
  have hg : (t * (2:ℝ)^j)⁻¹ ≤ (4/t) * (d:ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).2
    have hb : bandEdge j / 2 * (2:ℝ)^j = 1/4 := by
      simp only [bandEdge, pow_succ, inv_pow]
      field_simp
      norm_num
    have h := mul_lt_mul_of_pos_right hd.1 (by positivity : (0:ℝ) < 2^j)
    rw [hb] at h
    have he : (4/t) * (d:ℝ) * (t * (2:ℝ)^j) = 4 * ((d:ℝ) * (2:ℝ)^j) := by
      field_simp
    rw [he]
    linarith
  linarith

end ThresholdHC.EntropyTailQuantile
