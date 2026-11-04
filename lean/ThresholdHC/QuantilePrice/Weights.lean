import ThresholdHC.QuantileSelection.SeparatedCost

noncomputable section
open MeasureTheory Real Set
open scoped BigOperators ENNReal
namespace ThresholdHC.QuantilePrice
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

/-- A rational reference distribution indexed from the band containing the cutoff. -/
def weight : ℕ → ℝ
  | 0 | 1 => 4595/10000
  | 2 => 778/10000
  | k+3 => 24/10000*(1/10)^k

theorem weight_pos (n : ℕ) : 0 < weight n := by
  rcases n with _ | _ | _ | k <;> dsimp [weight] <;> positivity

theorem weight_mass (N : ℕ) : ∑ i : Fin N, weight i.val ≤ 1 := by
  have tail (k : ℕ) : ∑ i : Fin (k+3), weight i.val =
      2*(4595/10000)+778/10000+(24/10000)*(1-(1/10)^k)/(1-1/10) := by
    induction k with
    | zero => norm_num [Fin.sum_univ_succ,weight]
    | succ k ih =>
      change (∑ i : Fin ((k+3)+1), weight i.val) = _
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      rw [ih]
      change _ + 24/10000*(1/10)^k = _
      rw [pow_succ]
      ring
  rcases N with _ | _ | _ | k
  · simp
  · norm_num [Fin.sum_univ_succ,weight]
  · norm_num [Fin.sum_univ_succ,weight]
  · rw [tail]
    have h : (0:ℝ) ≤ (1/10)^k := by positivity
    ring_nf at h ⊢
    linarith

private theorem log_weight_bound {w c : ℝ} (hw : 0 < w) (h : 1/w ≤ exp (c-1)) :
    1 - log w ≤ c := by
  have hlog := (log_le_iff_le_exp (by positivity : 0 < 1/w)).mpr h
  rw [one_div,log_inv] at hlog
  linarith

theorem weight_coefficient (n : ℕ) : 1 - log (weight n) ≤ (16/9)*max 1 ((2:ℝ)^n/2) := by
  have h0 : 1-log (4595/10000 : ℝ) ≤ 16/9 := by
    apply log_weight_bound (by norm_num)
    apply le_trans _ (sum_le_exp_of_nonneg (by norm_num) 6)
    norm_num [Finset.sum_range_succ,Nat.factorial_succ]
  have h2 : 1-log (778/10000 : ℝ) ≤ 32/9 := by
    apply log_weight_bound (by norm_num)
    apply le_trans _ (sum_le_exp_of_nonneg (by norm_num) 9)
    norm_num [Finset.sum_range_succ,Nat.factorial_succ]
  have h3 : 1-log (24/10000 : ℝ) ≤ 64/9 := by
    apply log_weight_bound (by norm_num)
    apply le_trans _ (sum_le_exp_of_nonneg (by norm_num) 11)
    norm_num [Finset.sum_range_succ,Nat.factorial_succ]
  have h10 : log 10 ≤ 3 := by
    apply (log_le_iff_le_exp (by norm_num)).mpr
    apply le_trans _ (sum_le_exp_of_nonneg (by norm_num) 5)
    norm_num [Finset.sum_range_succ,Nat.factorial_succ]
  rcases n with _ | _ | _ | k
  · norm_num [weight] at h0 ⊢; linarith
  · norm_num [weight] at h0 ⊢; linarith
  · norm_num [weight] at h2 ⊢; linarith
  · have growth (j : ℕ) : 64/9+3*(j:ℝ) ≤ (16/9)*(2:ℝ)^(j+2) := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show j+1+2=(j+2)+1 by omega,pow_succ,Nat.cast_succ]
        linarith [Nat.cast_nonneg (α := ℝ) j]
    calc
      _ = 1-log (24/10000 : ℝ)+(k:ℝ)*log 10 := by
        change 1-log ((24/10000:ℝ)*(1/10)^k) = _
        rw [log_mul (by norm_num) (pow_ne_zero k (by norm_num)), log_pow,
          show (1/10:ℝ)=(10:ℝ)⁻¹ by norm_num,log_inv]
        ring
      _ ≤ 64/9+3*(k:ℝ) := by linarith [mul_le_mul_of_nonneg_left h10 (Nat.cast_nonneg k)]
      _ ≤ _ := (growth k).trans (by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply le_trans _ (le_max_right _ _)
        rw [show k+3=(k+2)+1 by omega,pow_succ]
        ring_nf
        exact le_rfl)

theorem weight_band {N : ℕ} {t : ℝ} (ht : 0 < t) (hbefore : ∀ j < N, t ≤ bandEdge j)
    (j : Fin N) (d : Gap) (hd : d ∈ band j) (hs : t ≤ (d:ℝ)) :
    1-log (weight j.rev.val) ≤ ((16/9)/t)*(d:ℝ) := by
  let r := j.rev.val
  have hlast : (j:ℕ)+r < N := by dsimp [r,Fin.rev]; omega
  have he : bandEdge ((j:ℕ)+r)*(2:ℝ)^r = bandEdge j := by
    rw [bandEdge,bandEdge,show (j:ℕ)+r+1 = ((j:ℕ)+1)+r by omega,pow_add,inv_pow]
    field_simp
    norm_num [← mul_pow]
  have hedge := mul_le_mul_of_nonneg_right (hbefore _ hlast) (show 0 ≤ (2:ℝ)^r by positivity)
  rw [he] at hedge
  calc
    _ ≤ (16/9)*max 1 ((2:ℝ)^r/2) := weight_coefficient r
    _ ≤ (16/9)*((d:ℝ)/t) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [max_le_iff]
      exact ⟨(le_div_iff₀ ht).2 (by linarith), (le_div_iff₀ ht).2 (by nlinarith [hd.1])⟩
    _ = _ := by ring

end ThresholdHC.QuantilePrice
