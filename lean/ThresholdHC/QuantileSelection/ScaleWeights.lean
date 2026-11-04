import ThresholdHC.EntropyTailQuantile.BandGeometry
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSelection
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

/-- Reference probabilities indexed outward from the band containing the threshold. -/
def scaleWeight : ℕ → ℝ
  | 0 | 1 => 3/8
  | k+2 => ((2:ℝ)^(k+3))⁻¹

theorem scaleWeight_pos (k : ℕ) : 0 < scaleWeight k := by
  rcases k with _ | _ | k <;> dsimp [scaleWeight] <;> positivity

theorem scaleWeight_mass (N : ℕ) : ∑ j : Fin N, scaleWeight j.val ≤ 1 := by
  have sum_tail (n : ℕ) : ∑ j : Fin (n+2), scaleWeight j.val = 1 - ((2:ℝ)^(n+2))⁻¹ := by
    induction n with
    | zero =>
      change (∑ j : Fin 2, scaleWeight j.val) = _
      rw [Fin.sum_univ_two]
      norm_num [scaleWeight]
    | succ n ih =>
      change (∑ j : Fin ((n+2)+1), scaleWeight j.val) = _
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      change 1 - ((2:ℝ)^(n+2))⁻¹ + (2^((n+2)+1))⁻¹ = 1 - (2^((n+2)+1))⁻¹
      rw [pow_succ, mul_inv_rev]
      ring
  rcases N with _ | _ | n
  · simp
  · norm_num [scaleWeight]
  · rw [sum_tail]; exact sub_le_self _ (by positivity)

theorem scaleWeight_coefficient (n : ℕ) :
    1 - log (scaleWeight n) ≤ max 2 ((2:ℝ)^n) := by
  have hfirst : 1 - log (3/8 : ℝ) ≤ 2 := by
    have h : log (8/3 : ℝ) ≤ 1 := (log_le_iff_le_exp (by norm_num)).2 (by linarith [exp_one_gt_d9])
    rw [show (3/8 : ℝ) = (8/3 : ℝ)⁻¹ by norm_num, log_inv]
    linarith
  rcases n with _ | _ | k
  · exact hfirst.trans (le_max_left ..)
  · exact hfirst.trans (le_max_left ..)
  apply le_trans _ (le_max_right ..)
  have hk : (k:ℝ)+4 ≤ (2:ℝ)^(k+2) := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [show k+1+2 = (k+2)+1 by omega, pow_succ, Nat.cast_succ]
      linarith [Nat.cast_nonneg (α := ℝ) k]
  simp only [scaleWeight, log_inv, log_pow, Nat.cast_add, Nat.cast_ofNat]
  have hl := mul_le_mul_of_nonneg_left (show log 2 ≤ 1 by linarith [log_two_lt_d9])
    (show (0:ℝ) ≤ k+3 by positivity)
  linarith

theorem scaleWeight_band {N : ℕ} {t : ℝ} (ht : 0 < t) (hbefore : ∀ j < N, t ≤ bandEdge j)
    (j : Fin N) (d : Gap) (hd : d ∈ band j) (hs : t ≤ (d:ℝ)) :
    1 - log (scaleWeight j.rev.val) ≤ (2/t) * (d:ℝ) := by
  let r := j.rev.val
  have hindex : (j:ℕ)+r+1 = N := by dsimp [r, Fin.rev]; omega
  have hlast : (j:ℕ)+r < N := by omega
  have he : bandEdge ((j:ℕ)+r) * (2:ℝ)^r = bandEdge j := by
    rw [bandEdge, bandEdge, show (j:ℕ)+r+1 = ((j:ℕ)+1)+r by omega, pow_add, inv_pow]
    field_simp
    norm_num [← mul_pow]
  have hedge := mul_le_mul_of_nonneg_right (hbefore _ hlast) (show 0 ≤ (2:ℝ)^r by positivity)
  rw [he] at hedge
  apply (scaleWeight_coefficient r).trans
  rw [div_mul_eq_mul_div, max_le_iff]
  exact ⟨(le_div_iff₀ ht).2 (by linarith), (le_div_iff₀ ht).2 (by linarith [hd.1])⟩

end ThresholdHC.QuantileSelection
