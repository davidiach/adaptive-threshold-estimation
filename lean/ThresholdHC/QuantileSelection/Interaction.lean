import ThresholdHC.QuantileSelection.BinaryEntropy
import ThresholdHC.QuantileSelection.Specification
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSelection
open ThresholdHC.EntropyTailQuantile

theorem binary_interaction {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    negMulLog A + negMulLog B - negMulLog (A+B) ≤ 2 * log 2 * sqrt (A*B) := by
  rcases hA.eq_or_lt with rfl | hA
  · simp
  let s := A+B
  let p := A/s
  have hs : 0 < s := add_pos_of_pos_of_nonneg hA hB
  have hp : 0 ≤ p := div_nonneg hA.le hs.le
  have hq : 1-p = B/s := by dsimp [p, s]; field_simp; ring
  have hq0 : 0 ≤ 1-p := hq ▸ div_nonneg hB hs.le
  have ha : s*p = A := by dsimp [p]; field_simp
  have hb : s*(1-p) = B := by rw [hq]; field_simp
  have he : s*binEntropy p = negMulLog A + negMulLog B - negMulLog s := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, ← ha, ← hb, negMulLog_mul, negMulLog_mul]
    ring
  have hr : s*sqrt (p*(1-p)) = sqrt (A*B) := by
    rw [← sqrt_sq hs.le, ← sqrt_mul (sq_nonneg s)]
    congr 1
    rw [← ha, ← hb]
    ring
  have h := mul_le_mul_of_nonneg_left (binEntropy_le_geometric hp (by linarith)) hs.le
  rw [he, mul_left_comm s, hr] at h
  exact h

/-- Lemma 1, retaining the sharp binary interaction coefficient before relaxing it. -/
theorem entropy_interaction : InteractionStatement := by
  intro ι _ a b ha hb
  constructor
  · have hc := Finset.sum_le_sum (s := Finset.univ) (fun i _ => negMulLog_add_le (ha i) (hb i))
    rw [Finset.sum_add_distrib] at hc
    have h := binary_interaction (costTotal_nonneg ha) (costTotal_nonneg hb)
    unfold costEntropy
    rw [costTotal_add]
    linarith only [hc, h]
  · apply add_le_add_right
    have hlog : 2 * log 2 ≤ sqrt 2 := by
      have h : (7/5 : ℝ) ≤ sqrt 2 := le_sqrt_of_sq_le (by norm_num)
      linarith only [h, log_two_lt_d9]
    calc
      _ ≤ sqrt 2 * sqrt (costTotal a * costTotal b) :=
        mul_le_mul_of_nonneg_right hlog (sqrt_nonneg _)
      _ ≤ sqrt 2 * sqrt (costEntropy a * costEntropy b) :=
        mul_le_mul_of_nonneg_left (sqrt_le_sqrt (mul_le_mul (costTotal_le_costEntropy ha)
          (costTotal_le_costEntropy hb) (costTotal_nonneg hb) (costEntropy_nonneg ha))) (sqrt_nonneg _)
      _ = _ := by rw [← sqrt_mul (by norm_num : (0:ℝ) ≤ 2), mul_assoc]

end ThresholdHC.QuantileSelection
