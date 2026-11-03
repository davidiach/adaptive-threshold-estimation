import ThresholdHC.EntropyTailQuantile.CostEntropy
import Mathlib

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.EntropyTailQuantile

theorem log_one_add_le_two_sqrt (x : ℝ) (hx : 0 ≤ x) : log (1+x) ≤ 2*sqrt x := by
  have hs := sq_sqrt hx
  have hle : 1+x ≤ (1+sqrt x)^2 := by nlinarith [sqrt_nonneg x]
  have hl := log_le_log (by linarith : 0 < 1+x) hle
  rw [log_pow] at hl
  have hr := log_le_sub_one_of_pos (show 0 < 1+sqrt x by positivity)
  norm_num at hl
  linarith

theorem mul_sqrt_ratio (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) :
    x*sqrt (y/x) = sqrt (x*y) := by
  rw [sqrt_div hy x,sqrt_mul hx.le y]
  have hs := sq_sqrt hx.le
  have hn : sqrt x ≠ 0 := (sqrt_pos.mpr hx).ne'
  field_simp
  nlinarith only [congrArg (fun z : ℝ => z*sqrt y) hs]

theorem binary_entropy_le_four_sqrt (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog x+negMulLog y-negMulLog (x+y) ≤ 4*sqrt (x*y) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rcases hy.eq_or_lt with rfl | hy
  · simp
  have hxy : x+y ≠ 0 := (add_pos hx hy).ne'
  have he : negMulLog x+negMulLog y-negMulLog (x+y) =
      x*log (1+y/x)+y*log (1+x/y) := by
    have he1 : 1+y/x = (x+y)/x := by field_simp
    have he2 : 1+x/y = (x+y)/y := by field_simp; ring
    rw [he1,he2,log_div hxy hx.ne',log_div hxy hy.ne']
    unfold negMulLog
    ring
  have h1 := mul_le_mul_of_nonneg_left (log_one_add_le_two_sqrt (y/x) (div_nonneg hy.le hx.le)) hx.le
  have h2 := mul_le_mul_of_nonneg_left (log_one_add_le_two_sqrt (x/y) (div_nonneg hx.le hy.le)) hy.le
  have hxy1 := mul_sqrt_ratio x y hx hy.le
  have hxy2 := mul_sqrt_ratio y x hy hx.le
  rw [mul_comm y x] at hxy2
  rw [he]
  nlinarith only [h1,h2,hxy1,hxy2]

theorem costEntropy_add_sqrt_cross {I : Type} [Fintype I] (a b : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    costEntropy (fun i => a i+b i) ≤ costEntropy a+costEntropy b+
      4*sqrt (costTotal a*costTotal b) := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => negMulLog_add_le (ha i) (hb i))
  have hcross := binary_entropy_le_four_sqrt (costTotal a) (costTotal b)
    (costTotal_nonneg ha) (costTotal_nonneg hb)
  simp only [Finset.sum_add_distrib] at hs
  simp only [costEntropy,costTotal_add]
  linarith

theorem sqrt_costEntropy_add {I : Type} [Fintype I] (a b : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    sqrt (costEntropy (fun i => a i+b i)) ≤ sqrt (costEntropy a)+2*sqrt (costEntropy b) := by
  have hA := costEntropy_nonneg ha
  have hB := costEntropy_nonneg hb
  have hAB := costEntropy_nonneg (fun i => add_nonneg (ha i) (hb i))
  have hcross : sqrt (costTotal a*costTotal b) ≤ sqrt (costEntropy a*costEntropy b) :=
    sqrt_le_sqrt (mul_le_mul (costTotal_le_costEntropy ha) (costTotal_le_costEntropy hb)
      (costTotal_nonneg hb) hA)
  have hl := costEntropy_add_sqrt_cross a b ha hb
  rw [sqrt_mul hA] at hcross
  have hs : (sqrt (costEntropy (fun i => a i+b i)))^2 ≤
      (sqrt (costEntropy a)+2*sqrt (costEntropy b))^2 := by
    rw [sq_sqrt hAB]
    nlinarith only [hl,hcross,sq_sqrt hA,sq_sqrt hB]
  exact (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp hs

theorem binary_entropy_lower_right (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    y*log ((x+y)/y) ≤ negMulLog x+negMulLog y-negMulLog (x+y) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [hy.ne']
  have hxy : x+y ≠ 0 := (add_pos hx hy).ne'
  have hlog : 0 ≤ log ((x+y)/x) := log_nonneg ((le_div_iff₀ hx).mpr (by linarith))
  have hp := mul_nonneg hx.le hlog
  rw [log_div hxy hx.ne'] at hp
  rw [log_div hxy hy.ne']
  unfold negMulLog
  nlinarith only [hp]

end ThresholdHC.EntropyTailLower
