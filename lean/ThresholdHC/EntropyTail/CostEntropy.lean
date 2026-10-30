import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Homogeneous entropy of finite cost vectors

This is the deterministic cost functional used in the entropy--tail and
quantile formulas. It does not assert a statistical lower or upper bound.
Zero costs are allowed, including the identically zero vector.
-/

noncomputable section
open scoped BigOperators
open Real

namespace ThresholdHC.EntropyTail

variable {ι : Type*} [Fintype ι]

def costTotal (a : ι → ℝ) : ℝ := ∑ i, a i

/-- `A + ∑ aᵢ log(A/aᵢ)`, written continuously at zero costs. -/
def costEntropy (a : ι → ℝ) : ℝ :=
  costTotal a + ∑ i, negMulLog (a i) - negMulLog (costTotal a)

theorem costTotal_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    0 ≤ costTotal a := Finset.sum_nonneg (fun i _ => ha i)

theorem le_costTotal {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (i : ι) :
    a i ≤ costTotal a := Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)

@[simp] theorem costTotal_zero : costTotal (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [costTotal]

@[simp] theorem costEntropy_zero : costEntropy (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [costEntropy]

theorem costTotal_add (a b : ι → ℝ) :
    costTotal (fun i => a i + b i) = costTotal a + costTotal b := by
  simp [costTotal, Finset.sum_add_distrib]

theorem costTotal_smul (c : ℝ) (a : ι → ℝ) :
    costTotal (fun i => c * a i) = c * costTotal a := by
  simp [costTotal, Finset.mul_sum]

theorem costEntropy_smul (c : ℝ) (a : ι → ℝ) :
    costEntropy (fun i => c * a i) = c * costEntropy a := by
  simp only [costEntropy, costTotal_smul, negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  unfold costTotal
  ring

theorem costEntropy_eq_log_sum {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    costEntropy a = costTotal a + ∑ i, a i * log (costTotal a / a i) := by
  have ht := costTotal_nonneg ha
  rcases ht.eq_or_lt with hzero | hpos
  · have hz : a = fun _ => 0 := by
      funext i
      exact le_antisymm (by simpa [← hzero] using le_costTotal ha i) (ha i)
    simp [hz]
  · have hi (i : ι) :
        a i * log (costTotal a / a i) = a i * log (costTotal a) + negMulLog (a i) := by
      by_cases hz : a i = 0
      · simp [hz]
      · rw [log_div hpos.ne' hz]
        simp only [negMulLog]
        ring
    simp only [hi, Finset.sum_add_distrib, ← Finset.sum_mul, costEntropy, negMulLog]
    unfold costTotal
    ring

theorem costTotal_le_costEntropy {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    costTotal a ≤ costEntropy a := by
  rw [costEntropy_eq_log_sum ha]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro i _
  by_cases hz : a i = 0
  · simp [hz]
  · exact mul_nonneg (ha i) (log_nonneg ((le_div_iff₀ (lt_of_le_of_ne (ha i) (Ne.symm hz))).2
      (by simpa using le_costTotal ha i)))

theorem costEntropy_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    0 ≤ costEntropy a := (costTotal_nonneg ha).trans (costTotal_le_costEntropy ha)

theorem eq_zero_of_costTotal_eq_zero {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hz : costTotal a = 0) : a = fun _ => 0 := by
  funext i
  exact le_antisymm (by simpa [hz] using le_costTotal ha i) (ha i)

theorem costEntropy_normalized {a : ι → ℝ} (hA : 0 < costTotal a) :
    costEntropy a = costTotal a * (1 + ∑ i, negMulLog (a i / costTotal a)) := by
  have h := costEntropy_smul (costTotal a)⁻¹ a
  have ht : costTotal (fun i => (costTotal a)⁻¹ * a i) = 1 := by
    rw [costTotal_smul, inv_mul_cancel₀ hA.ne']
  unfold costEntropy at h
  rw [ht, negMulLog_one, sub_zero] at h
  have hs : (∑ i, negMulLog ((costTotal a)⁻¹ * a i)) =
      ∑ i, negMulLog (a i / costTotal a) := by
    congr 1
    funext i
    rw [div_eq_mul_inv, mul_comm]
  rw [hs] at h
  have hm := congrArg (fun x => costTotal a * x) h
  simpa only [costEntropy, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] using hm.symm

/-- Concavity of `-x log x` in homogeneous (perspective) form. -/
theorem homogeneous_negMulLog_add {a b A B : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 < A) (hB : 0 < B) :
    A * negMulLog (a / A) + B * negMulLog (b / B) ≤
      (A+B) * negMulLog ((a+b)/(A+B)) := by
  have hAB : 0 < A+B := add_pos hA hB
  have hw : A/(A+B) + B/(A+B) = 1 := by
    rw [← add_div, div_self hAB.ne']
  have h := concaveOn_negMulLog.2 (div_nonneg ha hA.le) (div_nonneg hb hB.le)
    (div_nonneg hA.le hAB.le) (div_nonneg hB.le hAB.le) hw
  simp only [smul_eq_mul] at h
  have hx : A/(A+B)*(a/A) + B/(A+B)*(b/B) = (a+b)/(A+B) := by
    field_simp
  rw [hx] at h
  have hm := mul_le_mul_of_nonneg_left h hAB.le
  have hleft : (A+B) * (A/(A+B)*negMulLog (a/A) + B/(A+B)*negMulLog (b/B)) =
      A*negMulLog (a/A) + B*negMulLog (b/B) := by
    field_simp
  rwa [hleft] at hm

theorem costEntropy_superadditive {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    costEntropy a + costEntropy b ≤ costEntropy (fun i => a i + b i) := by
  rcases (costTotal_nonneg ha).eq_or_lt with hz | hA
  · have ha0 := eq_zero_of_costTotal_eq_zero ha hz.symm
    simp [ha0]
  rcases (costTotal_nonneg hb).eq_or_lt with hz | hB
  · have hb0 := eq_zero_of_costTotal_eq_zero hb hz.symm
    simp [hb0]
  have ht : 0 < costTotal (fun i => a i + b i) := by
    rw [costTotal_add]
    exact add_pos hA hB
  rw [costEntropy_normalized hA, costEntropy_normalized hB, costEntropy_normalized ht,
    costTotal_add]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    homogeneous_negMulLog_add (ha i) (hb i) hA hB)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  nlinarith only [hs]

theorem costEntropy_mono {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ i, a i ≤ b i) : costEntropy a ≤ costEntropy b := by
  have hd : ∀ i, 0 ≤ b i - a i := fun i => sub_nonneg.mpr (hab i)
  have hs := costEntropy_superadditive ha hd
  have he : (fun i => a i + (b i - a i)) = b := by funext i; ring
  rw [he] at hs
  exact (le_add_of_nonneg_right (costEntropy_nonneg hd)).trans hs

theorem negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog (x+y) ≤ negMulLog x + negMulLog y := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rcases hy.eq_or_lt with rfl | hy
  · simp
  have hxlog := mul_le_mul_of_nonneg_left (log_le_log hx (le_add_of_nonneg_right hy.le)) hx.le
  have hylog := mul_le_mul_of_nonneg_left (log_le_log hy (le_add_of_nonneg_left hx.le)) hy.le
  unfold negMulLog
  nlinarith only [hxlog, hylog]

theorem binary_entropy_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog x + negMulLog y - negMulLog (x+y) ≤ (x+y)*log 2 := by
  have h := concaveOn_negMulLog.2 hx hy (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul] at h
  have he : (1/2:ℝ)*x + (1/2:ℝ)*y = (1/2:ℝ)*(x+y) := by ring
  rw [he, negMulLog_mul] at h
  have hh : negMulLog (1/2:ℝ) = (1/2:ℝ)*log 2 := by
    simp [negMulLog]
  rw [hh] at h
  nlinarith only [h]

theorem costEntropy_add_le {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    costEntropy (fun i => a i + b i) ≤
      (1+log 2)*(costEntropy a + costEntropy b) := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => negMulLog_add_le (ha i) (hb i))
  simp only [Finset.sum_add_distrib] at hs
  have hm := binary_entropy_le (costTotal_nonneg ha) (costTotal_nonneg hb)
  have hbase := add_le_add (costTotal_le_costEntropy ha) (costTotal_le_costEntropy hb)
  have hlog : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hscale := mul_le_mul_of_nonneg_right hbase hlog
  simp only [costEntropy, costTotal_add] at *
  nlinarith only [hs, hm, hscale]

theorem costEntropy_add_le_two {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    costEntropy (fun i => a i + b i) ≤ 2*costEntropy a + 2*costEntropy b := by
  have hlog : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hsum := add_nonneg (costEntropy_nonneg ha) (costEntropy_nonneg hb)
  have h := mul_le_mul_of_nonneg_right hlog hsum
  nlinarith only [costEntropy_add_le ha hb, h]

/-- Cross-entropy bound against a positive reference vector of total mass at
most one. This also covers finite truncations of a countable reference law. -/
theorem costEntropy_le_reference {a p : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hp : ∀ i, 0 < p i) (hpsum : (∑ i, p i) ≤ 1) :
    costEntropy a ≤ ∑ i, a i * (1-log (p i)) := by
  rcases (costTotal_nonneg ha).eq_or_lt with hz | hA
  · have ha0 := eq_zero_of_costTotal_eq_zero ha hz.symm
    simp [ha0]
  have hi (i : ι) : a i * log (costTotal a / a i) + a i * log (p i) ≤
      costTotal a * p i - a i := by
    rcases (ha i).eq_or_lt with hz | hai
    · rw [← hz]
      simp only [zero_mul, add_zero, sub_zero]
      exact mul_nonneg hA.le (hp i).le
    have hlog := log_le_sub_one_of_pos (div_pos (mul_pos hA (hp i)) hai)
    have hm := mul_le_mul_of_nonneg_left hlog hai.le
    have harg : costTotal a * p i / a i = (costTotal a / a i)*p i := by ring
    rw [harg, log_mul (div_pos hA hai).ne' (hp i).ne'] at hm
    have hc : a i * (costTotal a * p i / a i) = costTotal a * p i := by
      field_simp
    have hc' : a i * (costTotal a / a i * p i) = costTotal a * p i := by
      field_simp
    nlinarith only [hm, hc']
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hmass := mul_le_mul_of_nonneg_left hpsum hA.le
  rw [costEntropy_eq_log_sum ha]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  unfold costTotal at *
  nlinarith only [hs, hmass]

theorem continuous_costEntropy : Continuous (costEntropy : (ι → ℝ) → ℝ) := by
  unfold costEntropy costTotal
  fun_prop

end ThresholdHC.EntropyTail
