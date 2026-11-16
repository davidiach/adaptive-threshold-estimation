import ThresholdHC.EntropyTailQuantile.CostEntropy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

noncomputable section
open scoped BigOperators
namespace ThresholdHC.PowerWindow
open ThresholdHC.EntropyTailQuantile

variable {ι : Type*} [Fintype ι]

theorem finite_entropy_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    0 ≤ ∑ i, Real.negMulLog (p i) := by
  apply Finset.sum_nonneg
  intro i _
  apply Real.negMulLog_nonneg (hp i)
  have h := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  simpa only [hs] using h

/-- A uniform atom bound gives the lower entropy bound, including zero atoms. -/
theorem finite_entropy_lower_bound {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) {r : ℝ} (hr : 0 < r) (hb : ∀ i, p i ≤ r) :
    -Real.log r ≤ ∑ i, Real.negMulLog (p i) := by
  have hpoint (i : ι) : p i * (-Real.log r) ≤ Real.negMulLog (p i) := by
    rcases (hp i).eq_or_lt with hz | hpos
    · simp [← hz]
    · have h := mul_le_mul_of_nonneg_left (Real.log_le_log hpos (hb i)) (hp i)
      unfold Real.negMulLog
      linarith
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  simpa only [← Finset.sum_mul, hs, one_mul] using h

theorem finite_entropy_cross_entropy {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hq : ∀ i, 0 < q i) (hqsum : ∑ i, q i ≤ 1) :
    (∑ i, Real.negMulLog (p i)) ≤ -(∑ i, p i * Real.log (q i)) := by
  have h := costEntropy_le_reference hp hq hqsum
  simp only [costEntropy, costTotal, hs, Real.negMulLog_one, sub_zero,
    mul_sub, mul_one, Finset.sum_sub_distrib] at h
  linarith

/-- Entropy is bounded by a first moment of any injective nonnegative integer
labelling. This form accommodates either orientation of the dyadic bands. -/
theorem finite_entropy_mean_bound {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (k : ι → ℕ) (hk : Function.Injective k)
    {m : ℝ} (hm : 0 < m) (hmean : ∑ i, p i * (k i : ℝ) ≤ m) :
    (∑ i, Real.negMulLog (p i)) ≤ Real.log (m + 1) + 1 := by
  classical
  let q := m / (m + 1)
  have hm1 : 0 < m + 1 := by linarith
  have hq0 : 0 < q := div_pos hm hm1
  have hq1 : q < 1 := (div_lt_one hm1).2 (by linarith)
  have h1q : 0 < 1 - q := sub_pos.2 hq1
  have hsum : ∑ i, (1 - q) * q ^ k i ≤ 1 := by
    have hseries := (summable_geometric_of_lt_one hq0.le hq1).mul_left (1 - q)
    have h := tsum_comp_le_tsum_of_inj hseries
      (fun j => mul_nonneg h1q.le (pow_nonneg hq0.le j)) hk
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1,
      mul_inv_cancel₀ h1q.ne'] at h
    simpa only [Function.comp_def, tsum_fintype] using h
  have h := finite_entropy_cross_entropy hp hs
    (fun i => mul_pos h1q (pow_pos hq0 (k i))) hsum
  have hlog (i : ι) : Real.log ((1 - q) * q ^ k i) =
      Real.log (1 - q) + (k i : ℝ) * Real.log q := by
    rw [Real.log_mul h1q.ne' (pow_pos hq0 (k i)).ne', Real.log_pow]
  have he : -(∑ i, p i * Real.log ((1 - q) * q ^ k i)) =
      -Real.log (1 - q) - (∑ i, p i * (k i : ℝ)) * Real.log q := by
    simp_rw [hlog, mul_add, ← mul_assoc]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul]
    ring
  rw [he] at h
  have hcompl : 1 - q = (m + 1)⁻¹ := by
    dsimp [q]
    field_simp
    ring
  rw [hcompl, Real.log_inv] at h
  have hlogq : Real.log q ≤ 0 := Real.log_nonpos hq0.le hq1.le
  have hmono := mul_le_mul_of_nonpos_right hmean hlogq
  have hlogInv := Real.log_le_sub_one_of_pos (inv_pos.2 hq0)
  rw [Real.log_inv] at hlogInv
  have hunit : m * (q⁻¹ - 1) = 1 := by
    dsimp [q]
    field_simp
    ring
  have hbound := mul_le_mul_of_nonneg_left hlogInv hm.le
  rw [hunit] at hbound
  linarith

end ThresholdHC.PowerWindow
