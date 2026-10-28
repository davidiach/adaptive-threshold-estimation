import ThresholdHC.CriticalAllSizes.SingleGap

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.CriticalAllSizes
open CriticalEntropy

/-- Uniform entropy bound for every finite gap count, including zero.
The original coefficient 1/512 remains available when log K ≥ 32. -/
theorem finite_gap_sign_entropy_all {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : SignTest R)
    (K : ℕ) (d : Fin K → EntropyGap)
    (hgap : ∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ))
    (hfinite : ∀ i b, expectedSignTestWork ν (signParameter (d i) b) A ≠ ∞)
    (herror : ∀ i b, (ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).real
      {z | A.output z ≠ b} ≤ 1/10) :
    (K : ℝ)*log (K : ℝ)/4096 ≤
      ∑ i, (d i : ℝ)^2*(expectedSignTestWork ν (signParameter (d i) false) A).toReal := by
  classical
  by_cases hK : 32 ≤ log (K : ℝ)
  · have h := finite_gap_sign_entropy ν A K d hK hgap hfinite herror
    have hp := mul_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
      (show 0 ≤ log (K : ℝ) by linarith)
    linarith
  · have hs : (K : ℝ)/128 ≤
        ∑ i, (d i : ℝ)^2*(expectedSignTestWork ν (signParameter (d i) false) A).toReal := by
      calc
        _ = ∑ _i : Fin K, (1/128 : ℝ) := by simp; ring
        _ ≤ _ := Finset.sum_le_sum (fun i _ => single_gap_work ν A (d i) (hfinite i false)
          (by simpa using herror i false) (by simpa using herror i true))
    have hm := mul_le_mul_of_nonneg_left (le_of_lt (not_le.mp hK))
      (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
    linarith

end ThresholdHC.CriticalAllSizes
