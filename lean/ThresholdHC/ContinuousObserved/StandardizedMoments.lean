import ThresholdHC.ContinuousObserved.BinaryMoments

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation

theorem binary_standardized_bound (d : Gap) (hd : (d : ℝ) ≤ 1 / 4) (s b : Bool) :
    |binaryValue b - binaryMean d s| /
      Real.sqrt (variance binaryValue (bernoulliMeasure true false (gapParameter s d))) ≤ Real.sqrt 3 := by
  have hv := binary_variance_lower d hd s
  have hs : 0 < Real.sqrt (variance binaryValue (bernoulliMeasure true false (gapParameter s d))) :=
    Real.sqrt_pos.mpr (by linarith)
  apply (div_le_iff₀ hs).mpr
  have hroot : Real.sqrt 3 / 2 ≤
      Real.sqrt (variance binaryValue (bernoulliMeasure true false (gapParameter s d))) := by
    calc
      _ = Real.sqrt (3 / 4 : ℝ) := by rw [Real.sqrt_div (by norm_num)]; norm_num
      _ ≤ _ := Real.sqrt_le_sqrt hv
  have h := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg 3)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hb := binary_centered_bound d hd s b
  nlinarith

theorem binary_standardized_moment (d : Gap) (hd : (d : ℝ) ≤ 1 / 4)
    (s : Bool) {q : ℝ} (hq : 0 ≤ q) :
    (∫ b, (|binaryValue b - binaryMean d s| /
      Real.sqrt (variance binaryValue (bernoulliMeasure true false (gapParameter s d)))) ^ q
      ∂bernoulliMeasure true false (gapParameter s d)) ≤ (3 : ℝ) ^ (q / 2) := by
  have hb (b : Bool) :
      (|binaryValue b - binaryMean d s| /
        Real.sqrt (variance binaryValue (bernoulliMeasure true false (gapParameter s d)))) ^ q ≤
          (3 : ℝ) ^ (q / 2) := by
    calc
      _ ≤ (Real.sqrt 3) ^ q :=
        Real.rpow_le_rpow (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
          (binary_standardized_bound d hd s b) hq
      _ = _ := by
        rw [Real.sqrt_eq_rpow,← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        congr 1
        ring
  calc
    _ ≤ ∫ _ : Bool, (3 : ℝ) ^ (q / 2) ∂bernoulliMeasure true false (gapParameter s d) :=
      integral_mono Integrable.of_finite (integrable_const _) hb
    _ = _ := by simp

end ThresholdHC.ContinuousObserved
