import ThresholdHC.ObservedState.Mean

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation

def binaryValue (b : Bool) : ℝ := if b then 1 else -1

def binaryMean (d : Gap) (s : Bool) : ℝ := 2 * (gapParameter s d : ℝ) - 1

theorem binary_mean (d : Gap) (s : Bool) :
    (∫ b, binaryValue b ∂bernoulliMeasure true false (gapParameter s d)) = binaryMean d s := by
  rw [integral_bernoulliMeasure]
  simp only [binaryValue,ite_true,Bool.false_eq_true,ite_false,smul_eq_mul,mul_one,mul_neg_one,binaryMean]
  ring

theorem binary_mean_magnitude (d : Gap) (s : Bool) : |binaryMean d s| = 2 * (d : ℝ) := by
  simpa only [ThresholdHC.ObservedState.conditionalMean,binaryMean] using
    ThresholdHC.ObservedState.conditionalMean_magnitude (fun _ : Fin 1 => d)
      (fun _ : unitInterval => (0 : Fin 1)) (fun _ => s) (0 : unitInterval)

theorem binary_variance (d : Gap) (s : Bool) :
    variance binaryValue (bernoulliMeasure true false (gapParameter s d)) = 1 - 4 * (d : ℝ) ^ 2 := by
  have hm : MemLp binaryValue 2 (bernoulliMeasure true false (gapParameter s d)) := by
    apply MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact ae_of_all _ (fun b => by cases b <;> norm_num [binaryValue])
  rw [variance_eq_sub hm,binary_mean,integral_bernoulliMeasure]
  cases s <;> simp [binaryMean,gapParameter,binaryValue] <;> ring

theorem binary_variance_lower (d : Gap) (hd : (d : ℝ) ≤ 1 / 4) (s : Bool) :
    3 / 4 ≤ variance binaryValue (bernoulliMeasure true false (gapParameter s d)) := by
  rw [binary_variance]
  have hp := d.property.1
  nlinarith

theorem binary_centered_bound (d : Gap) (hd : (d : ℝ) ≤ 1 / 4) (s b : Bool) :
    |binaryValue b - binaryMean d s| ≤ 3 / 2 := by
  calc
    _ ≤ |binaryValue b| + |binaryMean d s| := abs_sub _ _
    _ = 1 + 2 * (d : ℝ) := by rw [binary_mean_magnitude]; cases b <;> norm_num [binaryValue]
    _ ≤ _ := by linarith

end ThresholdHC.ContinuousObserved
