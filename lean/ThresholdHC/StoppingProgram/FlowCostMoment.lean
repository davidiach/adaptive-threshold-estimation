import ThresholdHC.StoppingProgram.FlowConservation

/-! The work of a count flow equals its stopping-depth moment. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)

theorem rawLayer_mul_depth {N : ℕ} (u : CountState N → ℝ) (w : ℕ → ℕ → ℝ) (n : ℕ) :
    rawLayer u (fun j k => j*w j k) n = n*rawLayer u w n := by
  unfold rawLayer
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem rawLayer_depth_weight {N : ℕ} (u : CountState N → ℝ) (w : ℕ → ℕ → ℝ) (n : ℕ) :
    rawLayer (fun s => (s.1.val:ℝ)*u s) w n = n*rawLayer u w n := by
  unfold rawLayer
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold rawArray arrayAt
  split_ifs <;> ring

theorem flow_work_stopping_depth {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (f : Flow N) (hf : FlowCone f) :
    countMean μ q (fun s => (s.1.val:ℝ)*f.stopWeight s) = countMean μ q f.continueWeight := by
  let w := prefixCoefficient μ q
  have hc (n : ℕ) : rawChildren f.continueWeight (fun j k => j*w j k) n =
      (n+1:ℝ)*rawLayer f.continueWeight w n := by
    unfold rawChildren rawLayer
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hadd := prefixCoefficient_add μ q n k (by have h := Finset.mem_range.mp hk; omega)
    change w (n+1) k+w (n+1) (k+1) = w n k at hadd
    push_cast
    nlinarith [congrArg (fun x : ℝ => rawArray f.continueWeight n k*(n+1)*x) hadd]
  have ht := raw_weighted_telescope f hf (fun n k => n*w n k)
  simp only [rawLayer_mul_depth,hc,Nat.cast_zero,zero_mul,mul_zero] at ht
  rw [← rawLayer_countMean μ q (fun s => (s.1.val:ℝ)*f.stopWeight s),
    ← rawLayer_countMean μ q f.continueWeight]
  simp only [rawLayer_depth_weight]
  apply sub_eq_zero.mp
  rw [← ht,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end ThresholdHC.StoppingProgram
