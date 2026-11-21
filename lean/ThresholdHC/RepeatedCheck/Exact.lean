import ThresholdHC.RepeatedCheck.PathCount
import ThresholdHC.RepeatedCheck.Certificate

/-! The exact value behind display (29) of
`research/2026-10-30-confidence-transfer/ANYTIME.md`: at `θ = 1/4` the
probability that the check `(4H_n - n)² > 12n` fires at some `n ≤ 512` is
`1 - survivorTotal / 4^512`, where `survivorTotal` is the kernel-checked
survivor weight of row `512`. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open ThresholdHC.Tier2

namespace ThresholdHC.RepeatedCheck

/-- The repeated-check probability in closed form, on the literal event of
`RepeatedCheckStatement`. -/
theorem repeated_check_exact (θ : unitInterval) (hθ : (θ : ℝ) = 1/4) :
    (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | ∃ n : ℕ, n ≤ 512 ∧
          12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2} =
      1 - (survivorTotal : ℝ) / 4 ^ 512 := by
  have h := repeatedEvent_real θ hθ 512
  rw [survivorRow_sum_512] at h
  exact h

end ThresholdHC.RepeatedCheck
