import ThresholdHC.RepeatedCheck.FixedTime
import ThresholdHC.RepeatedCheck.Exact
import ThresholdHC.RepeatedCheck.StopRule

/-! The optional-stopping counterexample of
`research/2026-10-30-confidence-transfer/ANYTIME.md` (section `Repeatedly
inspecting fixed-time intervals is not valid`).

`fixed_time` is display (28): the fixed-time Chebyshev miss bound `1/4` for
every `θ ≤ 1/4` and every `n` (`FixedTime.lean`). `repeated_check` is display
(29) as a 16-digit bracket around the exact probability
`1 - survivorTotal / 4^512` (`Exact.lean`, from the path count of
`PathCount.lean` and the kernel certificate of `Certificate.lean`).
`repeated_check_invalid` puts the two side by side at `θ = 1/4`.

The component `stopped_check` (`StopRule.lean`) restates (29) for the paper's
observable stop rule: the interval reported at the first crossing time, or at
time `512`, misses `1/4` with probability more than `1/4`. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace ThresholdHC.RepeatedCheck

theorem fixed_time : FixedTimeStatement := fixedTime_holds

theorem repeated_check : RepeatedCheckStatement := by
  intro θ hθ
  rw [repeated_check_exact θ hθ]
  exact ⟨survivorTotal_lower, survivorTotal_upper⟩

theorem repeated_check_invalid : RepeatedCheckInvalidStatement := by
  intro θ hθ
  refine ⟨fun n => fixed_time_quarter θ hθ n, ?_⟩
  rw [repeated_check_exact θ hθ]
  exact lt_trans (by norm_num) survivorTotal_lower

end ThresholdHC.RepeatedCheck
