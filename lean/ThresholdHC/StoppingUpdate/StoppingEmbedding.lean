import ThresholdHC.StoppingUpdate.Specification
import ThresholdHC.PilotFeedback.ScheduledPolicy

/-! A one-update plan of `PilotFeedback.Scheduled`, which fixes its split after
the pilot, is a one-stopping-update plan: its trigger fires exactly at the
prefix of length `18 + split`. So the class of `Specification.lean` contains
the class of `PilotFeedback.OneUpdateLowerStatement`. -/
namespace ThresholdHC.StoppingUpdate
open ThresholdHC.PilotFeedback

/-- With the split trigger, the first triggering prefix of length at most `n`
is the one of length `18 + split`, once that length is reached. -/
theorem boundary_of_split (P : Scheduled.Plan) (Q : Plan)
    (hQ : ∀ z, Q.trigger z = decide (z.length = 18 + (P.split (z.take 18)).val))
    (xs : List Bool) : ∀ n, n ≤ xs.length →
      boundary Q xs n = if 18 + (P.split (xs.take 18)).val ≤ n
        then some (xs.take (18 + (P.split (xs.take 18)).val)) else none
  | 0, _ => by simp [boundary]
  | n+1, h => by
    have ih := boundary_of_split P Q hQ xs n (by omega)
    rw [boundary, ih, hQ]
    by_cases hs : 18 + (P.split (xs.take 18)).val ≤ n
    · simp [hs, show 18 + (P.split (xs.take 18)).val ≤ n+1 by omega]
    · by_cases hp : 18 ≤ n+1
      · have hlen : (xs.take (n+1)).length = n+1 := by simp; omega
        have htake : (xs.take (n+1)).take 18 = xs.take 18 := by
          rw [List.take_take, Nat.min_eq_left hp]
        rw [hlen, htake]
        by_cases he : n+1 = 18 + (P.split (xs.take 18)).val
        · simp [hs, he]
        · simp [hs, he, show ¬ 18 + (P.split (xs.take 18)).val ≤ n+1 by omega]
      · simp [hs, hp, show ¬ 18 + (P.split (xs.take 18)).val ≤ n+1 by omega]

theorem frozen_of_split (P : Scheduled.Plan) (Q : Plan) (h1 : Q.first = P.first)
    (h2 : Q.second = P.second)
    (hQ : ∀ z, Q.trigger z = decide (z.length = 18 + (P.split (z.take 18)).val))
    (xs : List Bool) (hl : 18 ≤ xs.length) :
    frozen Q xs (xs.take 18) (xs.length - 18) =
      Scheduled.frozen P xs (xs.take 18) (xs.length - 18) := by
  unfold frozen Scheduled.frozen
  rw [show 18 + (xs.length - 18) = xs.length by omega,
    boundary_of_split P Q hQ xs xs.length le_rfl]
  by_cases hs : 18 + (P.split (xs.take 18)).val ≤ xs.length
  · simp [hs, h2, show ¬ xs.length - 18 < (P.split (xs.take 18)).val by omega]
  · simp [hs, h1, show xs.length - 18 < (P.split (xs.take 18)).val by omega]

/-- Every scheduled one-update policy is a one-stopping-update policy. -/
theorem policy_of_scheduled (P : Scheduled.Plan) :
    policy ⟨P.first, fun z => decide (z.length = 18 + (P.split (z.take 18)).val), P.second⟩ =
      Scheduled.policy P := by
  have hl : label ⟨P.first, fun z => decide (z.length = 18 + (P.split (z.take 18)).val),
      P.second⟩ = Scheduled.label P := by
    funext xs
    by_cases hlen : xs.length < 18
    · simp only [label, Scheduled.label, Ordered.label, hlen, ite_true]
    · have key := frozen_of_split P
        ⟨P.first, fun z => decide (z.length = 18 + (P.split (z.take 18)).val), P.second⟩
        rfl rfl (fun _ => rfl) xs (by omega)
      simp only [label, Scheduled.label, Ordered.label, hlen, ite_false, Ordered.effective, key]
  simp only [policy, Scheduled.policy, hl]

/-- Every algorithm whose seed selects a scheduled one-update plan also selects
a one-stopping-update plan, so the targets apply to it. -/
theorem stopping_of_scheduled {R : Type} [MeasurableSpace R] (A : Tier6.AdaptiveEstimator R)
    (h : ∀ r, ∃ P : Scheduled.Plan, A.policy r = Scheduled.policy P) :
    ∀ r, ∃ Q : Plan, A.policy r = policy Q := fun r => by
  obtain ⟨P, hP⟩ := h r
  exact ⟨_, hP.trans (policy_of_scheduled P).symm⟩

end ThresholdHC.StoppingUpdate
