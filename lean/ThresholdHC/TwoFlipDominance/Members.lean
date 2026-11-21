import ThresholdHC.TwoFlipDominance.PathwiseDepth
import ThresholdHC.TwoFlipFeedback.Members
import ThresholdHC.TwoFlipFeedback.Upper

/-! Members of the paper's class and the feedback witness. The two genuine
two-flip schedules of `ThresholdHC.TwoFlipFeedback` (the same coin twice, two
fresh coins) and its zero-flip estimator with constant output `1/8` are local
designs with explicit continuation rules, so the class infimum is at most
`1/64`. The feedback witness obeys the pathwise cap but is not a local design:
otherwise the pathwise dominance step would put it in the normal form. -/

noncomputable section
namespace ThresholdHC.TwoFlipDominance
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.TwoFlipFeedback

/-- The class condition for a schedule that stops at length two, from three
conditions on the continuation rules. -/
theorem stopAt_local (p : List Bool → ℕ) (cont : ℕ → List Bool → Bool)
    (h0 : cont (p []) [] = true)
    (h1 : ∀ a, cont (p [a]) (if p [] = p [a] then [a] else []) = true)
    (h2 : ∀ a b c, cont c ((if p [] = c then [a] else []) ++ (if p [a] = c then [b] else [])) =
      false) :
    LocalAt (stopAt 2 p) cont := by
  have e0 : stopAt 2 p [] = some (p []) := rfl
  have e1 (a : Bool) : stopAt 2 p [a] = some (p [a]) := rfl
  intro xs
  rcases xs with _ | ⟨a, _ | ⟨b, t⟩⟩
  · rw [e0]
    refine ⟨⟨fun h => absurd h (Option.some_ne_none _), fun h => ?_⟩, fun c hc => ?_⟩
    · have h' := h (p [])
      rw [ownBits_nil, h0] at h'
      exact absurd h' (by decide)
    · rw [← Option.some_injective _ hc, ownBits_nil]
      exact h0
  · have o (c : ℕ) : ownBits (stopAt 2 p) c [a] = if p [] = c then [a] else [] := by
      rw [ownBits_one, e0]
      simp only [Option.some.injEq]
    rw [e1]
    refine ⟨⟨fun h => absurd h (Option.some_ne_none _), fun h => ?_⟩, fun c hc => ?_⟩
    · have h' := h (p [a])
      rw [o, h1] at h'
      exact absurd h' (by decide)
    · rw [← Option.some_injective _ hc, o]
      exact h1 a
  · have hn : stopAt 2 p (a :: b :: t) = none := by
      simp [stopAt]
    have o (c : ℕ) : ownBits (stopAt 2 p) c (a :: b :: t) =
        (if p [] = c then [a] else []) ++ (if p [a] = c then [b] else []) := by
      rw [ownBits_stopAt_long, ownBits_two, e0, e1]
      simp only [Option.some.injEq]
    rw [hn]
    refine ⟨⟨fun _ c => ?_, fun _ => rfl⟩, fun c hc => absurd hc (by simp)⟩
    rw [o]
    exact h2 a b c

theorem sameCoin_local : LocalAcquisition sameCoinEstimator := by
  intro r
  refine ⟨fun d own => decide (d = 0 ∧ own.length < 2), ?_⟩
  refine stopAt_local (fun _ => 0) (fun d own => decide (d = 0 ∧ own.length < 2))
    (by decide) (fun a => by simp) (fun a b c => ?_)
  by_cases h : c = 0
  · subst h
    simp
  · simp [h]

theorem freshCoin_local : LocalAcquisition freshCoinEstimator := by
  intro r
  refine ⟨fun d own => decide (d < 2 ∧ own.length < 1), ?_⟩
  refine stopAt_local (fun xs => xs.length) (fun d own => decide (d < 2 ∧ own.length < 1))
    (by decide) (fun a => by simp) (fun a b c => ?_)
  rcases c with _ | _ | c
  · simp
  · simp
  · simp

theorem constant_local : LocalAcquisition constantEstimator := by
  intro r
  refine ⟨fun _ _ => false, fun xs => ⟨⟨fun _ _ => rfl, fun _ => rfl⟩, fun c hc => ?_⟩⟩
  exact absurd hc (by simp [constantEstimator])

theorem local_minimax_le : localMinimax ≤ ENNReal.ofReal (1/64) := by
  unfold localMinimax
  refine (sInf_le ?_).trans constant_upper
  exact ⟨Unit, inferInstance, constantEstimator, pathwise_almostSure constantEstimator constant_cap,
    constant_local, rfl⟩

/-- The feedback witness is not a local design. -/
theorem feedback_not_local : ¬ LocalAcquisition feedbackEstimator := fun h =>
  feedback_not_noninteractive (pathwise_dominance feedbackEstimator feedback_cap h)

end ThresholdHC.TwoFlipDominance
