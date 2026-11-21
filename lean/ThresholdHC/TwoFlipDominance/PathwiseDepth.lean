import ThresholdHC.TwoFlipDominance.LocalForm
import ThresholdHC.TwoFlipFeedback.Risk
import ThresholdHC.TypedConfidence.PathValidity

/-! The dominance step under a pathwise cap. Every pair of answers is realised
on a valid path of the population experiment (a persistent table of coin
flips), so a pathwise cap of two stops the policy after two flips at every
seed, and the combinatorial step puts every local design in the normal form.
The pathwise cap also gives the almost-sure cap, because almost every path of
the original experiment is valid. -/

noncomputable section
namespace ThresholdHC.TwoFlipDominance
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.TwoFlipFeedback
open ThresholdHC.ObservableSimulation ThresholdHC.CriticalEntropy

/-- A pathwise cap of two stops the policy after two flips at every seed. -/
theorem pathwise_depth_two {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hcap : PathwiseCap A 2) (r : R) (c c' : ℕ) (hc : A.policy r [] = some c)
    (b : Bool) (hb : A.policy r [b] = some c') (b' : Bool) : A.policy r [b, b'] = none := by
  let s : ℕ → ℕ → Bool := fun j k => if j = c ∧ k = 0 then b else b'
  let x := populationPath (A.policy r) s
  have hv : ∀ k, (x k).isSome = (A.policy r (processHistory x k)).isSome :=
    fun k => ThresholdHC.TypedConfidence.populationPath_valid (A.policy r) s k
  have hs : s c 0 = b := by simp [s]
  have hx0 : x 0 = some b := by
    change populationPath (A.policy r) s 0 = some b
    rw [ThresholdHC.BlindUpper.populationPath_zero, hc]
    exact congrArg some hs
  have hx1 : x 1 = some b' := by
    change populationPath (A.policy r) s (0+1) = some b'
    rw [ThresholdHC.BlindUpper.populationPath_succ (A.policy r) s c 0 hc,
      ThresholdHC.BlindUpper.populationPath_zero]
    rw [hs, hb]
    by_cases h : c' = c
    · subst h
      simp [tapeDrop, s]
    · simp [Function.update, h, s]
  have hh : processHistory x 2 = [b, b'] := by
    simp [processHistory, processPrefix, List.ofFn_succ, hx0, hx1]
  have h := capped_halts A hcap r x hv
  rwa [hh] at h

/-- The dominance step, pathwise form. -/
theorem pathwise_dominance {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hcap : PathwiseCap A 2) (hA : LocalAcquisition A) : NoninteractiveCapTwo A := by
  intro r c hc
  obtain ⟨cont, hcont⟩ := hA r
  refine local_normal_form (A.policy r) cont hcont ?_ c hc
  intro b b' h0 h1
  obtain ⟨c0, hc0⟩ := Option.ne_none_iff_exists'.mp h0
  obtain ⟨c1, hc1⟩ := Option.ne_none_iff_exists'.mp h1
  exact pathwise_depth_two A hcap r c0 c1 hc0 b hc1 b'

/-- The pathwise cap implies the almost-sure cap. -/
theorem pathwise_almostSure {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hcap : PathwiseCap A 2) : AlmostSureCap A 2 := by
  intro q _
  filter_upwards [ThresholdHC.StoppingProgram.original_path_valid twoGapLaw A q] with z hz
  exact hcap z.1.1 z.2 hz

end ThresholdHC.TwoFlipDominance
