import ThresholdHC.ContinuousObserved.SampledEnvironment
import ThresholdHC.ContinuousObserved.CountableWord

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6

def labelQuery (u : ℕ → unitInterval) : Option ℕ → unitInterval
  | none => 0
  | some i => u i

theorem sampling_prefix_expectation {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool)
    (u : ℕ → unitInterval) (pol : List Bool → Option ℕ) (n : ℕ) (F : Prefix n → ℝ≥0∞) :
    prefixExpectation D s (fun xs => (pol xs).isSome) (fun xs => labelQuery u (pol xs)) n F =
      countableExpectation pol (fun i => stateParameter D s (u i)) n F := by
  induction n generalizing pol with
  | zero => rfl
  | succ n ih =>
    cases hp : pol [] with
    | none => simp [prefixExpectation,countableExpectation,hp]
    | some i =>
      simp only [prefixExpectation,countableExpectation,hp,Option.isSome_some,ite_true,labelQuery]
      apply lintegral_congr
      intro b
      exact ih (fun xs => pol (b :: xs)) (fun w => F (Fin.cons (some b) w))

theorem sampled_prefix_creation_sum {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (s : Fin N → Bool) (A : AdaptiveEstimator R)
    (z : R × (ℕ → unitInterval)) (n : ℕ) (F : Prefix n → ℝ≥0∞) :
    prefixExpectation D s ((sampledStateEstimator A).continues z) ((sampledStateEstimator A).query z) n F =
      ∑ w, ENNReal.ofReal (creationLaw (sampledPolicy A z) (sampledGap D z) (sampledPrior D s z) w) * F w := by
  change prefixExpectation D s (fun xs => (A.policy z.1 xs).isSome)
    (fun xs => labelQuery z.2 (A.policy z.1 xs)) n F = _
  rw [sampling_prefix_expectation,countableExpectation_sum]
  apply Finset.sum_congr rfl
  intro w _
  congr 2
  unfold sampledPolicy sampledGap sampledPrior
  simp_rw [stateSignPrior_coe,deterministic_creation]
  rfl

end ThresholdHC.ContinuousObserved
