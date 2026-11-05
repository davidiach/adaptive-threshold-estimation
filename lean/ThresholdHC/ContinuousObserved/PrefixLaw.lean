import ThresholdHC.ContinuousObserved.WordMeasurable
import ThresholdHC.ContinuousObserved.FreshObservation

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

/-- The ordinary fresh Bernoulli observation rule at every chosen state,
written as its finite-horizon expectation operator. -/
def prefixExpectation {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool)
    (c : List Bool → Bool) (q : List Bool → unitInterval) :
    (n : ℕ) → (Prefix n → ℝ≥0∞) → ℝ≥0∞
  | 0, F => F Fin.elim0
  | n + 1, F =>
    if c [] then
      ∫⁻ b : Bool, prefixExpectation D s (fun ys => c (b :: ys)) (fun ys => q (b :: ys)) n
        (fun w => F (Fin.cons (some b) w))
        ∂bernoulliMeasure true false (gapParameter (s (D.cell (q []))) (D.gap (q [])))
    else F (fun _ => none)

/-- The adaptive simulation has precisely the finite-prefix law obtained
by taking a fresh observation at each point selected from the past. -/
theorem noisyWord_prefix_law {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool)
    (c : List Bool → Bool) (q : List Bool → unitInterval) (n : ℕ) (F : Prefix n → ℝ≥0∞) :
    (∫⁻ z, F (noisyWord D c q n z.1 z.2)
      ∂uniformTapeMeasure.prod (Measure.pi (fun i => Tier2.tapeMeasure (gapParameter (s i) (D.cap i))))) =
        prefixExpectation D s c q n F := by
  induction n generalizing c q with
  | zero => simp [noisyWord,prefixExpectation]
  | succ n ih =>
    by_cases hc : c [] = true
    · let j := D.cell (q [])
      let G (z : Bool × ((ℕ → ℝ) × (Fin N → ℕ → Bool))) :=
        F (Fin.cons (some z.1) (noisyWord D (fun ys => c (z.1 :: ys))
          (fun ys => q (z.1 :: ys)) n z.2.1 z.2.2))
      have hG : Measurable G := by
        apply measurable_from_prod_countable_right
        intro b
        exact (measurable_of_countable (fun w : Prefix n => F (Fin.cons (some b) w))).comp
          (measurable_noisyWord D (fun ys => c (b :: ys)) (fun ys => q (b :: ys)) n)
      have hs := (fresh_observation_preserving D.cap s j (D.gap (q [])) (D.bound (q []))).lintegral_comp hG
      have he : (∫⁻ z, F (noisyWord D c q (n + 1) z.1 z.2)
          ∂uniformTapeMeasure.prod (Measure.pi (fun i => Tier2.tapeMeasure (gapParameter (s i) (D.cap i))))) =
          ∫⁻ z, G z ∂(bernoulliMeasure true false (gapParameter (s j) (D.gap (q [])))).prod
            (uniformTapeMeasure.prod (Measure.pi (fun i => Tier2.tapeMeasure (gapParameter (s i) (D.cap i))))) := by
        simpa only [G,noisyWord,hc,ite_true,stepNoise,List.length_nil,j] using hs
      rw [he,lintegral_prod _ hG.aemeasurable]
      simp only [prefixExpectation,hc,ite_true]
      apply lintegral_congr
      intro b
      exact ih (fun ys => c (b :: ys)) (fun ys => q (b :: ys)) (fun w => F (Fin.cons (some b) w))
    · simp [noisyWord,prefixExpectation,hc]

end ThresholdHC.ContinuousObserved
