import ThresholdHC.ObservedState.StateModel

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ThresholdHC.ObservedState
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation

theorem conditionalMean_exact {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N)
    (s : Fin N → Bool) (u : unitInterval) :
    (∫ b : Bool, (if b then (1 : ℝ) else -1)
      ∂bernoulliMeasure true false (gapParameter (s (cell u)) (cap (cell u)))) =
        conditionalMean cap cell s u := by
  rw [integral_bernoulliMeasure]
  simp only [ite_true,Bool.false_eq_true,ite_false,smul_eq_mul,mul_one,mul_neg_one,conditionalMean]
  ring

theorem conditionalMean_magnitude {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N)
    (s : Fin N → Bool) (u : unitInterval) :
    |conditionalMean cap cell s u| = 2 * (cap (cell u) : ℝ) := by
  have hd := (cap (cell u)).property.1
  cases hs : s (cell u)
  · have he : conditionalMean cap cell s u = -2 * (cap (cell u) : ℝ) := by
      simp only [conditionalMean,gapParameter,hs,Bool.false_eq_true,ite_false]
      ring
    rw [he,abs_of_neg (by nlinarith)]
    ring
  · have he : conditionalMean cap cell s u = 2 * (cap (cell u) : ℝ) := by
      simp only [conditionalMean,gapParameter,hs,ite_true]
      ring
    rw [he,abs_of_pos (by positivity)]

end ThresholdHC.ObservedState
