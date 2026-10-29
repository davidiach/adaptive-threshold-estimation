import ThresholdHC.RareAboveTwo.Controller

/-! Pointwise output and actual work of the observable single-coin call. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal

theorem population_path (a ρ : ℝ) (l : ℕ) (s : ℕ → ℕ → Bool) :
    populationPath (policy a ρ l) s = fun n => (tapeWord (callCost a ρ (l,s 0)) (s 0))[n]? := by
  apply Observable713.single_coin_path
  intro n hn
  rw [policy_word a ρ]
  by_cases h : callCost a ρ (l,s 0) ≤ n
  · rw [ite_eq_left h,ite_eq_right (by omega)]
  · rw [ite_eq_right h,ite_eq_left (by omega)]

theorem population_output (a ρ : ℝ) (l : ℕ) (s : ℕ → ℕ → Bool) :
    output a ρ (l,populationPath (policy a ρ l) s) = callValue a ρ (l,s 0) := by
  rw [population_path a ρ]
  exact (call_prefix_ext a ρ l (s 0) _ (Observable713.decoded_word_prefix _ _).symm).2

theorem population_work (a ρ : ℝ) (l : ℕ) (s : ℕ → ℕ → Bool) :
    totalProcessWork (populationPath (policy a ρ l) s) = (callCost a ρ (l,s 0) : ℝ≥0∞) := by
  rw [population_path a ρ,totalProcessWork_word,tapeWord_length]

end ThresholdHC.RareAboveTwo
