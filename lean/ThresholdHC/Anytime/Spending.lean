import Mathlib

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace ThresholdHC.Anytime

def stageFailure (δ : ℝ) (j : ℕ) : ℝ := δ/(((j:ℝ)+1)*((j:ℝ)+2))

theorem stageFailure_pos {δ : ℝ} (hd : 0 < δ) (j : ℕ) : 0 < stageFailure δ j := by
  unfold stageFailure; positivity

theorem stageFailure_le {δ : ℝ} (hd : 0 ≤ δ) (j : ℕ) : stageFailure δ j ≤ δ := by
  have hn : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hc : 1 ≤ ((j:ℝ)+1)*((j:ℝ)+2) := by nlinarith
  exact div_le_self hd hc

theorem sum_stageFailure {δ : ℝ} (_hd : 0 ≤ δ) (n : ℕ) :
    (∑ j ∈ Finset.range n, stageFailure δ j) = δ*(1-1/(n+1:ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    unfold stageFailure
    push_cast
    field_simp
    ring

theorem sum_stageFailure_le {δ : ℝ} (hd : 0 ≤ δ) (n : ℕ) :
    (∑ j ∈ Finset.range n, ENNReal.ofReal (stageFailure δ j)) ≤ ENNReal.ofReal δ := by
  have hnn (j) : 0 ≤ stageFailure δ j := div_nonneg hd (by positivity)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hnn j),sum_stageFailure hd]
  apply ENNReal.ofReal_le_ofReal
  have h : 0 ≤ 1/(n+1:ℝ) := by positivity
  nlinarith only [mul_nonneg hd h]

/-- The failure allocations control the union over every stage at once.
The events may be dependent. -/
theorem simultaneous_coverage {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Set Ω) {δ : ℝ} (hd : 0 ≤ δ)
    (hE : ∀ j, P (E j) ≤ ENNReal.ofReal (stageFailure δ j)) :
    P (⋃ j, E j) ≤ ENNReal.ofReal δ := by
  apply (measure_iUnion_le E).trans
  apply (ENNReal.tsum_le_tsum hE).trans
  apply ENNReal.tsum_le_of_sum_range_le
  exact sum_stageFailure_le hd

end ThresholdHC.Anytime
