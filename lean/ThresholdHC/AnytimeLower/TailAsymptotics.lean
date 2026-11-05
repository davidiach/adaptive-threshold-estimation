
import ThresholdHC.AnytimeLower.TailSelection
import ThresholdHC.AnytimeLower.TailDivergence

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile

theorem profileMass_scaled (μ : Measure Gap) [IsFiniteMeasure μ]
    (τ : ℝ) {h A : ℝ} (hh : 0 ≤ h) (hA : 1 ≤ A) :
    profileMass μ τ (A*h) ≤ A*profileMass μ τ h := by
  change (∫ d, tailProfile τ (A*h) d ∂μ) ≤ A*(∫ d, tailProfile τ h d ∂μ)
  rw [← integral_const_mul]
  apply integral_mono (integrable_tailProfile μ τ (mul_nonneg (by linarith) hh))
    ((integrable_tailProfile μ τ hh).const_mul A)
  intro d
  change tailProfile τ (A*h) d ≤ A*tailProfile τ h d
  unfold tailProfile
  split_ifs
  · rw [mul_div_assoc]
    by_cases hd : h/(d:ℝ) ≤ 1
    · rw [min_eq_right hd]
      exact min_le_right _ _
    · rw [min_eq_left (le_of_not_ge hd),mul_one]
      exact (min_le_left _ _).trans hA
  · simp

theorem tail_selection_small_scale (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) {τ : ℝ} (hτ : 0 < τ) (ρ : ℝ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ B : ℝ, 0 < B → ThresholdHC.EntropyTailQuantile.budgetScale B ≤ h₀ →
      ThresholdHC.EntropyTail.selection μ ρ B ≤ ENNReal.ofReal (2*profileMass μ τ (ThresholdHC.EntropyTailQuantile.budgetScale B)) := by
  obtain ⟨h₀,hh₀,hdom⟩ := profileMass_dominates_linear μ hI hτ (1/τ)
  refine ⟨h₀,hh₀,?_⟩
  intro B hB hh
  have hp := hdom (ThresholdHC.EntropyTailQuantile.budgetScale B) (ThresholdHC.EntropyTailQuantile.budgetScale_pos hB) hh
  have hi := selection_le_profile_add μ ρ B hτ
  have hp' : ThresholdHC.EntropyTailQuantile.budgetScale B/τ ≤
      profileMass μ τ (ThresholdHC.EntropyTailQuantile.budgetScale B) := by
    calc
      _ = (1/τ)*ThresholdHC.EntropyTailQuantile.budgetScale B := by ring
      _ ≤ _ := hp
  apply hi.trans (ENNReal.ofReal_le_ofReal _)
  linarith

end ThresholdHC.AnytimeLower
