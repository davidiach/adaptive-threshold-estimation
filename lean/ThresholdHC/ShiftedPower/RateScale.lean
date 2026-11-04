import ThresholdHC.ShiftedPower.TailRates
import ThresholdHC.HardBudget.BudgetScale

noncomputable section
open Real
namespace ThresholdHC.ShiftedPower

theorem linear_scale {ρ x c : ℝ} (hr : 0 < ρ) (hx : 0 < x) (hl : 1 ≤ c) :
    linearRate ρ (c*x) ≤ c*linearRate ρ x := by
  have hl0 : 0 < c := lt_of_lt_of_le zero_lt_one hl
  have hden : x ≤ c*x := le_mul_of_one_le_left hx.le hl
  have hlog := Real.log_le_log (div_pos hr (mul_pos hl0 hx))
    (div_le_div_of_nonneg_left hr.le hx hden)
  have hmax := max_le_max_left 0 hlog
  unfold linearRate
  rw [mul_min_of_nonneg _ _ hl0.le]
  apply min_le_min (le_mul_of_one_le_left hr.le hl)
  calc c*x*(1+max 0 (log (ρ/(c*x)))) ≤ c*x*(1+max 0 (log (ρ/x))) :=
         mul_le_mul_of_nonneg_left (add_le_add le_rfl hmax) (mul_nonneg hl0.le hx.le)
       _ = _ := by ring

theorem intermediate_scale {α ρ x c : ℝ} (hr : 0 ≤ ρ) (hl : 1 ≤ c) :
    intermediateRate α ρ (c*x) ≤ c*intermediateRate α ρ x := by
  unfold intermediateRate
  rw [mul_min_of_nonneg _ _ (by linarith : 0 ≤ c)]
  apply min_le_min (le_mul_of_one_le_left hr hl)
  apply le_of_eq
  ring

theorem rate_budget_scale {a b B : ℝ} (_ha : 0 < a) (hb : 0 < b) (hB : b ≤ B) :
    1 ≤ sqrt (B/b) ∧ (sqrt b)⁻¹/a = sqrt (B/b)*((sqrt B)⁻¹/a) := by
  obtain ⟨hs,he⟩ := ThresholdHC.HardBudget.budget_scale hb hB
  refine ⟨hs,?_⟩
  simp only [one_div] at he
  rw [he]
  ring

end ThresholdHC.ShiftedPower
