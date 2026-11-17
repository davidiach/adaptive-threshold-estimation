import SharpMiddleBudget
import SharpReduction

/-! The optimal universal coefficient for unrestricted adaptive ordinary protocols. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Tier6
open scoped ENNReal

private theorem critical_at_budget (B : ℝ) (hb : 4 ≤ B) :
    ∃ g : Gap, g.val=1/Real.sqrt B ∧ (2*g.val)^2*B=4 := by
  have hr : (2:ℝ) ≤ Real.sqrt B := (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have hp : 0 < Real.sqrt B := by linarith
  let g : Gap := ⟨1/Real.sqrt B,one_div_pos.mpr hp,(div_le_iff₀ hp).2 (by linarith)⟩
  refine ⟨g,rfl,?_⟩
  change (2*(1/Real.sqrt B))^2*B=4
  field_simp [hp.ne']
  nlinarith only [Real.sq_sqrt (show 0 ≤ B by linarith)]

/-- The ordinary population experiment allows arbitrary measurable private seeds,
interleaving, revisits and stopping under a uniform expected-work budget. -/
theorem unrestricted_minimax_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hb : 1 ≤ B) :
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/6) ≤ minimaxRisk μ B := by
  by_cases small : B ≤ 4
  · apply le_trans _ (four_budget_minimax_lower μ B (by linarith) small)
    apply ENNReal.ofReal_le_ofReal
    linarith [modulus_le_one μ (show 0 ≤ 1/Real.sqrt B by positivity)]
  obtain ⟨g,hg,crit⟩ := critical_at_budget B (le_of_not_ge small)
  rw [←hg,show modulus μ g.val/6 = modulus μ g.val*(1/6) by ring,
      ENNReal.ofReal_mul (modulus_pos μ g.property.1).le]
  exact (mul_le_mul_right (critical_minimax_lower g B crit) _).trans (critical_gap_reduction μ g B)

/-- Strictly stronger coefficient for every gap law once B≥25. -/
theorem large_budget_minimax_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hb : 25 ≤ B) :
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*Real.sqrt (59/2100:ℝ)) ≤ minimaxRisk μ B := by
  obtain ⟨g,hg,crit⟩ := critical_at_budget B (by linarith)
  have hr : (5:ℝ) ≤ Real.sqrt B := (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have small : 2*g.val ≤ 2/5 := by
    rw [hg]
    have hp : 0 < Real.sqrt B := by linarith
    rw [mul_one_div,div_le_iff₀ hp]
    linarith
  rw [←hg,ENNReal.ofReal_mul (modulus_pos μ g.property.1).le]
  exact (mul_le_mul_right (weak_gap_minimax_lower g B small crit) _).trans (critical_gap_reduction μ g B)

/-- A real coefficient works simultaneously at every gap law and admissible
budget if and only if it is at most one sixth. -/
theorem universal_coefficient_iff (c : ℝ) :
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
      ENNReal.ofReal (modulus μ (1/Real.sqrt B)*c) ≤ minimaxRisk μ B) ↔ c ≤ 1/6 := by
  constructor
  · intro h
    have e := h (Measure.dirac endpointGap) 4 (by norm_num)
    have m : modulus (Measure.dirac endpointGap) (1/Real.sqrt 4) = 1 := by
      norm_num [modulus,clippedGap,endpointGap,Real.sqrt_eq_iff_mul_self_eq]
    rw [m,one_mul,endpoint_minimax_eq] at e
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp e
  · intro hc μ _ B hb
    apply le_trans _ (unrestricted_minimax_lower μ B hb)
    apply ENNReal.ofReal_le_ofReal
    have hp : 0 < 1/Real.sqrt B := by positivity
    simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hc (modulus_pos μ hp).le

end ThresholdHC.SharpRMS
