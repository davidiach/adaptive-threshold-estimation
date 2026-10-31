import ThresholdHC.Genie.OptimizedBrackets

/-! Exact nonnegative scale/price elimination for a fixed genie quadruple. -/

noncomputable section
open scoped ENNReal
namespace ThresholdHC.Genie

theorem scale_objective_bound (Δ B K α η : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hα : 0 ≤ α) (hη : 0 ≤ η) (hprice : α^2*K ≤ 4*η) :
    ENNReal.ofReal (α*Δ-α^2-η*B) ≤ ENNReal.ofReal (max Δ 0)^2/ENNReal.ofReal (4+B*K) := by
  have hD : 0 < 4+B*K := by positivity
  rw [←ENNReal.ofReal_pow (le_max_right _ _),←ENNReal.ofReal_div_of_pos hD]
  apply ENNReal.ofReal_le_ofReal
  have hd : Δ ≤ max Δ 0 := le_max_left _ _
  have hαd := mul_le_mul_of_nonneg_left hd hα
  have hηB := mul_le_mul_of_nonneg_right hprice hB
  apply (le_div_iff₀ hD).mpr
  have he : (max Δ 0)^2-(α*max Δ 0-α^2*(1+B*K/4))*(4+B*K) =
      (max Δ 0-α*(4+B*K)/2)^2 := by ring
  have hquad : (α*max Δ 0-α^2*(1+B*K/4))*(4+B*K) ≤ (max Δ 0)^2 := by nlinarith [sq_nonneg (max Δ 0-α*(4+B*K)/2)]
  have hobj : α*Δ-α^2-η*B ≤ α*max Δ 0-α^2*(1+B*K/4) := by nlinarith
  exact (mul_le_mul_of_nonneg_right hobj hD.le).trans hquad

theorem scale_objective_attained (Δ B K : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ α η : ℝ, 0 ≤ α ∧ 0 ≤ η ∧ α^2*K = 4*η ∧
      ENNReal.ofReal (α*Δ-α^2-η*B) = ENNReal.ofReal (max Δ 0)^2/ENNReal.ofReal (4+B*K) := by
  have hD : 0 < 4+B*K := by positivity
  let α := 2*max Δ 0/(4+B*K)
  let η := α^2*K/4
  refine ⟨α,η,by dsimp [α]; positivity,by dsimp [η]; positivity,by dsimp [η]; ring,?_⟩
  rw [←ENNReal.ofReal_pow (le_max_right _ _),←ENNReal.ofReal_div_of_pos hD]
  have he : α*Δ = α*max Δ 0 := by
    by_cases hΔ : 0 ≤ Δ
    · rw [max_eq_left hΔ]
    · simp [α,max_eq_right (le_of_not_ge hΔ)]
  rw [he]
  congr 1
  dsimp [η,α]
  field_simp
  ring

end ThresholdHC.Genie
