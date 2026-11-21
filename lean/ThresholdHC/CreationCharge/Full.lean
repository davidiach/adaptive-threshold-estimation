import ThresholdHC.CreationCharge.Charge
import ThresholdHC.SharpRMS.Full
import ThresholdHC.UpperScale.Full

/-! Charging a fee per created coin, stated against the specification.

`created_observed` and `charged_work` are the two source sentences, for every
adaptive estimator. `charged_blind_upper` applies the fee factor to the audited
blind family `UpperScale.scaledFamily`. `charged_minimax` and `charged_rate` go
beyond the source: the charged minimax risk is squeezed between the minimax
risks at budgets `B` and `B/(1+c)`, so the sharp lower bound `ω(B^{-1/2})/6` of
`SharpRMS` and the upper bound `12*ω` of `UpperScale` at budget `B/(1+c)` give
the rate for `B ≥ 1 + c`, using `ω(s*h) ≤ s*ω(h)` for `s = sqrt(1+c) ≥ 1`. -/
noncomputable section
namespace ThresholdHC.CreationCharge
open MeasureTheory ThresholdHC.Tier6
open scoped ENNReal

theorem created_observed : CreatedObservedStatement := createdObserved_holds

theorem charged_work : ChargedWorkStatement := chargedWork_holds

theorem charged_blind_upper : ChargedBlindUpperStatement := by
  refine ⟨BlindUpper.BatchSeed, inferInstance, UpperScale.scaledFamily, ?_⟩
  intro B hB μ _
  exact ⟨UpperScale.scaledFamily_uniformBudget B μ,
    fun c hc => chargedBudget_of_budget μ _ hc (UpperScale.scaledFamily_uniformBudget B μ),
    UpperScale.scaledFamily_maximalRMSRisk B hB μ⟩

theorem charged_minimax : ChargedMinimaxStatement := chargedMinimax_holds

/-- `1/sqrt(B/(1+c)) = sqrt(1+c) * (1/sqrt B)`. -/
theorem inv_sqrt_div (c B : ℝ) (hc : 0 ≤ c) (hB : 0 < B) :
    1 / Real.sqrt (B / (1 + c)) = Real.sqrt (1 + c) * (1 / Real.sqrt B) := by
  have hc1 : 0 < 1 + c := by linarith
  rw [Real.sqrt_div' B hc1.le]
  have hsB := Real.sqrt_pos.2 hB
  have hsc := Real.sqrt_pos.2 hc1
  field_simp

theorem charged_rate : ChargedRateStatement := by
  intro μ _ c B hc hB
  have hB1 : 1 ≤ B := by linarith
  have hc1 : 0 < 1 + c := by linarith
  have hBpos : 0 < B := by linarith
  obtain ⟨hlo, hup⟩ := charged_minimax μ c B hc
  refine ⟨(SharpRMS.sharp_lower μ B hB1).trans hlo, hup.trans ?_⟩
  have hBc : 1 ≤ B / (1 + c) := (le_div_iff₀ hc1).2 (by linarith)
  refine (UpperScale.minimax_upper_12 μ (B / (1 + c)) hBc).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hs1 : 1 ≤ Real.sqrt (1 + c) := by
    rw [Real.one_le_sqrt]
    linarith
  have hm := UpperMixture.modulus_mul_le μ hs1 (h := 1 / Real.sqrt B) (by positivity)
  rw [inv_sqrt_div c B hc hBpos]
  calc
    12 * modulus μ (Real.sqrt (1 + c) * (1 / Real.sqrt B)) ≤
        12 * (Real.sqrt (1 + c) * modulus μ (1 / Real.sqrt B)) := by linarith
    _ = 12 * Real.sqrt (1 + c) * modulus μ (1 / Real.sqrt B) := by ring

end ThresholdHC.CreationCharge
