import ThresholdHC.ShiftedPower.Certificate
import ThresholdHC.ShiftedPower.BaseLevel
import ThresholdHC.ShiftedPower.TailRates

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ShiftedPower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailUpper

def intermediateConstant (α : ℝ) : ℝ := 1+8*sqrt (workConstant α)/(1-summationRatio α)

theorem intermediateConstant_ge_one {α : ℝ} (hα : 1 < α) : 1 ≤ intermediateConstant α := by
  unfold intermediateConstant
  exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _)) (sub_pos.mpr (ratio_lt_one hα)).le)

theorem amplitude_le_rarity {α a ρ : ℝ} (hα : 1 < α) (ha : 0 < a) (hr : 0 < ρ)
    (k : ℕ) (hk : massBound α a k ≤ 2*ρ) :
    amplitude α a k ≤ 2*ρ^(1-1/α)/a := by
  have ha0 : 0 < α := by linarith
  have he : 0 ≤ 1-1/α := sub_nonneg.mpr ((div_le_one ha0).mpr hα.le)
  have he' : 1-1/α ≤ 1 := by have h := div_nonneg zero_le_one ha0.le; linarith
  have hm := Real.rpow_le_rpow (mass_positive (α := α) ha k).le hk he
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le] at hm
  have htwo : (2:ℝ)^(1-1/α) ≤ 2 := by
    calc _ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he'
         _ = 2 := Real.rpow_one _
  unfold amplitude
  rw [amplitude_identity (by linarith) ha]
  exact div_le_div_of_nonneg_right (hm.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hr.le _))) ha.le

/-- A finite number of levels suffices for any positive budget. The
geometric certificate has a bound independent of that number of levels. -/
theorem intermediate_rms_family {α a ρ B : ℝ}
    (hα : 1 < α) (hu : α < 2) (ha : 0 < a) (ha' : a ≤ 1) (hr : 0 < ρ) (hr' : ρ ≤ 1) (hB : 0 < B) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
      RareBudget ν A ρ B ∧ rareRisk ν A ρ ≤
        ENNReal.ofReal (intermediateConstant α*intermediateRate α ρ ((sqrt B)⁻¹/a)) := by
  let t := ρ^(1-1/α)*((sqrt B)⁻¹/a)
  have ht : 0 < t := mul_pos (Real.rpow_pos_of_pos hr _) (div_pos (inv_pos.mpr (sqrt_pos.mpr hB)) ha)
  have hC := intermediateConstant_ge_one hα
  by_cases hs : ρ ≤ t
  · refine ⟨_,inferInstance,idleEstimator ρ,?_⟩
    intro ν _ _
    refine ⟨fun q _ => (idle_work ν q ρ).le.trans bot_le,?_⟩
    unfold intermediateRate
    rw [min_eq_left hs]
    exact (idle_risk ν ρ).trans (ENNReal.ofReal_le_ofReal
      ((by linarith : ρ/2 ≤ ρ).trans (le_mul_of_one_le_left hr.le hC)))
  · obtain ⟨k,hkl,hku⟩ := base_level (by linarith) hu ha ha' hr hr'
    obtain ⟨J,hJ⟩ := finite_bias_level (by linarith) hu ha ht k
    refine ⟨_,inferInstance,shiftedEstimator α a B k J,?_⟩
    intro ν _ hm
    have hbound (q : SignLaw) (hq : RarePrior ν ρ q) :=
      shifted_bounds ν q (by linarith) hu ha hB hm hq k J (by linarith)
    refine ⟨fun q hq => (hbound q hq).1,?_⟩
    apply iSup_le; intro q; apply iSup_le; intro hq
    apply (hbound q hq).2.trans
    apply ENNReal.ofReal_le_ofReal
    unfold intermediateRate
    rw [min_eq_right (le_of_not_ge hs)]
    have hcert := intermediate_certificate hα hu ha k J
    have hamp := amplitude_le_rarity hα ha hr k hku
    have hden : 0 < 1-summationRatio α := sub_pos.mpr (ratio_lt_one hα)
    have hsqrt : 0 < sqrt B := sqrt_pos.mpr hB
    have hcert' : allocationCertificate (varianceWeights α a k J) (costWeights α a k J) ≤
        8*sqrt (workConstant α)*ρ^(1-1/α)/(a*(1-summationRatio α)) := by
      calc _ ≤ 4*sqrt (workConstant α)*amplitude α a k/(1-summationRatio α) := hcert
           _ ≤ 4*sqrt (workConstant α)*(2*ρ^(1-1/α)/a)/(1-summationRatio α) :=
             div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hamp (by positivity)) hden.le
           _ = _ := by simp only [div_eq_mul_inv,mul_inv]; ring
    have hdiv := div_le_div_of_nonneg_right hcert' hsqrt.le
    calc _ ≤ t+(8*sqrt (workConstant α)*ρ^(1-1/α)/(a*(1-summationRatio α)))/sqrt B :=
           add_le_add hJ hdiv
         _ = intermediateConstant α*t := by
           unfold intermediateConstant
           dsimp only [t]
           simp only [div_eq_mul_inv,mul_inv]
           ring

end ThresholdHC.ShiftedPower
