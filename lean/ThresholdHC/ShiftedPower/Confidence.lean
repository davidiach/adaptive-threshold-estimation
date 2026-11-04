import ThresholdHC.ShiftedPower.Linear
import ThresholdHC.ShiftedPower.Intermediate
import ThresholdHC.ShiftedPower.RateScale
import ThresholdHC.ShiftedPower.Amplify
import ThresholdHC.ConfidenceProgram.Upper

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ShiftedPower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.Confidence ThresholdHC.HardBudget
open ThresholdHC.ConfidenceProgram

theorem linearRate_nonneg {ρ x : ℝ} (hr : 0 ≤ ρ) (hx : 0 ≤ x) : 0 ≤ linearRate ρ x :=
  le_min hr (mul_nonneg hx (by have h := le_max_left (0:ℝ) (log (ρ/x)); linarith))

theorem intermediateRate_nonneg {α ρ x : ℝ} (hr : 0 ≤ ρ) (hx : 0 ≤ x) : 0 ≤ intermediateRate α ρ x :=
  le_min hr (mul_nonneg (Real.rpow_nonneg hr _) hx)

private theorem effective_resolution {B δ : ℝ} (hB : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    (sqrt (B/log (1/δ)))⁻¹ = confidenceScale B δ := by
  have hl := confidence_log_pos hd hd'
  simp only [confidenceScale,Real.sqrt_div hB.le,Real.sqrt_div hl.le,inv_div]

theorem linear_confidence_family {a ρ B δ : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1) (hr : 0 < ρ) (hr' : ρ ≤ 1) (hB : 0 < B)
    (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R), PathwiseCap A ⌊B⌋₊ ∧
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν 1 a →
      RareBudget ν A ρ B ∧ ∀ q : SignLaw, RarePrior ν ρ q →
        failureProbability ν A q (27*linearConstant*linearRate ρ (confidenceScale B δ/a)) ≤ ENNReal.ofReal δ := by
  have h := amplify_margin (α := 1) (a := a) (ρ := ρ) (C := linearConstant)
    (fun b => linearRate ρ ((sqrt b)⁻¹/a)) (zero_le_one.trans linearConstant_ge_one) hB hd hd'
    (fun b hb => linearRate_nonneg hr.le (by positivity))
    (fun b b' hb hbb => by
      obtain ⟨hc,he⟩ := rate_budget_scale ha hb hbb
      rw [he]
      exact linear_scale hr (div_pos (inv_pos.mpr (sqrt_pos.mpr (hb.trans_le hbb))) ha) hc)
    (fun b hb => linear_rms_family ha ha' hr hr' hb)
  simpa only [effective_resolution hB hd hd'] using h

theorem intermediate_confidence_family {α a ρ B δ : ℝ}
    (hα : 1 < α) (hu : α < 2) (ha : 0 < a) (ha' : a ≤ 1) (hr : 0 < ρ) (hr' : ρ ≤ 1)
    (hB : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R), PathwiseCap A ⌊B⌋₊ ∧
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
      RareBudget ν A ρ B ∧ ∀ q : SignLaw, RarePrior ν ρ q →
        failureProbability ν A q (27*intermediateConstant α*intermediateRate α ρ (confidenceScale B δ/a)) ≤ ENNReal.ofReal δ := by
  have h := amplify_margin (α := α) (a := a) (ρ := ρ) (C := intermediateConstant α)
    (fun b => intermediateRate α ρ ((sqrt b)⁻¹/a)) (zero_le_one.trans (intermediateConstant_ge_one hα)) hB hd hd'
    (fun b hb => intermediateRate_nonneg hr.le (by positivity))
    (fun b b' hb hbb => by
      obtain ⟨hc,he⟩ := rate_budget_scale ha hb hbb
      rw [he]
      exact intermediate_scale hr.le hc)
    (fun b hb => intermediate_rms_family hα hu ha ha' hr hr' hb)
  simpa only [effective_resolution hB hd hd'] using h

end ThresholdHC.ShiftedPower
