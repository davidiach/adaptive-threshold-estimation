import ThresholdHC.ShiftedPower.TailRates

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ShiftedPower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile ThresholdHC.Confidence
open ThresholdHC.ConfidenceTransfer ThresholdHC.ConfidenceProgram ThresholdHC.Genie

theorem lower_from_quantile (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4)
    (z : ℝ → ℝ) (hz : ∀ h, 0 < h → z h ≤ tailModulus (quantileTail μ ρ) h) :
    ENNReal.ofReal (z (EntropyTailQuantile.budgetScale B)/32) ≤ rareMinimaxRisk μ ρ B ∧
      ENNReal.ofReal (z (confidenceScale B δ)/960) ≤ rareConfidenceRadius μ ρ B δ := by
  have rms (b : ℝ) (h : 0 < b) : ENNReal.ofReal (z (EntropyTailQuantile.budgetScale b)/32) ≤ rareMinimaxRisk μ ρ b :=
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hz _ (inv_pos.mpr (Real.sqrt_pos.mpr h)))
      (by norm_num : (0:ℝ) ≤ 32))).trans (ThresholdHC.EntropyTailSharp.quantile_tail_lower_general μ hr hu h)
  refine ⟨rms B hb,?_⟩
  let β := B/Real.log (1/δ)
  have hl := confidence_log_pos hd hd'
  have hβ : 0 < β := div_pos hb hl
  have he := (rms β hβ).trans (infinite_program_comparison μ ρ β hr (by linarith) hβ).1
  have hscale : EntropyTailQuantile.budgetScale β = confidenceScale B δ := by
    simp only [EntropyTailQuantile.budgetScale,β,confidenceScale,Real.sqrt_div hb.le,Real.sqrt_div hl.le,inv_div]
  rw [hscale] at he
  have h := (ENNReal.div_le_div_right he 30).trans (stopping_confidence_lower μ hr (by linarith) hb hd hd')
  convert h using 1
  rw [← show ENNReal.ofReal (30:ℝ) = 30 from ENNReal.ofReal_ofNat 30,← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<30)]
  congr 1
  ring

theorem linear_lower (μ : Measure Gap) [IsProbabilityMeasure μ] {a ρ B δ : ℝ}
    (hm : ExactPowerLaw μ 1 a) (ha : 0 < a) (hr : 0 < ρ) (hu : ρ ≤ 1/4)
    (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ENNReal.ofReal (linearRate ρ (EntropyTailQuantile.budgetScale B/a)/32) ≤ rareMinimaxRisk μ ρ B ∧
      ENNReal.ofReal (linearRate ρ (confidenceScale B δ/a)/960) ≤ rareConfidenceRadius μ ρ B δ :=
  lower_from_quantile μ hr hu hb hd hd' (fun h => linearRate ρ (h/a)) (fun _ hh => linear_tail μ hm ha hr (by linarith) hh)

theorem intermediate_lower (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ B δ : ℝ}
    (hm : ExactPowerLaw μ α a) (hα : 0 < α) (ha : 0 < a) (hr : 0 < ρ) (hu : ρ ≤ 1/4)
    (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ENNReal.ofReal (intermediateRate α ρ (EntropyTailQuantile.budgetScale B/a)/32) ≤ rareMinimaxRisk μ ρ B ∧
      ENNReal.ofReal (intermediateRate α ρ (confidenceScale B δ/a)/960) ≤ rareConfidenceRadius μ ρ B δ :=
  lower_from_quantile μ hr hu hb hd hd' (fun h => intermediateRate α ρ (h/a))
    (fun _ hh => intermediate_tail μ hm hα ha hr (by linarith) hh)

end ThresholdHC.ShiftedPower
