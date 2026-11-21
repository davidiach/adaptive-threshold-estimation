import ThresholdHC.ConfidenceTransferSteps.Specification
import ThresholdHC.PsiNull.Full
import ThresholdHC.ConfidenceLocalization.ConfidenceRate
import ThresholdHC.RareAboveTwo.Psi
import ThresholdHC.Confidence.Lower

/-! The confidence-side lower route of the note: equation (17) for every gap
law, and the lower half of equation (22) for an exact power law.

`psi_confidence_null_proof` repeats the arithmetic of `PsiNull.psi_budget_lower` at the
confidence resolution `h = √(ℓ/B)`: Proposition `prop:psi-null` with `b = Ψ/64`
gives the null-work obstruction with `J = (15Ψ/16)² B/(192ℓ)`, so
`min{b, √(Jℓ/B)} = Ψ/64`, and the common-pair confidence transfer
`minimax_confidence_of_obstruction` (constant `1/128`) gives `Ψ/8192`. The case
`Ψ = 0` is trivial. The power-law lower half uses only the support `(0,a]` of the
exact law, through `rarePsi_supported_lower`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceTransferSteps
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.ConfidenceLocalization
  ThresholdHC.ObservableSimulation

/-- Note (17). -/
theorem psi_confidence_null_proof : PsiConfidenceNullStatement := by
  intro μ _ ρ B δ hρ hρ4 hB hδ hδ'
  have hℓ := ThresholdHC.Confidence.confidence_log_pos hδ hδ'
  set h := ThresholdHC.Confidence.confidenceScale B δ with hh
  have hpos : 0 < h := ThresholdHC.Confidence.confidenceScale_pos hB hδ hδ'
  have hle : rarePsi μ ρ h ≤ ENNReal.ofReal ρ :=
    iSup₂_le fun v hv => ENNReal.ofReal_le_ofReal (rareObjective_le_rarity μ ρ h hpos.le v hv)
  have hfin : rarePsi μ ρ h ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  set Ψ := (rarePsi μ ρ h).toReal with hΨ
  have hΨρ : Ψ ≤ ρ := ENNReal.toReal_le_of_le_ofReal hρ.le hle
  have hΨ0 : 0 ≤ Ψ := ENNReal.toReal_nonneg
  have heq : rarePsi μ ρ h = ENNReal.ofReal Ψ := (ENNReal.ofReal_toReal hfin).symm
  rcases hΨ0.eq_or_lt with h0 | h0
  · rw [heq, ← h0]; simp
  have hb : 0 < Ψ/64 := by positivity
  have hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ (Ψ/64)
      ((max (Ψ - 4*(Ψ/64)) 0)^2 / (192*h^2)) :=
    ThresholdHC.PsiNull.psi_null μ ρ (Ψ/64) h hρ hρ4 hb.le (by linarith) hpos
  have hh2 : h^2 = Real.log (1/δ)/B := by
    rw [hh]; exact Real.sq_sqrt (div_pos hℓ hB).le
  have hJ : (max (Ψ - 4*(Ψ/64)) 0)^2 / (192*h^2) =
      (15*Ψ/16)^2 * B / (192*Real.log (1/δ)) := by
    rw [max_eq_left (by linarith), hh2]
    field_simp
    ring
  rw [hJ] at hobs
  have hJpos : 0 < (15*Ψ/16)^2 * B / (192*Real.log (1/δ)) := by positivity
  have hm := minimax_confidence_of_obstruction μ hρ hρ4 hb hJpos hB hδ hδ' hobs
  have hmin : min (Ψ/64)
      (Real.sqrt ((15*Ψ/16)^2 * B / (192*Real.log (1/δ)) * Real.log (1/δ) / B)) = Ψ/64 := by
    apply min_eq_left
    apply Real.le_sqrt_of_sq_le
    rw [show (15*Ψ/16)^2 * B / (192*Real.log (1/δ)) * Real.log (1/δ) / B = (15*Ψ/16)^2/192 by
      field_simp]
    nlinarith
  rw [hmin] at hm
  rw [heq, ← ENNReal.ofReal_mul (by norm_num)]
  convert hm using 2
  ring

/-- The resolution `√(ℓ/B)` times `√ρ/a` is the rate's second argument. -/
theorem confidence_resolution_rate {a ρ B δ : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4) :
    ThresholdHC.Confidence.confidenceScale B δ * Real.sqrt ρ / a =
      Real.sqrt (ρ * Real.log (1/δ)) / (a * Real.sqrt B) := by
  have hℓ := ThresholdHC.Confidence.confidence_log_pos hδ hδ'
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  unfold ThresholdHC.Confidence.confidenceScale
  rw [Real.sqrt_div hℓ.le, Real.sqrt_mul hρ]
  rcases eq_or_ne a 0 with ha | ha
  · simp [ha]
  field_simp

/-- The lower half of note (22). It needs only the support `(0,a]` of the
exact law, not the exponent. -/
theorem exact_power_confidence_lower (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ B δ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4) (hμ : ExactPowerLaw μ α a) :
    ENNReal.ofReal (min ρ (Real.sqrt (ρ * Real.log (1/δ)) / (a * Real.sqrt B)) / 8192) ≤
      ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ := by
  have hh := ThresholdHC.Confidence.confidenceScale_pos hB hδ hδ'
  have hlow := rarePsi_supported_lower μ a ρ (ThresholdHC.Confidence.confidenceScale B δ) ha
    hρ.le (by linarith) hh.le (exactPower_support μ α a ha hμ)
  rw [confidence_resolution_rate hρ.le hB hδ hδ'] at hlow
  have hz : 0 ≤ min ρ (Real.sqrt (ρ * Real.log (1/δ)) / (a * Real.sqrt B)) :=
    le_min hρ.le (by positivity)
  rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (by norm_num)]
  apply le_trans _ (psi_confidence_null_proof μ ρ B δ hρ hρ4 hB hδ hδ')
  rw [show ((8192:ℝ))⁻¹ = 1/8192 by norm_num]
  gcongr

end ThresholdHC.ConfidenceTransferSteps
