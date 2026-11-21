import ThresholdHC.PaperCorollaries.Specification
import ThresholdHC.SharpRMS.Full
import ThresholdHC.UpperScale.Full

/-! The sharp lower coefficient `1/6` and the upper constant `12` in two derived
models.

* Envelope. Every algorithm admitted for the envelope class of `μ` is admitted
  at `μ` itself, so its risk is at least `R_μ(B) ≥ ω_μ(B^{-1/2})/6`. The
  distribution-blind family of `UpperScale` has risk at most `12 ω_ν(B^{-1/2})`
  under every law `ν`, and `ω_ν ≤ ω_μ` below the envelope.
* Hard cap. An algorithm with at most `⌊B⌋` observations on every path also
  meets the expected budget `B`, so `R_μ(B) ≤ R^hard_μ(B)`. -/
noncomputable section
namespace ThresholdHC.PaperCorollaries
open MeasureTheory ThresholdHC.Tier6
open scoped ENNReal

theorem envelope_rms_bounds : EnvelopeRMSStatement := by
  intro μ _ B hB
  constructor
  · apply le_sInf
    rintro t ⟨R, mR, A, hA⟩
    obtain ⟨hw, hr⟩ := hA μ (ThresholdHC.Envelope.within_self μ)
    have hmin : minimaxRisk μ B ≤ maximalRMSRisk μ A := sInf_le ⟨R, mR, A, hw, rfl⟩
    exact (ThresholdHC.SharpRMS.sharp_lower μ B hB).trans (hmin.trans hr)
  · obtain ⟨R, mR, rule, hrule⟩ := ThresholdHC.UpperScale.blind_upper_12
    apply sInf_le
    refine ⟨R, mR, rule B, fun ν _ hν => ⟨(hrule B hB ν).1, (hrule B hB ν).2.trans ?_⟩⟩
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (ThresholdHC.Envelope.modulus_le μ ν hν (by positivity)) (by norm_num)

theorem hard_lower_bound : HardSharpLowerStatement := by
  intro μ _ B hB
  apply le_sInf
  rintro t ⟨R, mR, A, hA, rfl⟩
  exact (ThresholdHC.SharpRMS.sharp_lower μ B hB).trans
    (sInf_le ⟨R, mR, A, fun q => ThresholdHC.HardBudget.pathwise_expected μ A q (by linarith) hA, rfl⟩)

end ThresholdHC.PaperCorollaries
