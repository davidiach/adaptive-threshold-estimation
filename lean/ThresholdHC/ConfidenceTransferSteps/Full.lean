import ThresholdHC.ConfidenceTransferSteps.Lower
import ThresholdHC.ConfidenceTransferSteps.Upper

/-! The three targets of `Specification.lean`: note (17) for every gap law, the
law-independent hard-cap family of the remark after note (22), and note (22)
under both budget conventions. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceTransferSteps
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- Note (17): `r^exp(B,δ) ≥ Ψ(√(ℓ/B))/8192`. -/
theorem psi_confidence_null : PsiConfidenceNullStatement :=
  psi_confidence_null_proof

/-- The remark after note (22): one hard-cap family over the power-margin class. -/
theorem above_two_confidence_family : AboveTwoConfidenceFamilyStatement :=
  above_two_confidence_family_proof

/-- Note (22) under both budget conventions. -/
theorem above_two_confidence : AboveTwoConfidenceStatement := by
  intro α hα
  obtain ⟨C, hC, hfam⟩ := above_two_confidence_family α hα
  refine ⟨C, hC, ?_⟩
  intro a ρ B δ ha ha' hρ hρ4 hB hδ hδ' μ _ hμ z
  refine ⟨exact_power_confidence_lower μ ha hρ hρ4 hB hδ hδ' hμ,
    ThresholdHC.ConfidenceProgram.expected_confidence_le_hard μ hB.le, ?_⟩
  obtain ⟨R, mR, A, hcap, hA⟩ := hfam a ρ B δ ha ha' hρ hρ4 hB hδ hδ'
  obtain ⟨_, hf⟩ := hA μ (exactPower_margin μ α a hμ)
  have hz : 0 ≤ z := le_min hρ.le (by positivity)
  exact sInf_le ⟨R, mR, A, C*z, mul_nonneg hC.le hz, hcap, hf, rfl⟩

end ThresholdHC.ConfidenceTransferSteps
