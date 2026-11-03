import ThresholdHC.EntropyTailLower.CertificateLower

/-! The matching lower half in the frozen observable experiment. -/
noncomputable section
namespace ThresholdHC.EntropyTail

theorem entropy_tail_lower : EntropyTailLowerStatement :=
  EntropyTailLower.entropy_tail_lower_iff_certificate_lower.mpr EntropyTailLower.certificate_lower

end ThresholdHC.EntropyTail
