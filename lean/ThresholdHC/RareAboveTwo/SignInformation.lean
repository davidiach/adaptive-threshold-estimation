import ThresholdHC.RareAboveTwo.PathInformation
noncomputable section
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy
theorem sign_kl_bound (d a : ℝ) (hd : 0 < d) (hda : d ≤ a) (ha : a ≤ 1/4) :
    klB (1/2-d) (1/2+d) ≤ 32*a^2 := by
  have hb := binary_kl_le_chisq (1/2-d) (1/2+d) (by linarith) (by linarith) (by linarith) (by linarith)
  have hden : 0 < (1/2+d)*(1-(1/2+d)) := by nlinarith
  apply hb.trans
  apply (div_le_iff₀ hden).2
  have hd2 : d^2 ≤ a^2 := by nlinarith
  have ha0 : 0 ≤ a := by linarith
  have hsmall : d^2 ≤ (1/16 : ℝ) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hsmall (sq_nonneg a)
  nlinarith only [hd2,hh,sq_nonneg a]

end ThresholdHC.RareAboveTwo
