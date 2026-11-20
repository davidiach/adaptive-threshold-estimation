import ThresholdHC.PaperCorollaries.Transfer
import ThresholdHC.PaperCorollaries.PsiSequence

/-! Corollaries and remarks that the guides state as paper arguments on top of
Lean-checked theorems: the RMS constants `1/6` and `12` under a stochastic
envelope, the coefficient `1/6` under a pathwise cap, and the paper's divergence
sequence for `Ψ` at the quadratic law. -/
noncomputable section
namespace ThresholdHC.PaperCorollaries
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem envelope_rms : EnvelopeRMSStatement := envelope_rms_bounds

theorem hard_sharp_lower : HardSharpLowerStatement := hard_lower_bound

theorem psi_sequence : PsiSequenceStatement := by
  intro μ _ hm n hn
  exact psi_sequence_bounds μ hm n hn

end ThresholdHC.PaperCorollaries
