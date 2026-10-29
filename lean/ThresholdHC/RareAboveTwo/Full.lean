import ThresholdHC.RareAboveTwo.PowerLaw
import ThresholdHC.RareAboveTwo.Single
import ThresholdHC.RareAboveTwo.Minimax
import ThresholdHC.RareAboveTwo.Psi

/-! The seven frozen statements for the observable alpha > 2 rare-event theory. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo

theorem above_two_theory :
    PowerLawExistenceStatement ∧ RareSingleCoinStatement ∧ RareSupportedLowerStatement ∧
    AboveTwoUpperStatement ∧ AboveTwoMinimaxStatement ∧ AboveTwoPsiStatement ∧ RareNonvacuityStatement :=
  ⟨power_law_exists,rare_single_coin,rare_supported_lower,above_two_upper,
    above_two_minimax,above_two_psi,rare_nonvacuity⟩

end ThresholdHC.RareAboveTwo
