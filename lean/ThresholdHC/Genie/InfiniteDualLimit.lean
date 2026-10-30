import ThresholdHC.Genie.CapMonotonicity
import ThresholdHC.Genie.Model

/-! Infimum identities for the extended-real dual and primal objectives.
These retain zero information and infinite information without exceptions. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem dualRatio_antitone (μ : Measure Gap) (B : ℝ) (Q : FourPriors) :
    Antitone (fun N => dualRatio μ B N Q) := by
  intro N M hNM
  exact ENNReal.div_le_div_left (add_le_add le_rfl
    (mul_le_mul_right (informationRatio_mono μ Q hNM) (ENNReal.ofReal B))) _

theorem infiniteDualRatio_eq_iInf (μ : Measure Gap) (B : ℝ) (Q : FourPriors) :
    infiniteDualRatio μ B Q = ⨅ N : ℕ, dualRatio μ B (N+1) Q := by
  unfold infiniteDualRatio infiniteInformationRatio dualRatio
  rw [ENNReal.mul_iSup,ENNReal.add_iSup,div_eq_mul_inv,ENNReal.inv_iSup,
    ENNReal.mul_iInf (fun h => (ENNReal.pow_ne_top ENNReal.ofReal_ne_top h).elim)]
  rfl

theorem infiniteProgramValue_sq (μ : Measure Gap) (ρ B : ℝ) :
    infiniteProgramValue μ ρ B ^ 2 = ⨅ N : ℕ, programSquared μ ρ B (N+1) := by
  rw [infiniteProgramValue,← ENNReal.rpow_two,
    ENNReal.iInf_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
  apply iInf_congr
  intro N
  rw [programValue,← ENNReal.rpow_mul]
  norm_num

end ThresholdHC.Genie
