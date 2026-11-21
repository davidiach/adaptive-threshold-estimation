import ThresholdHC.ProgramFactor.Specification
import ThresholdHC.ProgramFactor.Modulus
import ThresholdHC.Genie.InfiniteComparison
import ThresholdHC.SquareRootCap.Full

/-! The factor 3√7/2 between the infinite stopping program and minimax RMS
risk, and its finite-cap corollaries with the factor 3√7, stated against the
specification. -/
noncomputable section
namespace ThresholdHC.ProgramFactor
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie ThresholdHC.RareAboveTwo

theorem two_mul_factor :
    2*ENNReal.ofReal (3*Real.sqrt 7/2) = ENNReal.ofReal (3*Real.sqrt 7) := by
  rw [← ENNReal.ofReal_ofNat 2,← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

theorem infinite_program_factor : InfiniteProgramFactorStatement := by
  intro μ _ ρ B hρ hρhalf hB
  exact ⟨(infinite_program_comparison μ ρ B hρ hρhalf hB).1,
    infinite_program_upper_factor μ ρ B hρ hρhalf hB⟩

theorem four_ninths_factor : FourNinthsFactorStatement := by
  intro μ _ ρ B hρ hρhalf hB N hcap
  have hN : 0 < N := by exact_mod_cast (show 0 < (N:ℝ) by linarith)
  have h2 := (ThresholdHC.SquareRootCap.four_ninths_cap μ hρ hρhalf hB N hcap).1
  have hg := (genieValue_le_infinite μ ρ B hρ hρhalf hB N hN).trans
    (infinite_program_upper_factor μ ρ B hρ hρhalf hB)
  refine ⟨minimax_le_program μ hρ hρhalf hB.le N hN,?_⟩
  calc
    _ ≤ 2*genieValue μ ρ B N := h2
    _ ≤ 2*(ENNReal.ofReal (3*Real.sqrt 7/2)*rareMinimaxRisk μ ρ B) := mul_le_mul_right hg 2
    _ = _ := by rw [← mul_assoc,two_mul_factor]

theorem genie_test_factor : GenieTestFactorStatement := by
  intro μ _ ρ B hρ hρhalf hB N hN U L hU hL hUL
  have hg := (hL.trans (genieValue_le_infinite μ ρ B hρ hρhalf hB N hN)).trans
    (infinite_program_upper_factor μ ρ B hρ hρhalf hB)
  refine ⟨(minimax_le_program μ hρ hρhalf hB.le N hN).trans hU,?_⟩
  calc
    _ ≤ 2*L := hUL
    _ ≤ 2*(ENNReal.ofReal (3*Real.sqrt 7/2)*rareMinimaxRisk μ ρ B) := mul_le_mul_right hg 2
    _ = _ := by rw [← mul_assoc,two_mul_factor]

/-- The minimax risk is positive and finite in the model. -/
theorem rareMinimaxRisk_pos_lt_top (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}
    (hρ : 0 < ρ) (hρh : ρ ≤ 1/2) (hB : 0 < B) :
    0 < rareMinimaxRisk μ ρ B ∧ rareMinimaxRisk μ ρ B < ⊤ := by
  constructor
  · have hg := genieValue_positive μ ρ B hρ (by linarith) 1
    have hb := (genie_risk_bracket μ ρ B hρ hρh hB 1 (by norm_num)).1
    have : 0 < genieValue μ ρ B 1/8 := ENNReal.div_pos hg.ne' (by norm_num)
    exact this.trans_le hb
  · have h1 := minimax_le_program μ hρ hρh hB.le 1 (by norm_num)
    have h2 := programSquared_finite μ hρ.le hB.le 1
    refine h1.trans_lt ?_
    unfold programValue
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.ne

theorem factor_lt_eight : ENNReal.ofReal (3 * Real.sqrt 7) < 8 := by
  have h : Real.sqrt 7 < 8/3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [show (8:ℝ≥0∞) = ENNReal.ofReal 8 by simp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by linarith)

theorem below_eight : BelowEightStatement := by
  intro μ _ ρ B hρ hρh hB
  obtain ⟨hpos, htop⟩ := rareMinimaxRisk_pos_lt_top μ hρ hρh hB
  exact ENNReal.mul_lt_mul_left hpos.ne' htop.ne factor_lt_eight

end ThresholdHC.ProgramFactor
