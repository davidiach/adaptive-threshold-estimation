import ThresholdHC.RareAboveTwo.Lower
import ThresholdHC.RareAboveTwo.Budget

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ThresholdHC.Tier6
open scoped ENNReal

theorem above_two_minimax : AboveTwoMinimaxStatement := by
  obtain ⟨c,hc,hlower⟩ := rare_supported_lower
  refine ⟨c,hc,?_⟩
  intro α hα
  obtain ⟨C,hC,R,mR,rule,hupper⟩ := above_two_upper α hα
  letI := mR
  refine ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro a ρ B ha ha1 hρ hρ1 hB μ _ hpower
  constructor
  · apply le_sInf
    rintro t ⟨S,mS,A,hbudget,rfl⟩
    letI := mS
    exact hlower a ρ B ha ha1 hρ hρ1 hB μ (exactPower_support μ α a ha hpower) S A hbudget
  · obtain ⟨hbudget,hrisk⟩ := hupper a ρ B ha ha1 hρ hρ1 hB μ (exactPower_margin μ α a hpower)
    have hmin : rareMinimaxRisk μ ρ B ≤ rareRisk μ (rule a ρ B) ρ :=
      sInf_le ⟨R,mR,rule a ρ B,hbudget,rfl⟩
    apply hmin.trans (hrisk.trans (ENNReal.ofReal_le_ofReal ?_))
    have hM : 0 ≤ max 1 C := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
    have ht : 0 ≤ Real.sqrt ρ/(a*Real.sqrt B) := by positivity
    rw [aboveTwoRate,mul_min_of_nonneg _ _ hM]
    apply le_min
    · exact (min_le_left _ _).trans (by nlinarith [le_max_left (1 : ℝ) C])
    · have hb := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C) ht
      exact (min_le_right _ _).trans (by simpa only [mul_div_assoc] using hb)

end ThresholdHC.RareAboveTwo
