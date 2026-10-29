import ThresholdHC.RareAboveTwo.LowerSeparation
import ThresholdHC.RareAboveTwo.Specification

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ThresholdHC.Tier6
open scoped ENNReal

theorem rare_supported_lower : RareSupportedLowerStatement := by
  refine ⟨1/256,by norm_num,?_⟩
  intro a ρ B ha ha1 hρ hρ1 hB μ _ hsupp R _ A hbudget
  have hB0 : 0 < B := by linarith
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB0
  have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hden : 0 < a*Real.sqrt B := mul_pos ha hsB
  let δ := aboveTwoRate a ρ B/32
  have hrate : 0 < aboveTwoRate a ρ B := lt_min hρ (div_pos hsρ hden)
  have hδ : 0 < δ := div_pos hrate (by norm_num)
  have hδρ : δ ≤ ρ/2 := by
    have h := min_le_left ρ (Real.sqrt ρ/(a*Real.sqrt B))
    change aboveTwoRate a ρ B ≤ ρ at h
    dsimp [δ]; linarith
  have hsmall : δ*(a*Real.sqrt B) ≤ Real.sqrt ρ/32 := by
    have h := (le_div_iff₀ hden).1 (min_le_right ρ (Real.sqrt ρ/(a*Real.sqrt B)))
    change aboveTwoRate a ρ B*(a*Real.sqrt B) ≤ Real.sqrt ρ at h
    dsimp [δ]; nlinarith only [h]
  have hsq := (sq_le_sq₀ (mul_pos hδ hden).le (by positivity : 0 ≤ Real.sqrt ρ/32)).2 hsmall
  simp only [mul_pow,div_pow,Real.sq_sqrt hB0.le,Real.sq_sqrt hρ.le] at hsq
  have hinfo : 64*δ^2*a^2*B ≤ ρ/8 := by nlinarith only [hsq,hρ.le]
  have h := rare_lower_at_separation μ A a ρ B δ ha1 hsupp hρ hρ1 hB0.le hδ hδρ hinfo hbudget
  convert h using 1
  congr 1
  dsimp [δ]; ring

end ThresholdHC.RareAboveTwo
