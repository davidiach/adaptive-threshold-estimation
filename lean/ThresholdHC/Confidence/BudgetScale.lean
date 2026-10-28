import ThresholdHC.Confidence.Lower
import ThresholdHC.BlindUpper.BudgetChoice

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Confidence
open ThresholdHC.Tier6 ThresholdHC.BlindUpper

def confidenceRepetitions (δ : ℝ) : ℕ := ⌈2*Real.log (1/δ)⌉₊
def confidenceCount (δ : ℝ) : ℕ := 2*confidenceRepetitions δ+1

theorem confidence_log_ge_one {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1/4) :
    1 ≤ Real.log (1/δ) := by
  have hr : (4 : ℝ) ≤ 1/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hr
  have hfour : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  rw [hfour] at hl
  linarith [Real.log_two_gt_d9]

theorem confidenceCount_pos (δ : ℝ) : 0 < confidenceCount δ := by
  unfold confidenceCount
  omega

theorem confidenceCount_le {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1/4) :
    (confidenceCount δ : ℝ) ≤ 7*Real.log (1/δ) := by
  have hl := confidence_log_ge_one hδ hδle
  have hm := Nat.ceil_lt_add_one (show 0 ≤ 2*Real.log (1/δ) by linarith)
  change (confidenceRepetitions δ : ℝ) < 2*Real.log (1/δ)+1 at hm
  unfold confidenceCount
  push_cast
  linarith

theorem confidence_amplification_level {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1/4) :
    (1/2 : ℝ≥0∞)^(confidenceRepetitions δ) ≤ ENNReal.ofReal δ := by
  have hm : 2*Real.log (1/δ) ≤ (confidenceRepetitions δ : ℝ) := Nat.le_ceil _
  have hl := confidence_log_pos hδ hδle
  have htwo : (1/2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hd : Real.log δ = -Real.log (1/δ) := by rw [one_div,Real.log_inv,neg_neg]
  have hp : (1/2 : ℝ)^(confidenceRepetitions δ) ≤ δ := by
    apply (Real.log_le_log_iff (by positivity) hδ).mp
    rw [Real.log_pow,hhalf,hd]
    have hm0 : 0 ≤ (confidenceRepetitions δ : ℝ) := Nat.cast_nonneg _
    nlinarith
  have he := ENNReal.ofReal_le_ofReal hp
  simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/2),
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using he

theorem group_scale_le {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδle : δ ≤ 1/4) :
    1/Real.sqrt (B/(confidenceCount δ : ℝ)) ≤ 4*confidenceScale B δ := by
  have hk : 0 < (confidenceCount δ : ℝ) := by exact_mod_cast confidenceCount_pos δ
  have hl := confidence_log_pos hδ hδle
  have hroot : Real.sqrt (confidenceCount δ : ℝ) ≤ 4*Real.sqrt (Real.log (1/δ)) := by
    have hk2 := Real.sq_sqrt hk.le
    have hl2 := Real.sq_sqrt hl.le
    nlinarith [Real.sqrt_nonneg (confidenceCount δ : ℝ), Real.sqrt_nonneg (Real.log (1/δ)),
      confidenceCount_le hδ hδle]
  rw [Real.sqrt_div hB.le,one_div_div,confidenceScale,Real.sqrt_div hl.le]
  calc
    _ ≤ (4*Real.sqrt (Real.log (1/δ)))/Real.sqrt B :=
      div_le_div_of_nonneg_right hroot (Real.sqrt_nonneg B)
    _ = _ := by ring

theorem group_modulus_le (μ : Measure Gap) [IsProbabilityMeasure μ] (B δ : ℝ)
    (hB : 0 < B) (hδ : 0 < δ) (hδle : δ ≤ 1/4) (hg : 4 ≤ B/(confidenceCount δ : ℝ)) :
    modulus μ (1/Real.sqrt ((2 : ℝ)^(budgetLevel (B/(confidenceCount δ : ℝ))))) ≤
      16*modulus μ (confidenceScale B δ) := by
  have hfirst := (modulus_mono μ (by positivity) (budgetLevel_scale _ hg)).trans
    (modulus_quadruple_le μ (by positivity))
  have hsecond := (modulus_mono μ (by positivity) (group_scale_le hB hδ hδle)).trans
    (modulus_quadruple_le μ (confidenceScale_pos hB hδ hδle).le)
  linarith

theorem small_group_radius (μ : Measure Gap) [IsProbabilityMeasure μ] (B δ : ℝ)
    (hB : 0 < B) (hδ : 0 < δ) (hδle : δ ≤ 1/4) (hg : B/(confidenceCount δ : ℝ) < 4) :
    1 ≤ 8192*modulus μ (confidenceScale B δ) := by
  have hk : 0 < (confidenceCount δ : ℝ) := by exact_mod_cast confidenceCount_pos δ
  have hbk : B < 4*(confidenceCount δ : ℝ) := (div_lt_iff₀ hk).mp hg
  have hl := confidence_log_pos hδ hδle
  have hb : B < 28*Real.log (1/δ) := by linarith [confidenceCount_le hδ hδle]
  have hratio : (1/64 : ℝ) ≤ Real.log (1/δ)/B := (le_div_iff₀ hB).mpr (by linarith)
  have hs : (1/8 : ℝ) ≤ confidenceScale B δ := by
    have hsq := Real.sq_sqrt (div_nonneg hl.le hB.le)
    have hpos := confidenceScale_pos hB hδ hδle
    dsimp [confidenceScale] at *
    nlinarith
  have hquarter := modulus_scaling μ (1/4) (1/2) (by norm_num) (by norm_num) (by norm_num)
  rw [modulus_eq_one_of_half_le μ (by norm_num : (1/2 : ℝ) ≤ 1/2)] at hquarter
  norm_num at hquarter
  have hmono := modulus_mono μ (by norm_num : (0 : ℝ) ≤ 1/8) hs
  linarith

end ThresholdHC.Confidence
