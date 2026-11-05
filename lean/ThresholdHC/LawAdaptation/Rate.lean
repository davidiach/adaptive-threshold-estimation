import ThresholdHC.Anytime.Width

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.LawAdaptation
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.Anytime

theorem inflation_mono_budget {b B δ : ℝ} (hb : 0 ≤ b) (hle : b ≤ B) :
    inflation b δ ≤ inflation B δ := by
  have hlog : logBudget b ≤ logBudget B :=
    div_le_div_of_nonneg_right
      (log_le_log (by linarith : (0:ℝ) < 1+b) (by linarith))
      (log_pos (by norm_num : (1:ℝ)<2)).le
  have hp : 0 < 2+logBudget b := by have h := logBudget_nonneg hb; linarith
  have h := log_le_log hp (add_le_add (le_refl 2) hlog)
  unfold inflation
  linarith

theorem inflation_half_failure {B δ : ℝ} (hB : 0 ≤ B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    inflation B (δ/2) ≤ 2*inflation B δ := by
  have he : log (1/(δ/2)) = log (1/δ)+log 2 := by
    rw [show 1/(δ/2) = (1/δ)*2 by ring,
      log_mul (one_div_ne_zero hd.ne') (by norm_num)]
  have hl : log 2 ≤ log (1/δ) := log_le_log (by norm_num)
    ((le_div_iff₀ hd).mpr (by linarith))
  have hi := inflation_ge_log (δ := δ) hB
  unfold inflation at *
  rw [he]
  linarith

/-- The pilot only costs a factor two in the rate once the total budget is
at least twice its deterministic cap; the failure allowance is halved. -/
theorem delayed_selection (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ)
    {H B δ : ℝ} (hH : 0 ≤ H) (hB : 0 < B) (hHB : 2*H ≤ B)
    (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    selection μ ρ ((B-H)/inflation (B-H) (δ/2)) ≤
      2 * selection μ ρ (B/inflation B δ) := by
  let L := inflation B δ
  let L' := inflation (B-H) (δ/2)
  let β := B/L
  have ht : 0 < B-H := by linarith
  have hL : 0 < L := inflation_pos hB.le hd hd'
  have hL' : 0 < L' := inflation_pos ht.le (by linarith) (by linarith)
  have hLL : L' ≤ 2*L :=
    (inflation_mono_budget ht.le (by linarith : B-H ≤ B)).trans
      (inflation_half_failure hB.le hd hd')
  have hb : 0 < β := div_pos hB hL
  have hquarter : β/4 ≤ (B-H)/L' := by
    calc
      β/4 = (B/2)/(2*L) := by dsimp [β]; ring
      _ ≤ (B-H)/(2*L) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left ht.le hL' hLL
  have hm := selection_antitone μ ρ (by positivity : 0 < β/4) hquarter
  have hs := ThresholdHC.HardBudget.selection_budget_scale μ ρ
    (by positivity : 0 < β/4) (by linarith : β/4 ≤ β)
  have he : sqrt (β/(β/4)) = (2:ℝ) := by field_simp; norm_num
  rw [he] at hs
  simpa only [ENNReal.ofReal_ofNat] using hm.trans hs

end ThresholdHC.LawAdaptation

