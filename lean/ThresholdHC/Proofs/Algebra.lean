import ThresholdHC.Statements

namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory

private lemma posterior_den_pos (η L : ℝ) (hη : 0 ≤ η) (hlt : η < 1/2)
    (hL : 0 < L) : 0 < L + (1/4 - η ^ 2) * (L - 1) ^ 2 := by
  have h : 0 ≤ 1/4 - η ^ 2 := by nlinarith
  positivity

theorem posterior_identity : ThresholdHC.Targets.posterior_identity := by
  intro η L hη hlt hL
  have ha : 0 < 1/2 - η := by linarith
  have hb : 0 < 1/2 + η := by linarith
  have hda : (1/2 - η) + (1/2 + η) * L ≠ 0 := ne_of_gt (by positivity)
  have hdb : (1/2 + η) + (1/2 - η) * L ≠ 0 := ne_of_gt (by positivity)
  have hdc := ne_of_gt (posterior_den_pos η L hη hlt hL)
  dsimp [rhoPlus, rhoMinus]
  rw [div_sub_div _ _ hda hdb]
  apply (div_eq_div_iff (mul_ne_zero hda hdb) hdc).2
  ring

theorem posterior_diff_le : ThresholdHC.Targets.posterior_diff_le := by
  intro η L hη hlt hL
  rw [posterior_identity η L hη hlt hL]
  apply (div_le_iff₀ (posterior_den_pos η L hη hlt hL)).2
  have ha : 0 ≤ 1/4 - η ^ 2 := by nlinarith
  have hx := mul_nonneg (mul_nonneg (show 0 ≤ 2 * η by positivity) ha) (sq_nonneg (L-1))
  nlinarith

theorem posterior_mem : ThresholdHC.Targets.posterior_mem := by
  intro η L hη hlt hL
  have ha : 0 < 1/2 - η := by linarith
  have hb : 0 < 1/2 + η := by linarith
  have hda : 0 < (1/2 - η) + (1/2 + η) * L := by positivity
  have hdb : 0 < (1/2 + η) + (1/2 - η) * L := by positivity
  refine ⟨by dsimp [rhoMinus]; positivity, ?_, ?_⟩
  · have hdiff : 0 ≤ rhoPlus η L - rhoMinus η L := by
      rw [posterior_identity η L hη hlt hL]
      exact div_nonneg (by positivity) (le_of_lt (posterior_den_pos η L hη hlt hL))
    linarith
  · dsimp [rhoPlus]
    apply (div_lt_one hda).2
    linarith

theorem pred_variance_ge : ThresholdHC.Targets.pred_variance_ge := by
  intro d ρ hd hdlt
  have h : 0 ≤ 1 - 4 * d ^ 2 := by nlinarith
  have hp := mul_nonneg h (sq_nonneg (ρ - 1/2))
  dsimp [pred]
  nlinarith

theorem ratio_bound : ThresholdHC.Targets.ratio_bound := by
  intro a b L ha hb hL
  have hp : 0 < (b + a * L) ^ 2 := by positivity
  have hq : 0 < 4 * a * b := by positivity
  apply (div_le_div_iff₀ hp hq).2
  nlinarith [sq_nonneg (b - a * L)]

end ThresholdHC.Proofs
