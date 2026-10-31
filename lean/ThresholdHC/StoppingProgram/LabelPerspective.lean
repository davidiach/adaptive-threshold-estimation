import ThresholdHC.StoppingProgram.PriorContraction

/-! Information in a binary mixture cannot exceed information in its latent
label. This includes zero likelihoods at either component. -/

noncomputable section
open scoped ENNReal
namespace ThresholdHC.StoppingProgram

theorem perspective_label_bound (a b m δ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : 0 < m) (hm1 : m < 1) :
    perspective (δ*(a-b)) (m*a+(1-m)*b) ≤
      ENNReal.ofReal (δ^2*(a/m+b/(1-m))) := by
  have h1 : perspective a (m*a) = ENNReal.ofReal (a/m) := by
    calc
      _ = ENNReal.ofReal a*perspective 1 m := by
        simpa only [mul_one,mul_comm m a] using perspective_scale 1 m ha
      _ = _ := by
        rw [perspective_pos hm,← ENNReal.ofReal_mul ha]
        congr 1
        ring
  have h2 : perspective (-b) ((1-m)*b) = ENNReal.ofReal (b/(1-m)) := by
    calc
      _ = ENNReal.ofReal b*perspective (-1) (1-m) := by
        simpa only [mul_neg_one,mul_comm (1-m) b] using perspective_scale (-1) (1-m) hb
      _ = _ := by
        rw [perspective_pos (by linarith : 0 < 1-m),← ENNReal.ofReal_mul hb]
        congr 1
        ring
  have hh := perspective_add_le (x := a) (z := -b)
    (mul_nonneg hm.le ha) (mul_nonneg (by linarith : 0 ≤ 1-m) hb)
  rw [h1,h2,← ENNReal.ofReal_add (by positivity) (by positivity)] at hh
  rw [perspective_scale_contrast,ENNReal.ofReal_mul (sq_nonneg δ)]
  exact mul_le_mul_right hh _

end ThresholdHC.StoppingProgram
