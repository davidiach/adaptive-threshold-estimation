import ThresholdHC.EntropyTailLower.EntropyPacking

noncomputable section
namespace ThresholdHC.EntropyTailLower
open Real ThresholdHC.EntropyTailQuantile

theorem packed_gap_entropy_scale (lam G c n b : ℝ) (hlam : 0 ≤ lam) (hc : 0 ≤ c)
    (hG : G ≤ 4*c*n*(1+log n)) (hb : lam*n*(1+log n)/16 ≤ b) :
    lam*G ≤ 64*c*b := by
  have h1 := mul_le_mul_of_nonneg_left hG hlam
  have h2 := mul_le_mul_of_nonneg_left hb (show 0 ≤ 64*c by positivity)
  nlinarith only [h1,h2]

theorem packed_saturation_numeric (τ w a c b lam G : ℝ) (ha : 0 < a)
    (hc : 0 ≤ c) (hb : 0 ≤ b) (hlam : 0 ≤ lam) (hG : 0 ≤ G)
    (hτ : c*a^2 ≤ τ) (hw : c*b^2 ≤ w) (hscale : lam*G ≤ 64*c*b) :
    lam^2*G^2 ≤ 4096*(τ*w/a^2) := by
  have hτ0 : 0 ≤ τ := (mul_nonneg hc (sq_nonneg a)).trans hτ
  have hm := mul_le_mul hτ hw (mul_nonneg hc (sq_nonneg b)) hτ0
  have hq : c^2*b^2 ≤ τ*w/a^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
    nlinarith only [hm]
  have hs := (sq_le_sq₀ (mul_nonneg hlam hG) (show 0 ≤ 64*c*b by positivity)).mpr hscale
  nlinarith only [hs,hq]

theorem packed_rarity_cap (τ w a G θ : ℝ) (hG : 0 < G) (hw : 0 ≤ w)
    (hwτ : w ≤ τ) (hGscale : τ/a^2 ≤ G)
    (hθ : θ*G ≤ (τ*w/a^2)/4) : θ ≤ τ/4 := by
  have h := mul_le_mul_of_nonneg_right hGscale (show 0 ≤ w/4 by positivity)
  have hh : θ*G ≤ G*(w/4) := by
    calc
      θ*G ≤ (τ*w/a^2)/4 := hθ
      _ = (τ/a^2)*(w/4) := by ring
      _ ≤ G*(w/4) := h
  have hθw : θ ≤ w/4 := by nlinarith only [hh,hG]
  linarith only [hθw,hwτ]

theorem packed_min_cost (θ G B : ℝ) (hθ : 0 ≤ θ) (hG : 0 ≤ G) (hB : 0 < B) :
    0 ≤ min θ (sqrt (θ*G/B)) ∧ min θ (sqrt (θ*G/B)) ≤ θ ∧
      (min θ (sqrt (θ*G/B)))^2*B ≤ θ*G := by
  have hu : 0 ≤ min θ (sqrt (θ*G/B)) := le_min hθ (sqrt_nonneg _)
  refine ⟨hu,min_le_left _ _,?_⟩
  have hs := (sq_le_sq₀ hu (sqrt_nonneg (θ*G/B))).mpr (min_le_right θ (sqrt (θ*G/B)))
  rw [sq_sqrt (div_nonneg (mul_nonneg hθ hG) hB.le)] at hs
  have hm := mul_le_mul_of_nonneg_right hs hB.le
  rwa [div_mul_cancel₀ _ hB.ne'] at hm

end ThresholdHC.EntropyTailLower
