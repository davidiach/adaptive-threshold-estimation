import ThresholdHC.TwoFlipFeedback.Specification

/-! The risk polynomial of the feedback table on the full feasible triangle.
In the coordinates `δ = 2A` and the target `θ`, the feasible set is
`0 ≤ δ`, `2δ ≤ θ ≤ 4δ`, `θ ≤ 1/4`. The risk is convex in `θ` with second
derivative two, and on each edge it is a convex polynomial in `δ`; each
edge's curvature factor is derived from the certificate's exact edge-risk
coefficients (`full_class-body.tex`, `full_class_certificate.json`), rescaled
to `δ = 2A`, and its identity is checked by `ring`. -/

noncomputable section
namespace ThresholdHC.TwoFlipFeedback

def yTT : ℝ := 26862477375/237281040413
def yTH : ℝ := 3223497285/24696819223
def yHT : ℝ := 1074499095/8589934592
def yHH : ℝ := 22564480995/146053120736

/-- Risk of the feedback table at drift `δ = 2A` and target `θ`. -/
def riskPoly (δ θ : ℝ) : ℝ :=
  (11/16 - δ) * (11/16 - δ) * (yTT - θ)^2 + (11/16 - δ) * (5/16 + δ) * (yTH - θ)^2 +
    27/128 * (yHT - θ)^2 + (13/128 + δ) * (yHH - θ)^2

/-- The mean output at drift `δ`. -/
def riskMean (δ : ℝ) : ℝ :=
  (11/16 - δ) * (11/16 - δ) * yTT + (11/16 - δ) * (5/16 + δ) * yTH +
    27/128 * yHT + (13/128 + δ) * yHH

/-- The internal upper constant, below `15443/10^6`. -/
def upperValue : ℝ := 15442587/1000000000

theorem riskPoly_sub (δ s t : ℝ) :
    riskPoly δ t - riskPoly δ s = (t - s) * (t + s - 2 * riskMean δ) := by
  unfold riskPoly riskMean
  ring

theorem riskPoly_le_max (δ lo hi t : ℝ) (h1 : lo ≤ t) (h2 : t ≤ hi) :
    riskPoly δ t ≤ max (riskPoly δ lo) (riskPoly δ hi) := by
  have e1 := riskPoly_sub δ lo t
  have e2 := riskPoly_sub δ hi t
  by_cases h : t + lo ≤ 2 * riskMean δ
  · have hp : (t - lo) * (t + lo - 2 * riskMean δ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact (show riskPoly δ t ≤ riskPoly δ lo by linarith).trans (le_max_left _ _)
  · have hp : (t - hi) * (t + hi - 2 * riskMean δ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    exact (show riskPoly δ t ≤ riskPoly δ hi by linarith).trans (le_max_right _ _)

theorem vertex_origin : riskPoly 0 0 ≤ upperValue := by
  norm_num [riskPoly, yTT, yTH, yHT, yHH, upperValue]

theorem vertex_steep : riskPoly (1/16) (1/4) ≤ upperValue := by
  norm_num [riskPoly, yTT, yTH, yHT, yHH, upperValue]

theorem vertex_flat : riskPoly (1/8) (1/4) ≤ upperValue := by
  norm_num [riskPoly, yTT, yTH, yHT, yHH, upperValue]

private theorem chord_bound (a b δ Ea Eb L V e : ℝ) (hab : a < b) (h1 : a ≤ δ) (h2 : δ ≤ b)
    (ha : Ea ≤ V) (hb : Eb ≤ V) (hL : 0 ≤ L)
    (he : e = ((b - δ) * Ea + (δ - a) * Eb) / (b - a) + (δ - a) * (δ - b) * L) : e ≤ V := by
  have hc : ((b - δ) * Ea + (δ - a) * Eb) / (b - a) ≤ V := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left ha (sub_nonneg.2 h2),
      mul_le_mul_of_nonneg_left hb (sub_nonneg.2 h1)]
  have hp : (δ - a) * (δ - b) * L ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) hL
  linarith

/-- The edge `θ = 2δ` (no positive signs at the gap `1/8`). -/
theorem edge_low (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1/8) : riskPoly δ (2 * δ) ≤ upperValue := by
  apply chord_bound 0 (1/8) δ (riskPoly 0 0) (riskPoly (1/8) (1/4))
    ((405828167763912796320/5860086960125218259099) * δ +
      4781484962053714491816716022144952632289795739372440661/
        1253888649819768558707573974892644566040593802134971384) upperValue _
    (by norm_num) h0 h1 vertex_origin vertex_flat
    (add_nonneg (mul_nonneg (by norm_num) h0) (by norm_num))
  unfold riskPoly yTT yTH yHT yHH
  ring

/-- The edge `θ = 4δ` (no positive signs at the gap `1/4`). -/
theorem edge_high (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1/16) : riskPoly δ (4 * δ) ≤ upperValue := by
  apply chord_bound 0 (1/16) δ (riskPoly 0 0) (riskPoly (1/16) (1/4))
    ((811656335527825592640/5860086960125218259099) * δ +
      9794257921073796616473245780741554211349660107699144677/
        626944324909884279353786987446322283020296901067485692) upperValue _
    (by norm_num) h0 h1 vertex_origin vertex_steep
    (add_nonneg (mul_nonneg (by norm_num) h0) (by norm_num))
  unfold riskPoly yTT yTH yHT yHH
  ring

/-- The rarity edge `θ = 1/4`. -/
theorem edge_top (δ : ℝ) (h0 : 1/16 ≤ δ) (h1 : δ ≤ 1/8) : riskPoly δ (1/4) ≤ upperValue := by
  apply chord_bound (1/16) (1/8) δ (riskPoly (1/16) (1/4)) (riskPoly (1/8) (1/4))
    (152363208398407100162608659589973205378060/34340619180229621374615582110491784296291801)
    upperValue _ (by norm_num) h0 h1 vertex_steep vertex_flat (by norm_num)
  unfold riskPoly yTT yTH yHT yHH
  ring

/-- The risk polynomial is at most `upperValue` on the whole feasible triangle. -/
theorem riskPoly_le (δ θ : ℝ) (h0 : 0 ≤ δ) (hlo : 2 * δ ≤ θ) (hhi : θ ≤ 4 * δ) (htop : θ ≤ 1/4) :
    riskPoly δ θ ≤ upperValue := by
  rcases le_total δ (1/16) with h | h
  · refine (riskPoly_le_max δ (2 * δ) (4 * δ) θ hlo hhi).trans (max_le ?_ ?_)
    · exact edge_low δ h0 (by linarith)
    · exact edge_high δ h0 h
  · refine (riskPoly_le_max δ (2 * δ) (1/4) θ hlo htop).trans (max_le ?_ ?_)
    · exact edge_low δ h0 (by linarith)
    · exact edge_top δ h (by linarith)

end ThresholdHC.TwoFlipFeedback
