import ThresholdHC.SmoothDensity.Envelope
import ThresholdHC.SmoothDensity.Lower

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.SmoothDensity
open ThresholdHC.Tier6 ThresholdHC.Confidence ThresholdHC.RareAboveTwo

def upperBudget (M ε δ : ℝ) : ℝ :=
  (65536 * M) ^ 2 * (ε ^ 2)⁻¹ * (Real.log (1 / ε)) ^ 2 * Real.log (1 / δ)

theorem upper_scale_bounds {M ε δ : ℝ} (hM : 1 ≤ M)
    (hε : 0 < ε) (he : ε ≤ Real.exp (-16)) (hδ : 0 < δ) (hd : δ ≤ 1 / 4) :
    1 ≤ upperBudget M ε δ ∧
      0 < confidenceScale (upperBudget M ε δ) δ ∧
      confidenceScale (upperBudget M ε δ) δ < 1 / (2 * M) ∧
      8192 * ((confidenceScale (upperBudget M ε δ) δ / (1 / (2 * M))) *
        (1 + Real.log ((1 / (2 * M)) / confidenceScale (upperBudget M ε δ) δ))) ≤ ε := by
  let L := Real.log (1 / ε)
  let z := ε / (65536 * M * L)
  have hM0 : 0 < M := by linarith
  have hL : 16 ≤ L := by
    have h := Real.log_le_log hε he
    rw [Real.log_exp] at h
    dsimp [L]
    rw [Real.log_div one_ne_zero hε.ne',Real.log_one]
    linarith
  have hL0 : 0 < L := by linarith
  have hε1 : ε ≤ 1 := he.trans ((Real.exp_le_one_iff).mpr (by norm_num))
  have hz : 0 < z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 65536 * M * L)).mpr
    have := mul_le_mul hM hL (by norm_num : (0 : ℝ) ≤ 16) hM0.le
    nlinarith
  have hdlog : 1 ≤ Real.log (1 / δ) := by
    have hratio : (4 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by linarith)
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hratio
    have hfour : 1 ≤ Real.log (4 : ℝ) := by
      have hlog2 : 1 / 2 ≤ Real.log (2 : ℝ) := by
        have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        exact h
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,Real.log_pow]
      norm_num
      linarith
    exact hfour.trans h
  have hB : upperBudget M ε δ = Real.log (1 / δ) / z ^ 2 := by
    dsimp [upperBudget,z,L]
    field_simp
  have hB1 : 1 ≤ upperBudget M ε δ := by
    rw [hB]
    apply (le_div_iff₀ (sq_pos_of_pos hz)).mpr
    nlinarith [sq_nonneg z]
  have hscale : confidenceScale (upperBudget M ε δ) δ = z := by
    rw [confidenceScale,hB,div_div_cancel₀ (ne_of_gt (by linarith : 0 < Real.log (1 / δ)))]
    exact Real.sqrt_sq hz.le
  have hza : z < 1 / (2 * M) := by
    dsimp [z]
    apply (div_lt_div_iff₀ (by positivity : 0 < 65536 * M * L) (by positivity : 0 < 2 * M)).mpr
    have hML : 16 * M ≤ M * L := by
      simpa only [mul_comm M 16] using mul_le_mul_of_nonneg_left hL hM0.le
    nlinarith [mul_le_mul_of_nonneg_right hε1 (by positivity : 0 ≤ 2 * M)]
  refine ⟨hB1,hscale ▸ hz,hscale ▸ hza,?_⟩
  rw [hscale]
  have heq : z / (1 / (2 * M)) = ε / (32768 * L) := by dsimp [z]; field_simp; ring
  have heq' : (1 / (2 * M)) / z = 32768 * L / ε := by dsimp [z]; field_simp; ring
  rw [heq,heq',Real.log_div (by positivity : 32768 * L ≠ 0) hε.ne',
    Real.log_mul (by norm_num : (32768 : ℝ) ≠ 0) hL0.ne']
  have hlogK : Real.log (32768 : ℝ) ≤ 15 := by
    rw [show (32768 : ℝ) = 2 ^ 15 by norm_num,Real.log_pow]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have heL : Real.log ε = -L := by
    dsimp [L]
    rw [Real.log_div one_ne_zero hε.ne',Real.log_one]
    ring
  rw [heL]
  have hf : 1 + (Real.log (32768 : ℝ) + Real.log L - -L) ≤ 4 * L := by linarith
  have hm := mul_le_mul_of_nonneg_left hf (show 0 ≤ 8192 * (ε / (32768 * L)) by positivity)
  have heval : (8192 * (ε / (32768 * L))) * (4 * L) = ε := by field_simp; ring
  rw [heval] at hm
  nlinarith

/-- One law-independent estimator family supplies the matching upper rate
for every model in each smooth class. -/
theorem smooth_confidence_upper (s : ℕ) :
    ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → ℝ → ℝ → AdaptiveEstimator R),
      ∀ M ε δ : ℝ, 1 ≤ M → 0 < ε → ε ≤ Real.exp (-16) → 0 < δ → δ ≤ 1 / 4 →
        FitsClass s M (upperBudget M ε δ) ε δ (rule M ε δ) := by
  obtain ⟨R,mR,rule,h⟩ := ThresholdHC.Envelope.blind_confidence_upper
  refine ⟨R,mR,fun M ε δ => rule (upperBudget M ε δ) δ,?_⟩
  intro M ε δ hM hε he hδ hd μ _ q hq
  obtain ⟨hB,hscale,hscalea,hr⟩ := upper_scale_bounds hM hε he hδ hd
  have hM0 : 0 < M := by linarith
  have ha : 0 < 1 / (2 * M) := by positivity
  have ha1 : 1 / (2 * M) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * M)).mpr
    linarith
  let ν := powerGapLaw 1 (1 / (2 * M)) (by norm_num) ha ha1
  obtain ⟨hw,hc⟩ := h (upperBudget M ε δ) δ hB hδ hd ν μ (smoothModel_envelope hM μ q hq)
  refine ⟨hw q,(failureProbability_mono μ _ q ?_).trans (hc q)⟩
  rw [linear_modulus _ _ ha ha1 hscale hscalea]
  exact hr

end ThresholdHC.SmoothDensity
