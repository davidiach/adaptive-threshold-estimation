import ThresholdHC.StoppingProgram.MidpointInformation
import ThresholdHC.Tier6.RiskReduction

/-! A positive contraction scale giving the paper's three-eighths testing
constant, and the real square-root form of the midpoint dual ratio. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)

theorem contraction_scale (x : ℝ) (hx : 0 ≤ x) :
    let s := 1/Real.sqrt (4+x)
    (0 ≤ s ∧ s ≤ 1) ∧ s^2*x ≤ 1 := by
  have hroot : 0 < Real.sqrt (4+x) := Real.sqrt_pos.mpr (by linarith)
  have hsq := Real.sq_sqrt (show 0 ≤ 4+x by linarith)
  have hroot1 : 1 ≤ Real.sqrt (4+x) := by nlinarith
  dsimp only
  refine ⟨⟨by positivity,(div_le_one hroot).mpr hroot1⟩,?_⟩
  rw [div_pow,one_pow,hsq]
  rw [div_mul_eq_mul_div,one_mul]
  exact (div_le_one (by linarith : 0 < 4+x)).mpr (by linarith)

theorem midpoint_dual_root (μ : Measure Gap) [IsProbabilityMeasure μ]
    (B : ℝ) (hB : 0 ≤ B) (N : ℕ) (q r : SignLaw)
    (hgap : signMean μ q.val ≤ signMean μ r.val) :
    dualRatio μ B N (midpointFourPriors q r) ^ (1/(2:ℝ)) =
      ENNReal.ofReal ((signMean μ r.val-signMean μ q.val)/
        Real.sqrt (4+B*(informationRatio μ N (midpointFourPriors q r)).toReal)) := by
  let K := informationRatio μ N (midpointFourPriors q r)
  let Δ := signMean μ r.val-signMean μ q.val
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr hgap
  have hx : 0 ≤ 4+B*K.toReal := by positivity
  have he : 4+ENNReal.ofReal B*K = ENNReal.ofReal (4+B*K.toReal) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_mul hB,
      ENNReal.ofReal_toReal (midpoint_informationRatio_finite μ N q r)]
    norm_num
    rfl
  change (ENNReal.ofReal Δ^2/(4+ENNReal.ofReal B*K))^(1/(2:ℝ)) = _
  rw [he,← ENNReal.ofReal_pow hΔ,← ENNReal.ofReal_div_of_pos (by positivity : 0 < 4+B*K.toReal)]
  have hs : Δ^2/(4+B*K.toReal) = (Δ/Real.sqrt (4+B*K.toReal))^2 := by
    rw [div_pow,Real.sq_sqrt hx]
  rw [hs,ThresholdHC.Tier6.ofReal_square_rpow_half _ (by positivity)]

end ThresholdHC.StoppingProgram
