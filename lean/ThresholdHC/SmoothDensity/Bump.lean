import ThresholdHC.SmoothDensity.Perturbation

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ThresholdHC.SmoothDensity

def baseBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 8, 3 / 16, by norm_num, by norm_num⟩

/-- A fixed, even, normalized density supported strictly within the allowed interval. -/
def baseDensity : ℝ → ℝ := baseBump.normed volume

theorem baseDensity_contDiff : ContDiff ℝ ∞ baseDensity :=
  baseBump.contDiff_normed

theorem baseDensity_compact : HasCompactSupport baseDensity :=
  baseBump.hasCompactSupport_normed

theorem baseDensity_nonneg (x : ℝ) : 0 ≤ baseDensity x :=
  baseBump.nonneg_normed x

theorem baseDensity_integrable : Integrable baseDensity := baseBump.integrable_normed

theorem baseDensity_integral : ∫ x, baseDensity x = 1 := baseBump.integral_normed

theorem baseDensity_even (x : ℝ) : baseDensity (-x) = baseDensity x :=
  baseBump.normed_neg x

theorem baseDensity_zero {x : ℝ} (hx : 1 / 4 ≤ |x|) : baseDensity x = 0 := by
  unfold baseDensity
  rw [baseBump.normed_def, baseBump.zero_of_le_dist, zero_div]
  change (3 / 16 : ℝ) ≤ dist x 0
  simpa only [dist_zero_right, Real.norm_eq_abs] using
    (show (3 / 16 : ℝ) ≤ |x| by linarith)

theorem baseDensity_core {x : ℝ} (hx : |x| ≤ 1 / 8) : 1 ≤ baseDensity x := by
  have he : baseBump x = 1 := baseBump.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, baseBump] using hx)
  have hi : (∫ y, baseBump y) ≤ 1 := by
    have h := baseBump.integral_le_measure_closedBall (volume : Measure ℝ)
    norm_num [baseBump, Real.closedBall_eq_Icc, measureReal_def] at h
    change (∫ y, baseBump y) ≤ 3 / 8 at h
    linarith
  rw [baseDensity, baseBump.normed_def, he]
  exact (le_div_iff₀ baseBump.integral_pos).mpr (by simpa using hi)

private theorem baseDerivative_compact (k : ℕ) : HasCompactSupport (iteratedDeriv k baseDensity) := by
  induction k with
  | zero => simpa using baseDensity_compact
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem baseDerivative_bounded (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |iteratedDeriv k baseDensity x| ≤ C := by
  have hc : Continuous (iteratedDeriv k baseDensity) :=
    baseDensity_contDiff.continuous_iteratedDeriv k (by simp)
  obtain ⟨C,hC⟩ := hc.bounded_above_of_compact_support (baseDerivative_compact k)
  refine ⟨|C| + 1, by positivity, fun x => ?_⟩
  have hb : |iteratedDeriv k baseDensity x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x
  exact hb.trans (by linarith [le_abs_self C])

end ThresholdHC.SmoothDensity
