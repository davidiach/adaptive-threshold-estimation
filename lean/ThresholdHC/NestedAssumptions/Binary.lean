import ThresholdHC.NestedAssumptions.Specification
import ThresholdHC.ContinuousObserved.Normalization

/-!
# Pointwise moments of a binary conditional law

For a general success probability `p u`, the conditional law `binaryLaw p u` of
`X ∈ {-1,1}` has mean `2 p u - 1` and variance `1 - (2 p u - 1)^2`. Its normalized
absolute mean is `normalizedGap` of the half magnitude, and when the half magnitude is
at most `1/4` its standardized moments of every order `q ≥ 0` are at most `3^(q/2)`.
-/

noncomputable section
namespace ThresholdHC.NestedAssumptions
open MeasureTheory ProbabilityTheory Set
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.ContinuousObserved

theorem measurable_binaryValue : Measurable binaryValue := measurable_of_countable _

instance binaryLaw_probability (p : unitInterval → unitInterval) (u : unitInterval) :
    IsProbabilityMeasure (binaryLaw p u) := by
  unfold binaryLaw
  infer_instance

theorem binaryLaw_eq (p : unitInterval → unitInterval) (u : unitInterval) :
    binaryLaw p u = bernoulliMeasure (1 : ℝ) (-1) (p u) := by
  rw [binaryLaw, map_bernoulliMeasure]
  simp [binaryValue]

theorem condMean_binaryLaw (p : unitInterval → unitInterval) (u : unitInterval) :
    condMean (binaryLaw p) u = 2 * (p u : ℝ) - 1 := by
  rw [condMean, binaryLaw_eq, integral_bernoulliMeasure]
  simp only [smul_eq_mul]
  ring

theorem variance_binaryLaw (p : unitInterval → unitInterval) (u : unitInterval) :
    variance id (binaryLaw p u) = 1 - (condMean (binaryLaw p) u) ^ 2 := by
  rw [condMean_binaryLaw, binaryLaw_eq, variance_eq_integral aemeasurable_id]
  simp only [integral_bernoulliMeasure, id, smul_eq_mul]
  ring

theorem condSD_binaryLaw (p : unitInterval → unitInterval) (u : unitInterval) :
    condSD (binaryLaw p) u = Real.sqrt (1 - (condMean (binaryLaw p) u) ^ 2) := by
  rw [condSD, variance_binaryLaw]

theorem halfMagnitude_binaryLaw (p : unitInterval → unitInterval) (u : unitInterval) :
    |condMean (binaryLaw p) u| / 2 = |(p u : ℝ) - 1 / 2| := by
  rw [condMean_binaryLaw, show 2 * (p u : ℝ) - 1 = 2 * ((p u : ℝ) - 1 / 2) by ring, abs_mul]
  norm_num

theorem normalizedMean_binaryLaw (p : unitInterval → unitInterval) (u : unitInterval) :
    normalizedMean (binaryLaw p) u = normalizedGap (|condMean (binaryLaw p) u| / 2) := by
  rw [normalizedMean, condSD_binaryLaw, normalizedGap]
  have h1 : 2 * (|condMean (binaryLaw p) u| / 2) = |condMean (binaryLaw p) u| := by ring
  have h2 : 4 * (|condMean (binaryLaw p) u| / 2) ^ 2 = (condMean (binaryLaw p) u) ^ 2 := by
    rw [div_pow, sq_abs]
    ring
  rw [h1, h2]

theorem binaryLaw_moment (p : unitInterval → unitInterval) (u : unitInterval)
    (hu : |condMean (binaryLaw p) u| / 2 ≤ 1 / 4) {q : ℝ} (hq : 0 ≤ q) :
    0 < condSD (binaryLaw p) u ∧
      Integrable (fun x => (|x - condMean (binaryLaw p) u| / condSD (binaryLaw p) u) ^ q)
        (binaryLaw p u) ∧
      ∫ x, (|x - condMean (binaryLaw p) u| / condSD (binaryLaw p) u) ^ q ∂binaryLaw p u ≤
        (3 : ℝ) ^ (q / 2) := by
  have hσ := condSD_binaryLaw p u
  set m := condMean (binaryLaw p) u
  set σ := condSD (binaryLaw p) u
  have hm : |m| ≤ 1 / 2 := by linarith
  have hm2 : m ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg m]
  have hs3 : Real.sqrt 3 / 2 ≤ σ := by
    rw [hσ]
    calc
      Real.sqrt 3 / 2 = Real.sqrt (3 / 4 : ℝ) := by rw [Real.sqrt_div (by norm_num)]; norm_num
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < σ := lt_of_lt_of_le (by positivity) hs3
  have hb (x : ℝ) (hx : |x| = 1) : (|x - m| / σ) ^ q ≤ (3 : ℝ) ^ (q / 2) := by
    have hxm : |x - m| ≤ 3 / 2 := by
      calc
        |x - m| ≤ |x| + |m| := abs_sub _ _
        _ ≤ 3 / 2 := by linarith
    have hr : |x - m| / σ ≤ Real.sqrt 3 := by
      apply (div_le_iff₀ hpos).mpr
      have h := mul_le_mul_of_nonneg_left hs3 (Real.sqrt_nonneg 3)
      have hsq := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      nlinarith
    calc
      (|x - m| / σ) ^ q ≤ (Real.sqrt 3) ^ q :=
        Real.rpow_le_rpow (div_nonneg (abs_nonneg _) hpos.le) hr hq
      _ = (3 : ℝ) ^ (q / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        congr 1
        ring
  refine ⟨hpos, ?_, ?_⟩
  · rw [binaryLaw_eq]
    exact integrable_bernoulliMeasure _ _ _ _
  · rw [binaryLaw_eq, integral_bernoulliMeasure]
    simp only [smul_eq_mul]
    have h1 := hb 1 (by norm_num)
    have h2 := hb (-1) (by norm_num)
    have hp0 : 0 ≤ (p u : ℝ) := (p u).2.1
    have hp1 : 0 ≤ 1 - (p u : ℝ) := sub_nonneg.mpr (p u).2.2
    nlinarith [mul_le_mul_of_nonneg_left h1 hp0, mul_le_mul_of_nonneg_left h2 hp1]

end ThresholdHC.NestedAssumptions
