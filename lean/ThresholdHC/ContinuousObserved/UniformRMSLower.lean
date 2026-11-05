import ThresholdHC.ContinuousObserved.UniformLower
import ThresholdHC.CriticalEntropy.AffinityTesting

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState ThresholdHC.SmoothDensity

theorem mse_fixed_confidence {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (θ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hr : squaredRisk P f θ ≤ ENNReal.ofReal (ε ^ 2)) :
    P {z | 4 * ε < |f z - θ|} ≤ ENNReal.ofReal (1 / 16) := by
  have he : (4 * ε) ^ 2 * (1 / 16 : ℝ) = ε ^ 2 := by ring
  have h := CriticalEntropy.risk_event_markov P f hf θ ((4 * ε) ^ 2) (1 / 16)
    (by positivity) (by norm_num) {z | 4 * ε < |f z - θ|}
    (fun z hz => by
      have hp := abs_nonneg (f z - θ)
      have hs := sq_abs (f z - θ)
      change 4 * ε < |f z - θ| at hz
      nlinarith)
    (by simpa only [he] using hr)
  have hm := ENNReal.ofReal_le_ofReal h
  change ENNReal.ofReal (P {z | 4 * ε < |f z - θ|}).toReal ≤ _ at hm
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at hm
  exact hm

theorem uniform_rms_lower {ε : ℝ} (hε : 0 < ε)
    (he : ε ≤ min (radiusCutoff 0 / 4) (1 / 16)) :
    ∃ (h : Gap) (D : CellDesign uniformGaps h (1 / 16)),
      (∀ u, (D.gap u : ℝ) ≤ 1 / 4) ∧
      (∀ (R : Type) [MeasurableSpace R] (A : StateEstimator R)
        (P : (Fin D.count → Bool) → Measure (R × ProcessTape))
        [∀ s, IsProbabilityMeasure (P s)],
        (∀ s, RealizesQueryPrefixes (CellDesign.queryDesign uniformGaps h (1 / 16) D) A s (P s)) →
        ∀ (B : ℝ), 0 ≤ B →
        (∀ s, (∫⁻ z, totalProcessWork z.2 ∂P s) ≤ ENNReal.ofReal B) →
        (∀ s, squaredRisk (P s) A.output (stateTarget D.cell s) ≤ ENNReal.ofReal (ε ^ 2)) →
        (lowerCoefficient / 64) * (Real.log (1 / ε)) ^ 2 / ε ^ 2 ≤ B) := by
  have he4 : 4 * ε ≤ radiusCutoff 0 := by
    have h := he.trans (min_le_left _ _)
    linarith
  obtain ⟨h,D,hgap,hbound⟩ := uniform_confidence_lower (by positivity : 0 < 4 * ε) he4
  refine ⟨h,D,hgap,?_⟩
  intro R _ A P _ hl B hB hw hr
  have hb := hbound R A P hl B hB hw
    (fun s => mse_fixed_confidence (P s) A.output A.output_measurable (stateTarget D.cell s) hε (hr s))
  have he16 : ε ≤ 1 / 16 := he.trans (min_le_right _ _)
  have hratio : (16 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hratio
  have h16 : Real.log (16 : ℝ) = 2 * Real.log 4 := by
    rw [show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num,Real.log_pow]
    norm_num
  rw [h16] at hlog
  have heq : Real.log (1 / (4 * ε)) = Real.log (1 / ε) - Real.log 4 := by
    rw [Real.log_div one_ne_zero (mul_ne_zero (by norm_num) hε.ne'),
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hε.ne',Real.log_div one_ne_zero hε.ne']
    ring
  have h4 : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).le
  have hsq : (Real.log (1 / ε)) ^ 2 ≤ 4 * (Real.log (1 / (4 * ε))) ^ 2 := by
    rw [heq]
    have hp : 0 ≤ (Real.log (1 / ε) - 2 * Real.log 4) *
        (3 * Real.log (1 / ε) - 2 * Real.log 4) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq lowerCoefficient_pos.le
  calc
    _ ≤ (lowerCoefficient / 16) * (Real.log (1 / (4 * ε))) ^ 2 / ε ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
      nlinarith
    _ = lowerCoefficient * (Real.log (1 / (4 * ε))) ^ 2 / (4 * ε) ^ 2 := by
      field_simp
      ring
    _ ≤ B := hb

end ThresholdHC.ContinuousObserved
