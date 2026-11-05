import ThresholdHC.ContinuousObserved.Upper
import ThresholdHC.ContinuousObserved.UniformGaps
import ThresholdHC.SmoothDensity.Upper

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState
open ThresholdHC.Confidence ThresholdHC.BlindUpper

def uniformUpperBudget (ε : ℝ) : ℝ := ThresholdHC.SmoothDensity.upperBudget 2 ε (1 / 16)

theorem uniformUpperBudget_eq (ε : ℝ) :
    uniformUpperBudget ε = (131072 : ℝ) ^ 2 * (ε ^ 2)⁻¹ * (Real.log (1 / ε)) ^ 2 * Real.log 16 := by
  norm_num [uniformUpperBudget,ThresholdHC.SmoothDensity.upperBudget]

theorem uniform_upper_radius {ε : ℝ} (hε : 0 < ε) (he : ε ≤ Real.exp (-16)) :
    1 ≤ uniformUpperBudget ε ∧
      8192 * modulus uniformGaps (confidenceScale (uniformUpperBudget ε) (1 / 16)) ≤ ε ∧
      512 * modulus uniformGaps (1 / Real.sqrt (uniformUpperBudget ε)) ≤ ε := by
  obtain ⟨hB,hz,hza,hr⟩ := ThresholdHC.SmoothDensity.upper_scale_bounds
    (M := 2) (by norm_num) hε he (δ := 1 / 16) (by norm_num) (by norm_num)
  change 1 ≤ uniformUpperBudget ε at hB
  change 0 < confidenceScale (uniformUpperBudget ε) (1 / 16) at hz
  have hzq : confidenceScale (uniformUpperBudget ε) (1 / 16) < 1 / 4 := by
    simpa only [uniformUpperBudget,show (1 / (2 * (2 : ℝ))) = 1 / 4 by norm_num] using hza
  have hc : 8192 * modulus uniformGaps (confidenceScale (uniformUpperBudget ε) (1 / 16)) ≤ ε := by
    rw [uniformGaps,ThresholdHC.SmoothDensity.linear_modulus (1 / 4) _ (by norm_num) (by norm_num) hz hzq]
    simpa only [uniformUpperBudget,show (1 / (2 * (2 : ℝ))) = 1 / 4 by norm_num] using hr
  refine ⟨hB,hc,?_⟩
  have hlog : 1 ≤ Real.log (1 / (1 / 16 : ℝ)) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have heq : Real.log (1 / (1 / 16 : ℝ)) = 4 * Real.log 2 := by
      rw [show (1 / (1 / 16 : ℝ)) = (2 : ℝ) ^ 4 by norm_num,Real.log_pow]
      norm_num
    rw [heq]
    norm_num at h
    linarith
  have hB0 : 0 < uniformUpperBudget ε := by linarith
  have hs : 1 / Real.sqrt (uniformUpperBudget ε) ≤ confidenceScale (uniformUpperBudget ε) (1 / 16) := by
    rw [confidenceScale,Real.sqrt_div (by linarith : 0 ≤ Real.log (1 / (1 / 16 : ℝ)))]
    have hroot : 1 ≤ Real.sqrt (Real.log (1 / (1 / 16 : ℝ))) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlog
    exact div_le_div_of_nonneg_right hroot (Real.sqrt_nonneg _)
  have hm := modulus_mono uniformGaps (by positivity : 0 ≤ 1 / Real.sqrt (uniformUpperBudget ε)) hs
  have hn := modulus_nonneg uniformGaps hz.le
  nlinarith

theorem uniform_observed_confidence_upper :
    ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → StateEstimator R),
      ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-16) →
        ∀ (N : ℕ) (D : QueryDesign N) (s : Fin N → Bool), volume.map D.gap = uniformGaps →
          ∀ (P : Measure (R × ProcessTape)) [IsProbabilityMeasure P],
            RealizesQueryPrefixes D (rule ε) s P →
            (∫⁻ z, totalProcessWork z.2 ∂P) ≤ ENNReal.ofReal (uniformUpperBudget ε) ∧
              P {z | ε < |(rule ε).output z - stateTarget D.cell s|} ≤ ENNReal.ofReal (1 / 16) := by
  obtain ⟨R,mR,rule,hrule⟩ := observed_confidence_upper
  refine ⟨R,mR,fun ε => rule (uniformUpperBudget ε) (1 / 16),?_⟩
  intro ε hε he N D s hl P _ hreal
  obtain ⟨hB,hr,_⟩ := uniform_upper_radius hε he
  obtain ⟨hw,hc⟩ := hrule (uniformUpperBudget ε) (1 / 16) hB (by norm_num) (by norm_num) N uniformGaps D s hl P hreal
  refine ⟨hw,?_⟩
  exact (measure_mono (fun z hz => hr.trans_lt hz)).trans hc

theorem uniform_observed_rms_upper {ε : ℝ} (hε : 0 < ε) (he : ε ≤ Real.exp (-16))
    {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = uniformGaps)
    (P : Measure ((BatchSeed × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (rmsStateEstimator (uniformUpperBudget ε)) s P) :
    (∫⁻ z, totalProcessWork z.2 ∂P) ≤ ENNReal.ofReal (uniformUpperBudget ε) ∧
      rootMeanRisk P (rmsStateEstimator (uniformUpperBudget ε)).output (stateTarget D.cell s) ≤ ENNReal.ofReal ε := by
  obtain ⟨hB,_,hr⟩ := uniform_upper_radius hε he
  obtain ⟨hw,hc⟩ := observed_rms_upper (uniformUpperBudget ε) hB uniformGaps D s hl P hreal
  exact ⟨hw,hc.trans (ENNReal.ofReal_le_ofReal hr)⟩

end ThresholdHC.ContinuousObserved
