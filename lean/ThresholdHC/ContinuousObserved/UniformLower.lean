import ThresholdHC.ContinuousObserved.QueryLower
import ThresholdHC.ContinuousObserved.Scale
import ThresholdHC.ContinuousObserved.Target

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState ThresholdHC.SmoothDensity

def lowerCoefficient : ℝ := (225 / (128 * 64 ^ 2)) * klB (7 / 8) (1 / 8)

theorem lowerCoefficient_pos : 0 < lowerCoefficient := by
  have hk : klB (7 / 8) (1 / 8) = (3 / 4 : ℝ) * Real.log 7 := by
    norm_num [klB,Real.log_div]
    ring
  rw [lowerCoefficient,hk]
  exact mul_pos (by norm_num) (mul_pos (by norm_num) (Real.log_pos (by norm_num)))

/-- The uniform continuous-gap family forces the logarithmic-squared
expected-work lower rate at fixed confidence, even with selected queries. -/
theorem uniform_confidence_lower {ε : ℝ} (hε : 0 < ε) (he : ε ≤ radiusCutoff 0) :
    ∃ (h : Gap) (D : CellDesign uniformGaps h (1 / 16)),
      (∀ u, (D.gap u : ℝ) ≤ 1 / 4) ∧
      (∀ (R : Type) [MeasurableSpace R] (A : StateEstimator R)
        (P : (Fin D.count → Bool) → Measure (R × ProcessTape))
        [∀ s, IsProbabilityMeasure (P s)],
        (∀ s, RealizesQueryPrefixes (CellDesign.queryDesign uniformGaps h (1 / 16) D) A s (P s)) →
        ∀ (B : ℝ), 0 ≤ B →
        (∀ s, (∫⁻ z, totalProcessWork z.2 ∂P s) ≤ ENNReal.ofReal B) →
        (∀ s, P s {z | ε < |A.output z - stateTarget D.cell s|} ≤ ENNReal.ofReal (1 / 16)) →
        lowerCoefficient * (Real.log (1 / ε)) ^ 2 / ε ^ 2 ≤ B) := by
  obtain ⟨h,_,hscale,hsep⟩ := choose_observed_scale hε he
  obtain ⟨D,hgap,_⟩ := uniform_design_exists h (δ := 1 / 16) (by norm_num)
  refine ⟨h,D,hgap,?_⟩
  intro R _ A P _ hl B hB hw hc
  have hδ : 0 < (1 / 16 : ℝ) := by norm_num
  have hd : (1 / 16 : ℝ) ≤ 1 / 8 := by norm_num
  have hr : ε < cellDelta D.cap D.cell h / 4 := by
    have hs := design_separation uniformGaps h (1 / 16) D
    linarith
  have hconf : ∀ s, P s
      {z | cellDelta D.cap D.cell h / 4 < |A.output z - stateTarget D.cell s|} ≤
        ENNReal.ofReal (1 / 16) := by
    intro s
    exact (measure_mono (fun z hz => hr.trans hz)).trans (hc s)
  have hb := query_confidence_lower uniformGaps h hδ hd D A P hl hB hw hconf
  have hL : Real.log (1 / ε) ≠ 0 := by
    intro hz
    rw [hz,div_zero] at hscale
    have hp := h.property.1
    rw [hscale] at hp
    exact (lt_irrefl 0) hp
  have hcst : (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * (1 / 16)) (2 * (1 / 16)) =
      lowerCoefficient * (Real.log (1 / ε)) ^ 2 / ε ^ 2 := by
    norm_num only [show (1 - 2 * (1 / 16) : ℝ) = 7 / 8 by norm_num,
      show (2 * (1 / 16) : ℝ) = 1 / 8 by norm_num]
    rw [hscale]
    unfold lowerCoefficient
    field_simp [hε.ne',hL]
  rw [hcst] at hb
  exact hb

end ThresholdHC.ContinuousObserved
