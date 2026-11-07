import ThresholdHC.ArbitraryLawAdaptation.GammaTransport

/-! Integrating countable measurable cells and merging their costs. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.ArbitraryLawAdaptation

def cellCost {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (π : Measure Ω) (tag : Ω → ι) (w : Ω → ℝ≥0∞) (i : ι) : ℝ≥0∞ :=
  ∫⁻ z, if tag z = i then w z else 0 ∂π

theorem cellCost_merge {Ω ι κ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] [DecidableEq ι]
    [DecidableEq κ] (π : Measure Ω) {tag : Ω → ι} (htag : Measurable tag)
    {w : Ω → ℝ≥0∞} (hw : Measurable w) (dest : ι → κ) (j : κ) :
    (∑' i, if dest i = j then cellCost π tag w i else 0) =
      ∫⁻ z, if dest (tag z) = j then w z else 0 ∂π := by
  classical
  have he (i : ι) : (if dest i = j then cellCost π tag w i else 0) =
      ∫⁻ z, if tag z = i then (if dest i = j then w z else 0) else 0 ∂π := by
    by_cases hi : dest i = j <;> simp [hi, cellCost]
  simp_rw [he]
  rw [← lintegral_tsum]
  · apply lintegral_congr
    intro z
    simp only [tsum_ite_eq']
  · intro i
    apply Measurable.aemeasurable
    apply Measurable.ite (measurableSet_eq_fun htag measurable_const)
    · by_cases hi : dest i = j <;> simp only [hi, ite_true, ite_false] <;> fun_prop
    · exact measurable_const

end ThresholdHC.ArbitraryLawAdaptation
