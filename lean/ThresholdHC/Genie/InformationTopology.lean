import ThresholdHC.Genie.PerspectiveTopology
import ThresholdHC.StoppingProgram.FlowBasics

/-! Lower semicontinuity of the actual information/work ratio in any
continuous family of count coordinates. The charged root keeps work positive. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.StoppingProgram

theorem flow_ratio_perspective_sum {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (f : Flow N) (hf : FlowCone f) (hi : intensity f = 1) :
    flowInformation μ Q f/ENNReal.ofReal (countMean μ Q.work f.continueWeight) =
      ∑ s : CountState N,
        perspective ((f.stopWeight s/countMean μ Q.work f.continueWeight)*
          (countCoefficient μ Q.high s-countCoefficient μ Q.low s))
          ((f.stopWeight s/countMean μ Q.work f.continueWeight)*countCoefficient μ Q.variance s) := by
  have hw : 0 < countMean μ Q.work f.continueWeight := by
    have h := flow_work_ge_intensity μ Q.work f hf
    rw [hi] at h
    linarith
  rw [flowInformation,ENNReal.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  rw [perspective_scale _ _ (div_nonneg (hf.stop_nonneg s) hw.le),ENNReal.ofReal_div_of_pos hw]
  simp only [div_eq_mul_inv]
  ac_rfl

theorem flow_ratio_lowerSemicontinuous {X : Type*} [TopologicalSpace X] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : X → FourPriors)
    (hl : ∀ s : CountState N, Continuous (fun x => countCoefficient μ (Q x).low s))
    (hh : ∀ s : CountState N, Continuous (fun x => countCoefficient μ (Q x).high s))
    (hv : ∀ s : CountState N, Continuous (fun x => countCoefficient μ (Q x).variance s))
    (hw : ∀ s : CountState N, Continuous (fun x => countCoefficient μ (Q x).work s))
    (f : Flow N) (hf : FlowCone f) (hi : intensity f = 1) :
    LowerSemicontinuous (fun x => flowInformation μ (Q x) f/
      ENNReal.ofReal (countMean μ (Q x).work f.continueWeight)) := by
  have hW : Continuous (fun x => countMean μ (Q x).work f.continueWeight) :=
    continuous_finsetSum _ (fun s hs => (hw s).mul continuous_const)
  have hWpos (x : X) : 0 < countMean μ (Q x).work f.continueWeight := by
    have h := flow_work_ge_intensity μ (Q x).work f hf
    rw [hi] at h
    linarith
  have he : (fun x => flowInformation μ (Q x) f/ENNReal.ofReal (countMean μ (Q x).work f.continueWeight)) =
      fun x => ∑ s : CountState N,
        perspective ((f.stopWeight s/countMean μ (Q x).work f.continueWeight)*
          (countCoefficient μ (Q x).high s-countCoefficient μ (Q x).low s))
          ((f.stopWeight s/countMean μ (Q x).work f.continueWeight)*countCoefficient μ (Q x).variance s) :=
    funext (fun x => flow_ratio_perspective_sum μ (Q x) f hf hi)
  rw [he]
  apply lowerSemicontinuous_sum
  intro s hs
  have hc : Continuous (fun x => f.stopWeight s/countMean μ (Q x).work f.continueWeight) :=
    continuous_const.div hW (fun x => (hWpos x).ne')
  apply lowerSemicontinuous_perspective
    (fun x => (f.stopWeight s/countMean μ (Q x).work f.continueWeight)*
      (countCoefficient μ (Q x).high s-countCoefficient μ (Q x).low s))
    (fun x => (f.stopWeight s/countMean μ (Q x).work f.continueWeight)*countCoefficient μ (Q x).variance s)
    (hc.mul ((hh s).sub (hl s))) (hc.mul (hv s))
  intro x
  exact mul_nonneg (div_nonneg (hf.stop_nonneg s) (hWpos x).le) (countCoefficient_nonneg μ _ s)

theorem informationRatio_lowerSemicontinuous {X : Type*} [TopologicalSpace X]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : X → FourPriors)
    (hl : ∀ s : CountState N, Continuous (fun x => countCoefficient μ (Q x).low s))
    (hh : ∀ s : CountState N, Continuous (fun x => countCoefficient μ (Q x).high s))
    (hv : ∀ s : CountState N, Continuous (fun x => countCoefficient μ (Q x).variance s))
    (hw : ∀ s : CountState N, Continuous (fun x => countCoefficient μ (Q x).work s)) :
    LowerSemicontinuous (fun x => informationRatio μ N (Q x)) := by
  apply lowerSemicontinuous_iSup
  intro f
  apply lowerSemicontinuous_iSup
  intro hf
  apply lowerSemicontinuous_iSup
  intro hi
  exact flow_ratio_lowerSemicontinuous μ Q hl hh hv hw f hf hi

end ThresholdHC.Genie
