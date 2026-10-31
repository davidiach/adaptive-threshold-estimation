import ThresholdHC.StoppingProgram.PositiveTables

/-! The output z/a realizes the flow mean and has second moment bounded
by its perspective variable, including zero stopping weights. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.ObservableSimulation

def flowTableOutput {N : ℕ} (f : Flow N) (s : CountState N) : ℝ := f.outputWeight s/f.stopWeight s

theorem flowTableOutput_mean {N : ℕ} (f : Flow N) (hf : FlowCone f) (s : CountState N) :
    f.stopWeight s*flowTableOutput f s = f.outputWeight s := by
  by_cases ha : f.stopWeight s = 0
  · rw [ha,zero_mul,flow_output_zero_of_stop_zero f hf s ha]
  · exact mul_div_cancel₀ _ ha

theorem flowTableOutput_moment {N : ℕ} (f : Flow N) (hf : FlowCone f) (s : CountState N) :
    f.stopWeight s*(flowTableOutput f s)^2 ≤ f.momentWeight s := by
  by_cases ha : f.stopWeight s = 0
  · rw [ha,zero_mul]
    exact hf.moment_nonneg s
  · have ha' : 0 < f.stopWeight s := lt_of_le_of_ne (hf.stop_nonneg s) (Ne.symm ha)
    have he : f.stopWeight s*(flowTableOutput f s)^2 = (f.outputWeight s)^2/f.stopWeight s := by
      unfold flowTableOutput
      field_simp
    rw [he]
    exact (div_le_iff₀ ha').mpr (by simpa only [mul_comm] using hf.perspective s)

theorem flow_output_mean {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (f : Flow N) (hf : FlowCone f) (hN : 0 < N) :
    (∑ b : CountState N → Bool, flowTableRate f b*
      (∫ ω, tableValue b (flowTableOutput f) ω ∂originalPopulationTapeLaw μ q)) =
      countMean μ q f.outputWeight := by
  rw [flow_mixture_mean μ q f hf hN]
  congr 1
  funext s
  exact flowTableOutput_mean f hf s

theorem flow_output_second_moment {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (f : Flow N) (hf : FlowCone f) (hN : 0 < N) :
    (∑ b : CountState N → Bool, flowTableRate f b*
      (∫ ω, (tableValue b (flowTableOutput f) ω)^2 ∂originalPopulationTapeLaw μ q)) ≤
      countMean μ q f.momentWeight := by
  rw [flow_mixture_second_moment μ q f hf hN]
  exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (flowTableOutput_moment f hf s)
    (countCoefficient_nonneg μ q s))

end ThresholdHC.StoppingProgram
