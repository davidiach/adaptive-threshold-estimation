import ThresholdHC.PaperStatements.Specification
import ThresholdHC.Observable713.Full

/-! The second moment of the observable 713 construction. The output law is the
law of the call value, whose second moment is at most `23 I_μ`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PaperStatements
open ThresholdHC.Tier6 ThresholdHC.Observable713

theorem output_second_moment_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hI : Integrable (fun d : Gap => (d : ℝ)⁻¹) μ) :
    (∫⁻ z, ENNReal.ofReal ((populationOutput observableEstimator z)^2)
        ∂experimentLaw μ observableEstimator q) ≤
      ENNReal.ofReal (23 * ∫ d : Gap, (d : ℝ)⁻¹ ∂μ) := by
  rw [output_lintegral μ q (fun y => ENNReal.ofReal (y^2))
    ((measurable_id.pow_const 2).ennreal_ofReal)]
  exact call_second_le μ q hI

theorem second_moment_bounds (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hI : Integrable (fun d : Gap => (d : ℝ)⁻¹) μ) :
    UnbiasedConverse.UniformlyUnbiased μ observableEstimator ∧
    (∀ q : SignLaw, (∫⁻ z, ENNReal.ofReal ((populationOutput observableEstimator z)^2)
        ∂experimentLaw μ observableEstimator q) ≤ ENNReal.ofReal (23 * ∫ d : Gap, (d : ℝ)⁻¹ ∂μ)) ∧
    UniformBudget μ observableEstimator (31 * ∫ d : Gap, (d : ℝ)⁻¹ ∂μ) := by
  refine ⟨fun q => ⟨(output_memLp μ q hI).integrable (by norm_num), output_mean μ q hI⟩,
    fun q => output_second_moment_le μ q hI, fun q => ?_⟩
  rw [expectedWork_eq]
  exact call_work_le μ q hI

end ThresholdHC.PaperStatements
