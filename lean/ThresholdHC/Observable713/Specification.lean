import ThresholdHC.UnbiasedConverse.Model

/-!
The target uses the unchanged observable adaptive experiment. One algorithm is
chosen before every gap law; the only population restriction is integrability
of the inverse gap. Variance and work remain extended-real quantities.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.Observable713
open ThresholdHC.Tier6 ThresholdHC.UnbiasedConverse

def Observable713Statement : Prop :=
  ∃ A : AdaptiveEstimator ℕ,
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      Integrable (fun d : Gap => (d : ℝ)⁻¹) μ →
      UniformlyUnbiased μ A ∧
      UniformVarianceBound μ A (23 * ∫ d : Gap, (d : ℝ)⁻¹ ∂μ) ∧
      UniformBudget μ A (31 * ∫ d : Gap, (d : ℝ)⁻¹ ∂μ) ∧
      (⨆ q : SignLaw, evariance (populationOutput A) (experimentLaw μ A q)) *
        (⨆ q : SignLaw, expectedWork μ A q) ≤
          ENNReal.ofReal (713 * (∫ d : Gap, (d : ℝ)⁻¹ ∂μ)^2)

def ObservableUnbiasedIffStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    (∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R) (V W : ℝ),
      0 ≤ V ∧ 0 ≤ W ∧ UniformlyUnbiased μ A ∧
      UniformVarianceBound μ A V ∧ UniformBudget μ A W) ↔
    Integrable (fun d : Gap => (d : ℝ)⁻¹) μ

end ThresholdHC.Observable713
