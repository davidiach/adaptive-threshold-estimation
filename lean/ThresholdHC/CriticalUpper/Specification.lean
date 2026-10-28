import ThresholdHC.CriticalEntropy.CriticalMinimax

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory ThresholdHC.CriticalEntropy
open scoped ENNReal

/-- Matching upper target for the fixed quadratic gap law, in the full
observable rare-prior model. One universal constant precedes rarity and budget;
the estimator can depend on both but not on the unknown sign prior. -/
def CriticalUpperStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ (R : Type) (_ : MeasurableSpace R) (rule : unitInterval → ℝ → Tier6.AdaptiveEstimator R),
      ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
      ∀ B : ℝ, 1 ≤ B →
        CriticalUniformBudget (rule ρ B) (ρ : ℝ) B ∧
        criticalMaximalRMSRisk (rule ρ B) (ρ : ℝ) ≤
          ENNReal.ofReal (C*min (ρ : ℝ)
            (Real.sqrt ((ρ : ℝ)*criticalLogFactor (ρ : ℝ)/B)))

def CriticalMinimaxUpperStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ B : ℝ, 1 ≤ B →
      criticalMinimaxRisk (ρ : ℝ) B ≤
        ENNReal.ofReal (C*min (ρ : ℝ)
          (Real.sqrt ((ρ : ℝ)*criticalLogFactor (ρ : ℝ)/B)))

end ThresholdHC.CriticalUpper
