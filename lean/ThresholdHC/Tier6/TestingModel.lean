import ThresholdHC.Tier5.Model

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.Tier6

/-- Mean squared error, retaining infinite risk without integrability assumptions. -/
def squaredRisk {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((f x-a)^2) ∂P

/-- A two-point estimation lower bound for actual probability measures and KL. -/
def TwoPointRiskStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (a b : ℝ),
    Measurable f → a < b → klDiv P Q ≤ ENNReal.ofReal (1/8:ℝ) →
    ENNReal.ofReal ((b-a)^2/16) ≤ max (squaredRisk P f a) (squaredRisk Q f b)

end ThresholdHC.Tier6
