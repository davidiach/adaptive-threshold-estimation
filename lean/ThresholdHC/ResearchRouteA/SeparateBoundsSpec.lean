import ThresholdHC.Uniform713.Specification

/-!
Separate moments for the existing fixed estimator, and their passage to two
separate real suprema. This is a bridge within the existing observation-kernel
model, not a realization theorem for a fresh-coin policy or a rare-event bound.
The estimator and observation map are fixed before the family of latent laws.
-/

noncomputable section

namespace ThresholdHC.ResearchRouteA

open MeasureTheory ProbabilityTheory ThresholdHC.Uniform713

def SeparateMomentBoundsStatement : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Θ] [MeasurableSpace Ω]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (κ : Kernel Θ Ω) [IsMarkovKernel κ]
    (X : ℕ → Ω → ℝ) (d : Θ → ℝ) (s : Θ → Bool),
    ObservationModel ν κ X d s →
    MemLp (@uniformEstimator Θ Ω X) 2 (mixtureLaw ν κ) ∧
    Integrable (@uniformWork Θ Ω X) (mixtureLaw ν κ) ∧
    (∫ x, (uniformEstimator X x) ^ 2 ∂mixtureLaw ν κ) ≤
      23 * (∫ θ, (d θ)⁻¹ ∂ν) ∧
    (∫ x, uniformWork X x ∂mixtureLaw ν κ) ≤
      31 * (∫ θ, (d θ)⁻¹ ∂ν)

def UniformFamilyBoundsStatement : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Θ] [MeasurableSpace Ω]
    (κ : Kernel Θ Ω) [IsMarkovKernel κ]
    (X : ℕ → Ω → ℝ) (d : Θ → ℝ) (s : Θ → Bool)
    (Γ : Type) [Nonempty Γ] (ν : Γ → Measure Θ) (I : ℝ),
    (∀ γ, IsProbabilityMeasure (ν γ)) →
    (∀ γ, ObservationModel (ν γ) κ X d s) →
    (∀ γ, (∫ θ, (d θ)⁻¹ ∂ν γ) = I) →
    let variances := Set.range (fun γ =>
      variance (@uniformEstimator Θ Ω X) (mixtureLaw (ν γ) κ))
    let works := Set.range (fun γ =>
      ∫ x, uniformWork X x ∂mixtureLaw (ν γ) κ)
    BddAbove variances ∧ BddAbove works ∧
    0 ≤ sSup variances ∧ sSup variances ≤ 23 * I ∧
    0 ≤ sSup works ∧ sSup works ≤ 31 * I ∧
    sSup variances * sSup works ≤ 713 * I ^ 2

end ThresholdHC.ResearchRouteA
