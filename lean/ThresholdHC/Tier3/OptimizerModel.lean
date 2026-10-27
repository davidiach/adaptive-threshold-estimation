import ThresholdHC.Statements2

/-!
The arbitrary-law rare-event variational problem. The magnitude is positive
almost everywhere and at most one half; its law may have atoms or be singular.
No inverse moment is assumed. All competitors are measurable allocations in
[0,1] with the stated integral budget.
-/

noncomputable section
open MeasureTheory Set

namespace ThresholdHC.Tier3

def allocation (t d : ℝ) : ℝ := min 1 (t ^ 2 / d ^ 2)

def allocationMass {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (D : α → ℝ) (t : ℝ) : ℝ :=
  ∫ x, allocation t (D x) ∂μ

def rareObjective {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (D : α → ℝ) (h : ℝ) (v : α → ℝ) : ℝ :=
  ∫ x, min (v x) (h * Real.sqrt (v x) / D x) ∂μ

def FeasibleAllocation {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ρ : ℝ) (v : α → ℝ) : Prop :=
  Measurable v ∧ (∀ᵐ x ∂μ, 0 ≤ v x ∧ v x ≤ 1) ∧ (∫ x, v x ∂μ) ≤ ρ

def ArbitraryLawCutoffStatement : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (D : α → ℝ) (ρ : ℝ),
    Measurable D → (∀ᵐ x ∂μ, 0 < D x ∧ D x ≤ 1 / 2) → 0 < ρ → ρ < 1 →
    ∃ t : ℝ, 0 < t ∧ t < 1 / 2 ∧ allocationMass μ D t = ρ ∧
      ∀ s : ℝ, 0 < s → allocationMass μ D s = ρ → s = t

def ArbitraryLawOptimizerStatement : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (D : α → ℝ) (ρ : ℝ),
    Measurable D → (∀ᵐ x ∂μ, 0 < D x ∧ D x ≤ 1 / 2) → 0 < ρ → ρ < 1 →
    ∃ t : ℝ, 0 < t ∧ t < 1 / 2 ∧ allocationMass μ D t = ρ ∧
      (∀ s : ℝ, 0 < s → allocationMass μ D s = ρ → s = t) ∧
      FeasibleAllocation μ ρ (fun x => allocation t (D x)) ∧
      ∀ h : ℝ, 0 < h →
        (∀ v : α → ℝ, FeasibleAllocation μ ρ v →
          rareObjective μ D h v ≤ rareObjective μ D h (fun x => allocation t (D x))) ∧
        (t ≤ h → rareObjective μ D h (fun x => allocation t (D x)) = ρ) ∧
        (h < t → rareObjective μ D h (fun x => allocation t (D x)) =
          μ.real {x | D x ≤ h} + h * (∫ x in {x | h < D x ∧ D x ≤ t}, (D x)⁻¹ ∂μ) +
            h * t * (∫ x in {x | t < D x}, ((D x)⁻¹) ^ 2 ∂μ))

end ThresholdHC.Tier3
