
import ThresholdHC.ArbitraryLawAdaptation.ZeroQuantile
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6 (Gap)

example : ∀ (z : ℝ) (η : Measure Gap),
    zeroAtomLaw z η =
      ENNReal.ofReal z • Measure.dirac 0 + ENNReal.ofReal (1 - z) • η.map Subtype.val :=
  fun _ _ => rfl
example : ∀ (z : ℝ) (η : Measure Gap) [IsFiniteMeasure η],
    IsFiniteMeasure (zeroAtomLaw z η) := @zeroAtomLaw_finite
example : ∀ (ρ z : ℝ), conditionalRarity ρ z = (ρ - z) / (1 - z) := fun _ _ => rfl
example : ∀ (z : ℝ) (η : Measure Gap) (ρ B : ℝ),
    zeroQuantileValue z η ρ B =
      if ρ ≤ z then ENNReal.ofReal ρ
      else min (ENNReal.ofReal ρ)
        (ENNReal.ofReal z +
          (ENNReal.ofReal (1 - z) *
              ENNReal.ofReal
                (tailModulus (quantileTail η (conditionalRarity ρ z)) (budgetScale B)) +
            ENNReal.ofReal (budgetScale B) *
              (ENNReal.ofReal ρ * (ENNReal.ofReal (1 - z) *
                measureCostEntropy (quantileCore η (conditionalRarity ρ z)))) ^ (1 / (2 : ℝ)))) :=
  fun _ _ _ _ => rfl
example : ∀ (α : Measure ℝ), zeroMass α = α.real {0} := fun _ => rfl
example : ∀ (α : Measure ℝ),
    positiveLaw α = (ENNReal.ofReal (1 - zeroMass α))⁻¹ • positivePart α := fun _ => rfl
example : ∀ (α : Measure ℝ) (ρ B : ℝ),
    quantileDesignValue α ρ B = zeroQuantileValue (zeroMass α) (positiveLaw α) ρ B :=
  fun _ _ _ => rfl
example : ∀ (z : ℝ) (η : Measure Gap),
    zeroAtomLaw z η {0} = ENNReal.ofReal z := @zeroAtomLaw_zero_atom
example : ∀ {α σ : Measure ℝ} [IsFiniteMeasure α] (hσ : σ ≤ α) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B),
    α {0} ≤ zeroObjective α ρ B σ := @zeroMass_le_zeroObjective
example : ∀ (α : Measure ℝ) [IsFiniteMeasure α] {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B),
    min (ENNReal.ofReal ρ) (α {0}) ≤ zeroSelection α ρ B := @min_zeroMass_le_zeroSelection
example : ∀ (η : Measure Gap) [IsFiniteMeasure η] {c r ρ B : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (hcr : c * r ≤ ρ),
    ENNReal.ofReal c * ThresholdHC.EntropyTail.selection η r B ≤ ThresholdHC.EntropyTail.selection (ENNReal.ofReal c • η) ρ B := @smul_selection_le
example : ∀ (c : ℝ≥0∞) (σ : Measure Gap),
    (c • σ).map Subtype.val = c • σ.map Subtype.val := @map_val_smul
example : ∀ (η : Measure Gap) [IsFiniteMeasure η] {z r ρ B : ℝ} (hz1 : z < 1) (hr : 0 ≤ r) (hcr : (1 - z) * r ≤ ρ),
    ENNReal.ofReal (1 - z) * ThresholdHC.EntropyTail.selection η r B ≤ zeroSelection (zeroAtomLaw z η) ρ B := @positive_selection_le_zeroSelection
example : ∀ (η : Measure Gap) {ρ B : ℝ} (hρ : 0 < ρ),
    zeroQuantileValue 0 η ρ B = closedQuantileValue η ρ B := @zeroQuantileValue_zero
example : ∀ (z : ℝ) (η : Measure Gap) (ρ B : ℝ),
    zeroQuantileValue z η ρ B ≤ ENNReal.ofReal ρ := @zeroQuantileValue_le_rho
example : ∀ (η : Measure Gap) {z ρ B : ℝ} (hz0 : 0 ≤ z) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hz : 2 * z ≤ ρ),
    zeroQuantileValue z η ρ B ≤
      ENNReal.ofReal z +
      ENNReal.ofReal (Real.sqrt 2 * (1 - z)) *
      closedQuantileValue η (conditionalRarity ρ z) B := @zeroQuantileValue_le_closed
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z ρ B : ℝ} (hz0 : 0 ≤ z) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hB : 0 < B),
    zeroQuantileValue z η ρ B ≤ 4 * zeroSelection (zeroAtomLaw z η) ρ B := @zeroQuantileValue_le_four
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z ρ : ℝ} (hzρ : z < ρ) (hρ1 : ρ ≤ 1) (B : ℝ),
    zeroObjective (zeroAtomLaw z η) ρ B
      ((ENNReal.ofReal (1 - z) • quantileCore η (conditionalRarity ρ z)).map Subtype.val) =
      ENNReal.ofReal z +
      (ENNReal.ofReal (1 - z) *
      ENNReal.ofReal (tailModulus (quantileTail η (conditionalRarity ρ z)) (budgetScale B)) +
      ENNReal.ofReal (budgetScale B) *
      (ENNReal.ofReal ρ * (ENNReal.ofReal (1 - z) *
      measureCostEntropy (quantileCore η (conditionalRarity ρ z)))) ^ (1 / (2 : ℝ))) := @zeroObjective_quantileCore
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (z : ℝ) {ρ : ℝ} (hρ1 : ρ ≤ 1) (B : ℝ),
    zeroSelection (zeroAtomLaw z η) ρ B ≤ zeroQuantileValue z η ρ B := @zeroSelection_le_zeroQuantileValue
example : ∀ (α : Measure ℝ) [IsProbabilityMeasure α] (hsupp : α (Set.Icc 0 (1 / 2))ᶜ = 0) (hz : zeroMass α < 1),
    IsProbabilityMeasure (positiveLaw α) ∧ zeroAtomLaw (zeroMass α) (positiveLaw α) = α := @zeroAtomLaw_decomposition
example : ∀ (α : Measure ℝ) [IsProbabilityMeasure α] (hsupp : α (Set.Icc 0 (1 / 2))ᶜ = 0) {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hB : 0 < B),
    quantileDesignValue α ρ B ≤ 4 * zeroSelection α ρ B := @quantileDesignValue_le_four
example : ∀ (α : Measure ℝ) [IsProbabilityMeasure α] (hsupp : α (Set.Icc 0 (1 / 2))ᶜ = 0) {ρ : ℝ} (hρ1 : ρ ≤ 1) (B : ℝ),
    zeroSelection α ρ B ≤ quantileDesignValue α ρ B := @zeroSelection_le_quantileDesignValue
#print axioms ThresholdHC.ArbitraryLawAdaptation.conditionalRarity
#print axioms ThresholdHC.ArbitraryLawAdaptation.map_val_smul
#print axioms ThresholdHC.ArbitraryLawAdaptation.min_zeroMass_le_zeroSelection
#print axioms ThresholdHC.ArbitraryLawAdaptation.positiveLaw
#print axioms ThresholdHC.ArbitraryLawAdaptation.positive_selection_le_zeroSelection
#print axioms ThresholdHC.ArbitraryLawAdaptation.quantileDesignValue
#print axioms ThresholdHC.ArbitraryLawAdaptation.quantileDesignValue_le_four
#print axioms ThresholdHC.ArbitraryLawAdaptation.smul_selection_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroAtomLaw
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroAtomLaw_decomposition
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroAtomLaw_finite
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroAtomLaw_zero_atom
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroMass
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroMass_le_zeroObjective
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroObjective_quantileCore
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroQuantileValue
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroQuantileValue_le_closed
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroQuantileValue_le_four
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroQuantileValue_le_rho
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroQuantileValue_zero
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroSelection_le_quantileDesignValue
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroSelection_le_zeroQuantileValue
