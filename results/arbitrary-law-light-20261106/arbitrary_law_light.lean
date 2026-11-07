
import ThresholdHC.ArbitraryLawAdaptation.LightMultiplier
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set Real
open scoped ENNReal BigOperators unitInterval
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EntropyTail
open ThresholdHC.Tier6 (Gap)

example : ∀ v : Gap, lightInverse v = ENNReal.ofReal (2/(v : ℝ)) := fun _ => rfl
example : Measurable lightInverse := measurable_lightInverse
example : ∀ {v : Gap} {n : ℕ}, bandIndex v = n+1 →
    2/(v : ℝ) ≤ (1/16 : ℝ)*(4 : ℝ)^(n+4) := @lightInverse_band
example : ∀ ν : Measure Gap, (∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) →
    cellCost ν bandIndex lightInverse 0 = 0 := lightInverse_cell_zero
example : ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤ ENNReal.ofReal (2*exp (-((4 : ℝ)^(n+2)/2)))) →
    ∀ n : ℕ, cellCost ν bandIndex lightInverse (n+1) ≤
      ENNReal.ofReal (1/16 : ℝ)*ENNReal.ofReal (lightCostBound n) := @lightInverse_cell_budget
example : (∑' n, ENNReal.ofReal (lightCostBound n)) ≤ 257 := lightCostBound_tsum
example : ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) →
    (∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤ ENNReal.ofReal (2*exp (-((4 : ℝ)^(n+2)/2)))) →
    (∫⁻ v, lightInverse v ∂ν) ≤ 32 := @lightInverse_integral
example : ∀ (z : Gap × Gap) {h : ℝ}, 0 ≤ h →
    ENNReal.ofReal (min 1 (h/(lightGap z : ℝ))) ≤
      ENNReal.ofReal (min 1 (h/(z.1 : ℝ)))*lightInverse z.2 := @lightGap_tail_kernel
example : ∀ (sel ν : Measure Gap) [IsFiniteMeasure sel] [IsProbabilityMeasure ν],
    (∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) →
    (∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤ ENNReal.ofReal (2*exp (-((4 : ℝ)^(n+2)/2)))) →
    ∀ {h : ℝ}, 0 ≤ h → tailCost ((sel.prod ν).map lightGap) h ≤ 32*tailCost sel h :=
  @tailCost_light_contraction

example : ∀ x : ℝ, lightCDF x =
    if x ≤ 0 then 0 else if x < 1/4 then 2*exp (-(1/(2*x^2))) else 1 := fun _ => rfl
example : ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    ∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4 := @lightCDF_support
example : ∀ ν : Measure Gap,
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    ∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤ ENNReal.ofReal (2*exp (-((4 : ℝ)^(n+2)/2))) :=
  lightCDF_band_bound
example : ∀ {μ sel : Measure Gap} (ν : Measure Gap) [IsProbabilityMeasure ν], sel ≤ μ →
    (sel.prod ν).map lightGap ≤ (μ.prod ν).map lightGap := @lightSelection_le
example : ∀ {μ sel : Measure Gap} [IsFiniteMeasure μ] (ν : Measure Gap) [IsProbabilityMeasure ν], sel ≤ μ →
    (μ.prod ν).map lightGap-(sel.prod ν).map lightGap = ((μ-sel).prod ν).map lightGap := @lightSelection_residual
example : ∀ {μ sel : Measure Gap} [IsFiniteMeasure μ] (ν : Measure Gap) [IsProbabilityMeasure ν], sel ≤ μ →
    (∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) →
    (∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤ ENNReal.ofReal (2*exp (-((4 : ℝ)^(n+2)/2)))) →
    ∀ ρ B : ℝ, selectionObjective ((μ.prod ν).map lightGap) ρ B ((sel.prod ν).map lightGap) ≤
      32*selectionObjective μ ρ B sel := @lightSelection_objective
example : ∀ (μ ν : Measure Gap) [IsFiniteMeasure μ] [IsProbabilityMeasure ν],
    (∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) →
    (∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤ ENNReal.ofReal (2*exp (-((4 : ℝ)^(n+2)/2)))) →
    ∀ ρ B : ℝ, selection ((μ.prod ν).map lightGap) ρ B ≤ 32*selection μ ρ B :=
  @selection_light_contraction_of_bands
example : ∀ (μ ν : Measure Gap) [IsFiniteMeasure μ] [IsProbabilityMeasure ν],
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    ∀ ρ B : ℝ, selection ((μ.prod ν).map lightGap) ρ B ≤ 32*selection μ ρ B :=
  @selection_light_contraction

example : ∀ (u : I), 0 < (u : ℝ) → 0 < 2*log (2/(u : ℝ)) := lightLog_pos
example : ∀ u : I, (lightQuantile u : ℝ) =
    if 0 < (u : ℝ) then min (1/4) (sqrt (2*log (2/(u : ℝ))))⁻¹ else 1/4 := fun _ => rfl
example : Measurable lightQuantile := measurable_lightQuantile
example : ∀ u : I, (lightQuantile u : ℝ) ≤ 1/4 := lightQuantile_le_quarter
example : ∀ (u : I) {x : ℝ}, 0 < x → x < 1/4 →
    ((lightQuantile u : ℝ) ≤ x ↔ 0 < (u : ℝ) ∧ (u : ℝ) ≤ 2*exp (-(1/(2*x^2)))) :=
  @lightQuantile_le_iff
example : lightMultiplier = (volume : Measure I).map lightQuantile := rfl
example : IsProbabilityMeasure lightMultiplier := lightMultiplier_probability
example : ∀ x : ℝ, lightMultiplier {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x) :=
  lightMultiplier_cdf
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (ρ B : ℝ),
    selection ((μ.prod lightMultiplier).map lightGap) ρ B ≤ 32*selection μ ρ B :=
  @selection_lightMultiplier
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightCDF
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightCDF_band_bound
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightCDF_support
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightCostBound_tsum
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightGap_tail_kernel
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightInverse
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightInverse_band
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightInverse_cell_budget
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightInverse_cell_zero
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightInverse_integral
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightLog_pos
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightMultiplier
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightMultiplier_cdf
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightMultiplier_probability
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightQuantile
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightQuantile_le_iff
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightQuantile_le_quarter
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightSelection_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightSelection_objective
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightSelection_residual
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_lightInverse
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_lightQuantile
#print axioms ThresholdHC.ArbitraryLawAdaptation.selection_lightMultiplier
#print axioms ThresholdHC.ArbitraryLawAdaptation.selection_light_contraction
#print axioms ThresholdHC.ArbitraryLawAdaptation.selection_light_contraction_of_bands
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailCost_light_contraction
