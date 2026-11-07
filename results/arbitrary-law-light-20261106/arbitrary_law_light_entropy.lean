
import ThresholdHC.ArbitraryLawAdaptation.LightContractionCells
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set Real
open scoped ENNReal BigOperators
open ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

example {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ∀ {a : ι → ℝ} {t p : κ → ℝ}, (∀ i, 0 ≤ a i) → (∀ k, 0 ≤ t k) →
      (∀ k, 0 < p k) → (∑ k, p k) ≤ 1 →
    ThresholdHC.EntropyTailQuantile.costEntropy (fun x : ι × κ => a x.1*t x.2) ≤
      (∑ k, t k*(1-log (p k)))*ThresholdHC.EntropyTailQuantile.costEntropy a :=
  @costEntropy_product_reference ι κ _ _
example : ∀ {a t p : ℕ → ℝ} {b : ℕ × ℕ → ℝ} {C : ℝ},
    (∀ i, 0 ≤ a i) → (∀ k, 0 ≤ t k) → (∀ x, 0 ≤ b x) → (∀ k, 0 < p k) →
    (∀ n, (∑ k : Fin n, p k.val) ≤ 1) →
    (∀ n, (∑ k : Fin n, t k.val*(1-log (p k.val))) ≤ C) →
    0 ≤ C → (∀ x, b x ≤ a x.1*t x.2) → ∀ dest : ℕ × ℕ → ℕ,
    (∀ j, Summable (fun x => if dest x = j then b x else 0)) →
    countableEntropy (fun j => ∑' x, if dest x = j then b x else 0) ≤
      ENNReal.ofReal C*countableEntropy a := @countable_product_transport

example : ∀ n, lightCostBound n = if n = 0 then 256 else 3*(1/64 : ℝ)^n := fun _ => rfl
example : ∀ n, lightReference n = if n = 0 then 7/16 else (1/2 : ℝ)^(n+4) := fun _ => rfl
example : ∀ n, 0 ≤ lightCostBound n := lightCostBound_nonneg
example : ∀ n, 0 < lightReference n := lightReference_pos
example : ∀ n, lightReference n ≤ 1 := lightReference_le_one
example : ∀ n : ℕ, (4 : ℝ)^(n+4)*(2*exp (-((4 : ℝ)^(n+2)/2))) ≤ 3*(1/64 : ℝ)^n :=
  light_exponential_cost
example : 256*(1-log (lightReference 0)) ≤ 485 := lightReference_code_zero
example : ∀ n : ℕ, lightCostBound (n+1)*(1-log (lightReference (n+1))) ≤ 9*(1/32 : ℝ)^(n+1) :=
  lightReference_code_succ
example : ∀ n : ℕ, (∑ k : Fin n, lightReference k.val) ≤ 1/2 := lightReference_prefix
example : ∀ n : ℕ, (∑ k : Fin n, lightCostBound k.val) ≤ 257 := lightCostBound_prefix
example : ∀ n : ℕ, (∑ k : Fin n, lightCostBound k.val*(1-log (lightReference k.val))) ≤ 486 :=
  lightReference_code_prefix
example : ∀ (f : ℕ → ℝ) (n : ℕ), (∑ k : Fin (2*n), f (k.val/2)) = 2*∑ k : Fin n, f k.val :=
  duplicate_prefix
example : ∀ {f : ℕ → ℝ}, (∀ k, 0 ≤ f k) → ∀ n : ℕ,
    (∑ k : Fin n, f (k.val/2)) ≤ 2*∑ k : Fin n, f k.val := @duplicate_prefix_le
example : ∀ n : ℕ, (∑ k : Fin n, lightReference (k.val/2)) ≤ 1 := lightReference_duplicate_prefix
example : ∀ n : ℕ,
    (∑ k : Fin n, lightCostBound (k.val/2)*(1-log (lightReference (k.val/2)))) ≤ 1024 :=
  lightReference_duplicate_code_prefix

example : ∀ z : Gap × Gap, (lightGap z : ℝ) = (z.1 : ℝ)*(z.2 : ℝ)/2 := fun _ => rfl
example : Measurable lightGap := measurable_lightGap
example : ∀ {d : Gap} {m : ℕ}, (1/2 : ℝ)^(m+2) < (d : ℝ) → bandIndex d ≤ m :=
  @bandIndex_le_of_lower
example : ∀ {d : Gap} {m : ℕ}, (d : ℝ) ≤ (1/2 : ℝ)^(m+1) → m ≤ bandIndex d :=
  @bandIndex_ge_of_upper
example : ∀ z : Gap × Gap,
    bandIndex z.1+bandIndex z.2+2 ≤ bandIndex (lightGap z) ∧
      bandIndex (lightGap z) ≤ bandIndex z.1+bandIndex z.2+3 := lightGap_bands
example : ∀ z : Gap × Gap, lightTag z =
    (bandIndex z.1, 2*(bandIndex z.2-1)+(bandIndex (lightGap z)-(bandIndex z.1+(bandIndex z.2-1)+3))) :=
  fun _ => rfl
example : ∀ x : ℕ × ℕ, lightDest x = x.1+x.2/2+3+x.2%2 := fun _ => rfl
example : Measurable lightTag := measurable_lightTag
example : ∀ {z : Gap × Gap}, (z.2 : ℝ) ≤ 1/4 → (lightTag z).2/2+1 = bandIndex z.2 :=
  @lightTag_multiplier
example : ∀ {z : Gap × Gap}, (z.2 : ℝ) ≤ 1/4 → lightDest (lightTag z) = bandIndex (lightGap z) :=
  @lightTag_destination
example : ∀ z : Gap × Gap,
    (lightGap z : ℝ)⁻¹^2 ≤ (4 : ℝ)^(bandIndex z.2+3)*(z.1 : ℝ)⁻¹^2 := lightGap_inverseSquare

example : ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤ ENNReal.ofReal (2*exp (-((4 : ℝ)^(n+2)/2)))) →
    ∀ n : ℕ, ENNReal.ofReal ((4 : ℝ)^(n+4))*ν (band (n+1)) ≤ ENNReal.ofReal (lightCostBound n) :=
  @light_band_budget
example : ∀ (σ ν : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure ν],
    (∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) → ∀ᵐ (z : Gap × Gap) ∂σ.prod ν, (z.2 : ℝ) ≤ 1/4 :=
  @light_prod_support
example : ∀ (σ : Measure Gap) (i : ℕ),
    bandCost σ i = ∫⁻ d, if bandIndex d = i then inverseWeight d else 0 ∂σ := bandCost_index
example : ∀ (ν : Measure Gap) (j : ℕ),
    (∫⁻ v, if bandIndex v = j then (1 : ℝ≥0∞) else 0 ∂ν) = ν (band j) := lintegral_bandIndex_indicator
example : ∀ (σ ν : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure ν] (i j : ℕ),
    (∫⁻ z, if bandIndex z.1 = i ∧ bandIndex z.2 = j then inverseWeight z.1 else 0 ∂σ.prod ν) =
      bandCost σ i*ν (band j) := @product_band_cost
example : ∀ (σ ν : Measure Gap) [IsFiniteMeasure σ] [IsProbabilityMeasure ν],
    (∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) →
    (∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤ ENNReal.ofReal (2*exp (-((4 : ℝ)^(n+2)/2)))) →
    ∀ x : ℕ × ℕ, cellCost (σ.prod ν) lightTag (fun z => inverseWeight (lightGap z)) x ≤
      bandCost σ x.1*ENNReal.ofReal (lightCostBound (x.2/2)) := @light_cell_bound
example : ∀ (σ ν : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure ν],
    (∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) → ∀ j : ℕ,
    (∑' x, if lightDest x = j then cellCost (σ.prod ν) lightTag (fun z => inverseWeight (lightGap z)) x else 0) =
      bandCost ((σ.prod ν).map lightGap) j := @light_column_cost
example : ∀ (σ ν : Measure Gap) [IsFiniteMeasure σ] [IsProbabilityMeasure ν],
    (∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) →
    (∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤ ENNReal.ofReal (2*exp (-((4 : ℝ)^(n+2)/2)))) →
    gamma ((σ.prod ν).map lightGap) ≤ 1024*gamma σ := @gamma_light_contraction
#print axioms ThresholdHC.ArbitraryLawAdaptation.bandCost_index
#print axioms ThresholdHC.ArbitraryLawAdaptation.bandIndex_ge_of_upper
#print axioms ThresholdHC.ArbitraryLawAdaptation.bandIndex_le_of_lower
#print axioms ThresholdHC.ArbitraryLawAdaptation.costEntropy_product_reference
#print axioms ThresholdHC.ArbitraryLawAdaptation.countable_product_transport
#print axioms ThresholdHC.ArbitraryLawAdaptation.duplicate_prefix
#print axioms ThresholdHC.ArbitraryLawAdaptation.duplicate_prefix_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.gamma_light_contraction
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightCostBound
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightCostBound_nonneg
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightCostBound_prefix
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightDest
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightGap
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightGap_bands
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightGap_inverseSquare
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightReference
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightReference_code_prefix
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightReference_code_succ
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightReference_code_zero
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightReference_duplicate_code_prefix
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightReference_duplicate_prefix
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightReference_le_one
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightReference_pos
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightReference_prefix
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightTag
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightTag_destination
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightTag_multiplier
#print axioms ThresholdHC.ArbitraryLawAdaptation.light_band_budget
#print axioms ThresholdHC.ArbitraryLawAdaptation.light_cell_bound
#print axioms ThresholdHC.ArbitraryLawAdaptation.light_column_cost
#print axioms ThresholdHC.ArbitraryLawAdaptation.light_exponential_cost
#print axioms ThresholdHC.ArbitraryLawAdaptation.light_prod_support
#print axioms ThresholdHC.ArbitraryLawAdaptation.lintegral_bandIndex_indicator
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_lightGap
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_lightTag
#print axioms ThresholdHC.ArbitraryLawAdaptation.product_band_cost
