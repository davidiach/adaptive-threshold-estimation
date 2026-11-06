"""Audit product entropy, numerical budgets, and actual light-contraction cells."""

import subprocess
from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
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
"""
    roots = {"ThresholdHC.ArbitraryLawAdaptation." + name for name in [
        "costEntropy_product_reference", "countable_product_transport", "lightCostBound", "lightReference",
        "lightCostBound_nonneg", "lightReference_pos", "lightReference_le_one", "light_exponential_cost",
        "lightReference_code_zero", "lightReference_code_succ", "lightReference_prefix", "lightCostBound_prefix",
        "lightReference_code_prefix", "duplicate_prefix", "duplicate_prefix_le", "lightReference_duplicate_prefix",
        "lightReference_duplicate_code_prefix", "lightGap", "measurable_lightGap", "bandIndex_le_of_lower",
        "bandIndex_ge_of_upper", "lightGap_bands", "lightTag", "lightDest", "measurable_lightTag",
        "lightTag_multiplier", "lightTag_destination", "lightGap_inverseSquare", "light_band_budget",
        "light_prod_support", "bandCost_index", "lintegral_bandIndex_indicator", "product_band_cost",
        "light_cell_bound", "light_column_cost", "gamma_light_contraction",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ArbitraryLawAdaptation.LightContractionCells"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
