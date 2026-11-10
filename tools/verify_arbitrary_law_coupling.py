"""Audit canonical band cells and entropy under an increasing-gap coupling."""

import subprocess
from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ArbitraryLawAdaptation.CouplingEntropy
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory
open scoped BigOperators ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EntropyTail
open ThresholdHC.Tier6 (Gap)

example : ∀ d : Gap, bandIndex d = (exists_band d).choose := fun _ => rfl
example : ∀ d : Gap, d ∈ band (bandIndex d) := mem_bandIndex
example : ∀ (d : Gap) (j : ℕ), bandIndex d = j ↔ d ∈ band j := bandIndex_eq_iff
example : Measurable bandIndex := measurable_bandIndex
example : ∀ {x y : Gap}, (x : ℝ) ≤ (y : ℝ) → bandIndex y ≤ bandIndex x :=
  @bandIndex_antitone
example : ∀ {x y : Gap}, (x : ℝ) ≤ (y : ℝ) →
    (y : ℝ)⁻¹^2 ≤ min 1 (4*(1/4 : ℝ)^(bandIndex x-bandIndex y))*(x : ℝ)⁻¹^2 :=
  @inverseSquare_band_contraction

example {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] :
    ∀ (π : Measure Ω) (tag : Ω → ι) (w : Ω → ℝ≥0∞) (i : ι),
    cellCost π tag w i = ∫⁻ z, if tag z = i then w z else 0 ∂π := fun _ _ _ _ => rfl
example {Ω ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Countable ι] [DecidableEq ι] [DecidableEq κ] :
    ∀ (π : Measure Ω) {tag : Ω → ι} (htag : Measurable tag)
    {w : Ω → ℝ≥0∞} (hw : Measurable w) (dest : ι → κ) (j : κ),
    (∑' i, if dest i = j then cellCost π tag w i else 0) =
      ∫⁻ z, if dest (tag z) = j then w z else 0 ∂π := @cellCost_merge Ω ι κ _ _ _ _ _ _

example : ∀ d : Gap, inverseWeight d = ENNReal.ofReal ((d : ℝ)⁻¹^2) := fun _ => rfl
example : Measurable inverseWeight := measurable_inverseWeight
example : ∀ z : Gap × Gap, transportTag z = (bandIndex z.1, bandIndex z.1-bandIndex z.2) :=
  fun _ => rfl
example : ∀ x : ℕ × ℕ, transportDest x = x.1-x.2 := fun _ => rfl
example : Measurable transportTag := measurable_transportTag
example : ∀ {z : Gap × Gap}, (z.1 : ℝ) ≤ (z.2 : ℝ) →
    transportDest (transportTag z) = bandIndex z.2 := @transportTag_destination
example {Ω : Type*} [MeasurableSpace Ω] : ∀ (π : Measure Ω) {g : Ω → Gap}
    (hg : Measurable g) (j : ℕ),
    bandCost (π.map g) j = ∫⁻ z, if bandIndex (g z) = j then inverseWeight (g z) else 0 ∂π :=
  @bandCost_map_index Ω _
example : ∀ (π : Measure (Gap × Gap)) (i : ℕ),
    (∑' k, cellCost π transportTag (fun z => inverseWeight z.1) (i,k)) =
      bandCost (π.map Prod.fst) i := coupling_row_cost
example : ∀ (π : Measure (Gap × Gap)) (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) (j : ℕ),
    (∑' x, if transportDest x = j then cellCost π transportTag (fun z => inverseWeight z.2) x else 0) =
      bandCost (π.map Prod.snd) j := coupling_column_cost
example : ∀ (π : Measure (Gap × Gap)) (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) (x : ℕ × ℕ),
    cellCost π transportTag (fun z => inverseWeight z.2) x ≤
      ENNReal.ofReal (min 1 (4*(1/4 : ℝ)^x.2))*
        cellCost π transportTag (fun z => inverseWeight z.1) x := coupling_cell_contraction
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)),
    gamma (π.map Prod.snd) ≤ 3*gamma (π.map Prod.fst) :=
  @gamma_le_three_of_increasing_coupling
"""
    roots = {"ThresholdHC.ArbitraryLawAdaptation." + name for name in [
        "bandIndex", "mem_bandIndex", "bandIndex_eq_iff", "measurable_bandIndex",
        "bandIndex_antitone", "inverseSquare_band_contraction", "cellCost", "cellCost_merge",
        "inverseWeight", "measurable_inverseWeight", "transportTag", "transportDest",
        "measurable_transportTag", "transportTag_destination", "bandCost_map_index",
        "coupling_row_cost", "coupling_column_cost", "coupling_cell_contraction",
        "gamma_le_three_of_increasing_coupling",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ArbitraryLawAdaptation.CouplingEntropy"],
                   cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
