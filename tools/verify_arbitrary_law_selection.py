"""Audit fractional selection transport through an increasing-gap coupling."""

import subprocess
from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ArbitraryLawAdaptation.IncreasingSelection
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EntropyTail
open ThresholdHC.Tier6 (Gap)

example : ∀ (π : Measure (Gap × Gap)) (σ : Measure Gap), selectionLift π σ =
    π.withDensity (fun z => σ.rnDeriv (π.map Prod.fst) z.1) := fun _ _ => rfl
example : ∀ (π : Measure (Gap × Gap)) (σ : Measure Gap), transportedSelection π σ =
    (selectionLift π σ).map Prod.snd := fun _ _ => rfl
example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] :
    ∀ (π : Measure Ω) {g : Ω → E} (hg : Measurable g) {w : E → ℝ≥0∞} (hw : Measurable w),
    (π.withDensity (fun z => w (g z))).map g = (π.map g).withDensity w :=
  @map_withDensity_comp Ω E _ _
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] {σ : Measure Gap}
    (hσ : σ ≤ π.map Prod.fst), (selectionLift π σ).map Prod.fst = σ := @selectionLift_first
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] {σ : Measure Gap}
    (hσ : σ ≤ π.map Prod.fst), selectionLift π σ ≤ π := @selectionLift_le
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] {σ : Measure Gap}
    (hσ : σ ≤ π.map Prod.fst), transportedSelection π σ ≤ π.map Prod.snd :=
  @transportedSelection_le
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] {σ : Measure Gap}
    (hσ : σ ≤ π.map Prod.fst), transportedSelection π σ Set.univ = σ Set.univ :=
  @transportedSelection_mass
example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] :
    ∀ {π ξ : Measure Ω} [IsFiniteMeasure ξ] (hξ : ξ ≤ π) {g : Ω → E} (hg : Measurable g),
    (π-ξ).map g = π.map g-ξ.map g := @map_sub_of_le Ω E _ _
example : ∀ (π : Measure (Gap × Gap)) (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ))
    {h : ℝ} (hh : 0 ≤ h), tailCost (π.map Prod.snd) h ≤ tailCost (π.map Prod.fst) h :=
  @tailCost_increasing_coupling
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) {σ : Measure Gap}
    (hσ : σ ≤ π.map Prod.fst) {h : ℝ} (hh : 0 ≤ h),
    gamma (transportedSelection π σ) ≤ 3*gamma σ ∧
      tailCost (π.map Prod.snd-transportedSelection π σ) h ≤ tailCost (π.map Prod.fst-σ) h :=
  @transportedSelection_costs
example : (1 : ℝ) ≤ Real.sqrt 3 := one_le_sqrt_three
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) {σ : Measure Gap}
    (hσ : σ ≤ π.map Prod.fst) (ρ B : ℝ),
    selectionObjective (π.map Prod.snd) ρ B (transportedSelection π σ) ≤
      ENNReal.ofReal (Real.sqrt 3)*selectionObjective (π.map Prod.fst) ρ B σ :=
  @transportedSelection_objective
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) (ρ B : ℝ),
    selection (π.map Prod.snd) ρ B ≤
      ENNReal.ofReal (Real.sqrt 3)*selection (π.map Prod.fst) ρ B :=
  @selection_le_sqrt_three_of_increasing_coupling
"""
    roots = {"ThresholdHC.ArbitraryLawAdaptation." + name for name in [
        "selectionLift", "transportedSelection", "map_withDensity_comp", "selectionLift_first",
        "selectionLift_le", "transportedSelection_le", "transportedSelection_mass",
        "map_sub_of_le", "tailCost_increasing_coupling", "transportedSelection_costs",
        "one_le_sqrt_three", "transportedSelection_objective",
        "selection_le_sqrt_three_of_increasing_coupling",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ArbitraryLawAdaptation.IncreasingSelection"],
                   cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
