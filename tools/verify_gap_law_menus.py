"""Exact theorem types and transitive axioms for finite gap-law menu realization."""

import subprocess
from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.GapLawMenus.Atoms
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory
open scoped BigOperators ENNReal Classical
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix
open ThresholdHC.BandCostSelection ThresholdHC.GapLawMenus

example : ∀ (F : Finset Gap) (js : List ℕ)
    (hcover : ∀ d ∈ F, bandIndex d ∈ js),
    (enumerate (menus F js)).image traceSet = suffixChoices F := @trace_image

example : ∀ (F : Finset Gap) (js : List ℕ) {xs : List (Finset Gap)}
    (hx : xs ∈ enumerate (menus F js)) {d : Gap} (hd : d ∈ traceSet xs),
    bandIndex d ∈ js := @trace_band_mem

example : ∀ (F : Finset Gap) {j : ℕ} {js : List ℕ}
    (hj : j ∉ js) {S : Finset Gap} (hS : S ∈ suffixChoices (slice F j))
    {xs : List (Finset Gap)} (hx : xs ∈ enumerate (menus F js)),
    Disjoint S (traceSet xs) := @head_disjoint_tail

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hF : μ.support.Finite) (js : List ℕ)
    (hcover : ∀ d ∈ hF.toFinset, bandIndex d ∈ js)
    {ρ B : ℝ} (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hB : 0 < B),
    ∃ xs ∈ enumerate (menus hF.toFinset js), ∀ σ : Measure Gap, σ ≤ μ →
      selectionObjective μ ρ B (μ.restrict (traceSet xs)) ≤ selectionObjective μ ρ B σ :=
  @menu_attains

example : ∀ (σ : Measure Gap) [IsFiniteMeasure σ]
    (js : List ℕ) (hj : js.Nodup)
    (hz : ∀ j, j ∉ js → bandCost σ j = 0),
    gamma σ = ENNReal.ofReal (multisetEntropy (↑(js.map fun j => (bandCost σ j).toReal))) :=
  @gamma_list

example : ∀ (μ : Measure Gap) (F : Finset Gap) (js : List ℕ) (hj : js.Nodup)
    {xs : List (Finset Gap)} (hx : xs ∈ enumerate (menus F js)),
    xs.map (cost μ) = js.map (fun j => (bandCost (μ.restrict (traceSet xs)) j).toReal) :=
  @trace_costs

example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ]
    (F : Finset Gap) (js : List ℕ) (hj : js.Nodup)
    {xs : List (Finset Gap)} (hx : xs ∈ enumerate (menus F js)),
    gamma (μ.restrict (traceSet xs)) =
      ENNReal.ofReal (multisetEntropy (traceKey (cost μ) xs)) := @trace_gamma

example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (h : ℝ)
    (F : Finset Gap) (js : List ℕ) (hj : js.Nodup)
    {xs : List (Finset Gap)} (hx : xs ∈ enumerate (menus F js)),
    traceSaved (saving μ h) xs = (tailCost (μ.restrict (traceSet xs)) h).toReal :=
  @trace_saving

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    (F : Finset Gap) (js : List ℕ) (hj : js.Nodup)
    {xs : List (Finset Gap)} (hx : xs ∈ enumerate (menus F js))
    {ρ : ℝ} (hr : 0 ≤ ρ) (B : ℝ),
    ENNReal.ofReal (menuObjective μ ρ B xs) =
      min (ENNReal.ofReal ρ) (selectionObjective μ ρ B (μ.restrict (traceSet xs))) :=
  @menuObjective_eq

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hF : μ.support.Finite) (js : List ℕ) (hj : js.Nodup)
    (hcover : ∀ d ∈ hF.toFinset, bandIndex d ∈ js)
    {ρ B : ℝ} (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hB : 0 < B),
    ∃ xs ∈ solve (cost μ) (saving μ (1/Real.sqrt B)) (menus hF.toFinset js),
      traceSet xs ∈ suffixChoices hF.toFinset ∧
      selection μ ρ B = ENNReal.ofReal (menuObjective μ ρ B xs) := @compressed_attains

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hF : μ.support.Finite) {ρ B : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hB : 0 < B),
    ∃ xs ∈ solve (cost μ) (saving μ (1/Real.sqrt B))
        (menus hF.toFinset (occupiedBands hF.toFinset)),
      traceSet xs ∈ suffixChoices hF.toFinset ∧
      selection μ ρ B = ENNReal.ofReal (menuObjective μ ρ B xs) := @finite_law_solver

example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (S : Finset Gap),
    cost μ S = ∑ d ∈ S, (μ {d}).toReal * ((d:ℝ)⁻¹)^2 := @cost_atomic

example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (S : Finset Gap)
    {h : ℝ} (hh : 0 ≤ h),
    saving μ h S = ∑ d ∈ S, (μ {d}).toReal * min 1 (h/(d:ℝ)) := @saving_atomic
"""
    roots = {"ThresholdHC.GapLawMenus." + name for name in [
        "trace_image", "trace_band_mem", "head_disjoint_tail", "menu_attains",
        "gamma_list", "trace_costs", "trace_gamma", "trace_saving", "menuObjective_eq",
        "compressed_attains", "finite_law_solver", "cost_atomic", "saving_atomic",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.GapLawMenus.Atoms"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} exact statements and transitive axiom reports")


if __name__ == "__main__":
    main()

