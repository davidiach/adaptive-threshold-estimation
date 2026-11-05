"""Exact types and axioms for output-preserving finite-cap truncation."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.FiniteCapTruncation.Risk
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie ThresholdHC.RareAboveTwo
open ThresholdHC.FiniteCapTruncation

example : ∀ {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M) (f : Flow M)
    (hf : FlowCone f), FlowCone (capFlow N f) := @capFlow_cone

example : ∀ {M : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (N : ℕ) (f : Flow M) (hf : FlowCone f),
    ((N:ℝ)+1) * discardedMean μ q N f.stopWeight ≤
      countMean μ q f.continueWeight := @discarded_mass_work

example : ∀ {M : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (N : ℕ) (f : Flow M) (hf : FlowCone f)
    {B V : ℝ} (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hw : countMean μ q f.continueWeight ≤ B)
    (hv : countMean μ q f.momentWeight ≤ V),
    |discardedMean μ q N f.outputWeight| ≤ Real.sqrt (B*V/((N:ℝ)+1)) :=
  @discarded_output_bound

example : ∀ {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ} (hB : 0 ≤ B)
    (C : Certificate M) (hC : Feasible μ ρ B C),
    Feasible μ ρ B (capCertificate N B C) := @capCertificate_feasible

example : ∀ {M : ℕ} (N : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (C : Certificate M) (hV : 0 ≤ C.variance),
    certificateSquared (capCertificate N B C) ≤
      ENNReal.ofReal ((1+Real.sqrt (B/((N:ℝ)+1)))^2) * certificateSquared C :=
  @capCertificate_squared

example : ∀ {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) {B : ℝ} (hB : 0 ≤ B),
    programSquared μ ρ B N ≤
      ENNReal.ofReal ((1+Real.sqrt (B/((N:ℝ)+1)))^2) * programSquared μ ρ B M :=
  @programSquared_cap_le

example : ∀ {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) {B : ℝ} (hB : 0 ≤ B),
    programValue μ ρ B N ≤
      ENNReal.ofReal (1+Real.sqrt (B/((N:ℝ)+1))) * programValue μ ρ B M :=
  @programValue_cap_le

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ)
    {B : ℝ} (hB : 0 ≤ B) (N : ℕ) (hN : 0 < N),
    infiniteProgramValue μ ρ B ≤ programValue μ ρ B N ∧
      programValue μ ρ B N ≤
        ENNReal.ofReal (1+Real.sqrt (B/((N:ℝ)+1))) * infiniteProgramValue μ ρ B :=
  @ordinary_cap_rate

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B)
    (N : ℕ) (hN : 0 < N),
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
      programValue μ ρ B N ≤ ENNReal.ofReal (8*(1+Real.sqrt (B/((N:ℝ)+1)))) *
        rareMinimaxRisk μ ρ B := @ordinary_cap_minimax

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B)
    (N : ℕ) (hN : 0 < N) (hcap : B ≤ (N:ℝ)+1),
    programValue μ ρ B N ≤ 16 * rareMinimaxRisk μ ρ B := @ordinary_linear_cap
"""
    roots = {"ThresholdHC.FiniteCapTruncation." + n for n in [
        "capFlow_cone", "discarded_mass_work", "discarded_output_bound",
        "capCertificate_feasible", "capCertificate_squared", "programSquared_cap_le",
        "programValue_cap_le", "ordinary_cap_rate", "ordinary_cap_minimax", "ordinary_linear_cap",
    ]}
    return source + "".join("#print axioms " + n + "\n" for n in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.FiniteCapTruncation.Risk"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} exact statements and transitive axiom reports")


if __name__ == "__main__":
    main()

