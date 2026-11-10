"""Audit density restriction and the zero-atom dominated-mass comparison (A5)."""

import subprocess
from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ArbitraryLawAdaptation.DominatedMass
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EntropyTail
open ThresholdHC.Tier6 (Gap)

example : ∀ (σ : Measure Gap) [IsFiniteMeasure σ] {c : ℝ}, 0 ≤ c →
    gamma (ENNReal.ofReal c • σ) = ENNReal.ofReal c*gamma σ := @canonicalGamma_smul
example : ∀ {σ τ : Measure ℝ} [IsFiniteMeasure τ], σ ≤ τ → zeroGamma σ ≤ zeroGamma τ :=
  @zeroGamma_mono
example : ∀ (σ : Measure ℝ) [IsFiniteMeasure σ] {c : ℝ}, 0 ≤ c →
    zeroGamma (ENNReal.ofReal c • σ) = ENNReal.ofReal c*zeroGamma σ := @zeroGamma_smul
example : ∀ {μ ν : Measure ℝ}, μ ≤ ν → ∀ t : ℝ, zeroTailCost μ t ≤ zeroTailCost ν t :=
  @zeroTailCost_mono
example : ∀ (μ ν : Measure ℝ) (t : ℝ),
    zeroTailCost (μ+ν) t = zeroTailCost μ t+zeroTailCost ν t := zeroTailCost_add
example : ∀ (c : ℝ≥0∞) (μ : Measure ℝ) (t : ℝ),
    zeroTailCost (c • μ) t = c*zeroTailCost μ t := zeroTailCost_smul
example : ∀ t : ℝ, zeroTailCost (Measure.dirac 0) t = 1 := zeroTailCost_dirac_zero

example {E : Type*} [MeasurableSpace E] : ∀ {μ ν : Measure E}, μ ≤ ν →
    ∀ w : E → ℝ≥0∞, μ.withDensity w ≤ ν.withDensity w := @withDensity_base_mono E _
example : ∀ (ζ ν : Measure ℝ) (x : ℝ), dominatedDensity ζ ν x = min 1 (ζ.rnDeriv ν x) :=
  fun _ _ _ => rfl
example : ∀ ζ ν σ : Measure ℝ,
    dominatedSelection ζ ν σ = σ.withDensity (dominatedDensity ζ ν) := fun _ _ _ => rfl
example : ∀ (ζ ν : Measure ℝ) (x : ℝ), dominatedDensity ζ ν x ≤ 1 := dominatedDensity_le_one
example : ∀ {ζ ν : Measure ℝ} [IsFiniteMeasure ν], ζ ≤ ν →
    ν.withDensity (dominatedDensity ζ ν) = ζ := @dominatedDensity_recovers
example : ∀ ζ ν σ : Measure ℝ, dominatedSelection ζ ν σ ≤ σ := dominatedSelection_le
example : ∀ {ζ ν σ : Measure ℝ} [IsFiniteMeasure ν], ζ ≤ ν → σ ≤ ν →
    dominatedSelection ζ ν σ ≤ ζ := @dominatedSelection_le_law
example : ∀ {ζ ν σ : Measure ℝ} [IsFiniteMeasure ν], ζ ≤ ν → σ ≤ ν →
    ζ-dominatedSelection ζ ν σ = (ν-σ).withDensity (dominatedDensity ζ ν) :=
  @dominatedSelection_residual
example : ∀ {ζ ν σ : Measure ℝ} [IsFiniteMeasure ν], ζ ≤ ν → σ ≤ ν →
    ζ-dominatedSelection ζ ν σ ≤ ν-σ := @dominatedSelection_residual_le
example : ∀ {ζ ν σ : Measure ℝ} [IsFiniteMeasure ν], ζ ≤ ν → σ ≤ ν → ∀ ρ B : ℝ,
    zeroObjective ζ ρ B (dominatedSelection ζ ν σ) ≤ zeroObjective ν ρ B σ :=
  @dominatedSelection_objective
example : ∀ {ζ ν : Measure ℝ} [IsFiniteMeasure ν], ζ ≤ ν → ∀ ρ B : ℝ,
    zeroSelection ζ ρ B ≤ zeroSelection ν ρ B := @zeroSelection_mono

example : ∀ {η σ : Measure ℝ} [IsFiniteMeasure η], σ ≤ η → ∀ c e : ℝ,
    (ENNReal.ofReal c • η+ENNReal.ofReal e • Measure.dirac 0)-ENNReal.ofReal c • σ =
      ENNReal.ofReal c • (η-σ)+ENNReal.ofReal e • Measure.dirac 0 := @scaledSelection_residual
example : ∀ {η σ : Measure ℝ} [IsFiniteMeasure η], σ ≤ η → ∀ {c : ℝ}, 1 ≤ c → ∀ e ρ B : ℝ,
    zeroObjective (ENNReal.ofReal c • η+ENNReal.ofReal e • Measure.dirac 0) ρ B
        (ENNReal.ofReal c • σ) ≤ ENNReal.ofReal c*zeroObjective η ρ B σ+ENNReal.ofReal e :=
  @scaledSelection_objective
example : ∀ (η : Measure ℝ) [IsFiniteMeasure η] {c : ℝ}, 1 ≤ c → ∀ e ρ B : ℝ,
    zeroSelection (ENNReal.ofReal c • η+ENNReal.ofReal e • Measure.dirac 0) ρ B ≤
      ENNReal.ofReal c*zeroSelection η ρ B+ENNReal.ofReal e := @zeroSelection_scaled_add_zero
example : ∀ {ζ η : Measure ℝ} [IsFiniteMeasure η] {c e : ℝ}, 1 ≤ c →
    ζ ≤ ENNReal.ofReal c • η+ENNReal.ofReal e • Measure.dirac 0 → ∀ ρ B : ℝ,
    zeroSelection ζ ρ B ≤ ENNReal.ofReal c*zeroSelection η ρ B+ENNReal.ofReal e :=
  @zeroSelection_dominated_mass
"""
    roots = {"ThresholdHC.ArbitraryLawAdaptation." + name for name in [
        "canonicalGamma_smul", "zeroGamma_mono", "zeroGamma_smul", "zeroTailCost_mono",
        "zeroTailCost_add", "zeroTailCost_smul", "zeroTailCost_dirac_zero", "withDensity_base_mono",
        "dominatedDensity", "dominatedSelection", "dominatedDensity_le_one", "dominatedDensity_recovers",
        "dominatedSelection_le", "dominatedSelection_le_law", "dominatedSelection_residual",
        "dominatedSelection_residual_le", "dominatedSelection_objective", "zeroSelection_mono",
        "scaledSelection_residual", "scaledSelection_objective", "zeroSelection_scaled_add_zero",
        "zeroSelection_dominated_mass",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ArbitraryLawAdaptation.DominatedMass"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
