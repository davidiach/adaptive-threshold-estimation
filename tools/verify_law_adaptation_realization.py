"""Exact theorem types and transitive axioms for observable law adaptation."""

import subprocess
from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.LawAdaptation.Moments
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory
open ThresholdHC.Tier6 ThresholdHC.LawAdaptation

example : ∀ (μ ν : Measure unitInterval)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ k : ℕ, ∫ x, (x:ℝ)^k ∂μ = ∫ x, (x:ℝ)^k ∂ν),
    μ = ν := @unitInterval_eq_of_moments

example : Measurable squaredGap := measurable_squaredGap

example : Function.Injective squaredGap := squaredGap_injective

example : ∀ (μ ν : Measure Gap)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ k : ℕ, 0 < k → evenMoment μ k = evenMoment ν k),
    μ = ν := @gapLaw_eq_of_evenMoments

example : ∀ (μ ν : Measure Gap)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hne : μ ≠ ν),
    ∃ k : ℕ, 0 < k ∧ evenMoment μ k ≠ evenMoment ν k := @exists_separating_moment

example : ∀ {ι : Type*} [Fintype ι] [Nonempty ι]
    (laws : ι → Measure Gap) [∀ i, IsProbabilityMeasure (laws i)]
    (hinj : Function.Injective laws),
    ∃ m : ℕ, 0 < m ∧ ∃ η : ℝ, 0 < η ∧
      ∀ i j, i ≠ j → ∃ k : Fin m,
        η ≤ |evenMoment (laws i) (k.val+1) - evenMoment (laws j) (k.val+1)| :=
  @finite_moment_separation
"""
    roots = {"ThresholdHC.LawAdaptation." + name for name in [
        "unitInterval_eq_of_moments", "measurable_squaredGap", "squaredGap_injective",
        "gapLaw_eq_of_evenMoments", "exists_separating_moment", "finite_moment_separation",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.LawAdaptation.Moments"],
                   cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} exact statements and transitive axiom reports")


if __name__ == "__main__":
    main()

