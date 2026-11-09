"""Audit common-uniform coupling existence, including atoms at zero."""

import subprocess
from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ArbitraryLawAdaptation.CDFCoupling
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval
open ThresholdHC.ArbitraryLawAdaptation

example : ∀ (f : StieltjesFunction ℝ) (u : I),
    boundedQuantile f u = sInf {x : ℝ | 0 ≤ x ∧ (u : ℝ) ≤ f x} := fun _ _ => rfl
example : ∀ (f : StieltjesFunction ℝ) {M : ℝ} (hM : 0 ≤ M) (hfM : f M = 1) (u : I),
    0 ≤ boundedQuantile f u ∧ boundedQuantile f u ≤ M ∧ (u : ℝ) ≤ f (boundedQuantile f u) :=
  @boundedQuantile_properties
example : ∀ (f : StieltjesFunction ℝ) {M : ℝ} (hM : 0 ≤ M) (hfM : f M = 1) (u : I) (x : ℝ),
    boundedQuantile f u ≤ x ↔ 0 ≤ x ∧ (u : ℝ) ≤ f x := @boundedQuantile_le_iff
example : ∀ (f : StieltjesFunction ℝ) {M : ℝ} (hM : 0 ≤ M) (hfM : f M = 1),
    Monotone (boundedQuantile f) := @boundedQuantile_monotone
example : ∀ (f : StieltjesFunction ℝ) {M : ℝ} (hM : 0 ≤ M) (hfM : f M = 1),
    Measurable (boundedQuantile f) := @measurable_boundedQuantile
example : ∀ (f g : StieltjesFunction ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hfM : f M = 1) (hgM : g M = 1) (hgf : ∀ x, g x ≤ f x) (u : I),
    boundedQuantile f u ≤ boundedQuantile g u := @boundedQuantile_antitone_cdf
example : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (hzero : μ (Iio 0) = 0)
    {M : ℝ} (hM : 0 ≤ M) (hμM : cdf μ M = 1),
    (volume : Measure I).map (boundedQuantile (cdf μ)) = μ := @boundedQuantile_map_volume
example : ∀ (μ ν : Measure ℝ), cdfCoupling μ ν =
    (volume : Measure I).map (fun u => (boundedQuantile (cdf μ) u, boundedQuantile (cdf ν) u)) :=
  fun _ _ => rfl
example : ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0) {M : ℝ} (hM : 0 ≤ M)
    (hμM : cdf μ M = 1) (hνM : cdf ν M = 1),
    (cdfCoupling μ ν).map Prod.fst = μ ∧ (cdfCoupling μ ν).map Prod.snd = ν :=
  @cdfCoupling_marginals
example : ∀ (μ ν : Measure ℝ) {M : ℝ} (hM : 0 ≤ M) (hμM : cdf μ M = 1)
    (hνM : cdf ν M = 1) (hdom : ∀ x, cdf ν x ≤ cdf μ x),
    ∀ᵐ z ∂cdfCoupling μ ν, z.1 ≤ z.2 := @cdfCoupling_increasing
example : ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0) {M : ℝ} (hM : 0 ≤ M)
    (hμM : cdf μ M = 1) (hνM : cdf ν M = 1) (hdom : ∀ x, cdf ν x ≤ cdf μ x),
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
      π.map Prod.snd = ν ∧ (∀ᵐ z ∂π, z.1 ≤ z.2) := @exists_increasing_coupling_of_cdf
"""
    roots = {"ThresholdHC.ArbitraryLawAdaptation." + name for name in [
        "boundedQuantile", "boundedQuantile_properties", "boundedQuantile_le_iff",
        "boundedQuantile_monotone", "measurable_boundedQuantile", "boundedQuantile_antitone_cdf",
        "boundedQuantile_map_volume", "cdfCoupling", "cdfCoupling_marginals",
        "cdfCoupling_increasing", "exists_increasing_coupling_of_cdf",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ArbitraryLawAdaptation.CDFCoupling"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
