"""Exact-type and transitive-axiom audit for the learned finite CDF envelope.

This establishes deterministic validity given finite grid bounds. It does not
assume or assert that the statistical pilot attains those bounds.
"""

import subprocess
from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ArbitraryLawAdaptation.CDFEnvelope
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set
open scoped ENNReal BigOperators
open ThresholdHC.ArbitraryLawAdaptation

example : ∀ u : ℕ → ℝ, prefixMinimum u 0 = u 0 := fun _ => rfl
example : ∀ (u : ℕ → ℝ) (n : ℕ),
    prefixMinimum u (n+1) = min (prefixMinimum u n) (u (n+1)) := fun _ _ => rfl
example : ∀ (u : ℕ → ℝ) (n : ℕ), prefixMinimum u n ≤ u n := prefixMinimum_le
example : ∀ u : ℕ → ℝ, Antitone (prefixMinimum u) := prefixMinimum_antitone
example : ∀ {u : ℕ → ℝ} (hu : ∀ j, 0 ≤ u j) (n : ℕ),
    0 ≤ prefixMinimum u n := @prefixMinimum_nonneg
example : ∀ {u v : ℕ → ℝ} (hv : Antitone v) (n : ℕ)
    (hu : ∀ j ≤ n, v j ≤ u j), v n ≤ prefixMinimum u n := @prefixMinimum_majorizes
example : gridPoint = fun j : ℕ => (1/2:ℝ)^(j+1) := rfl
example : ∀ j : ℕ, 0 < gridPoint j := gridPoint_pos
example : Antitone gridPoint := gridPoint_antitone
example : ∀ j : ℕ, gridPoint (j+1) < gridPoint j := gridPoint_succ_lt

example : ∀ (c : ℕ → ℝ) (n : ℕ), envelopeLaw c n =
    ENNReal.ofReal (c n) • Measure.dirac 0 +
      ∑ i : Fin n, ENNReal.ofReal (c i.val-c (i.val+1)) •
        Measure.dirac (gridPoint (i.val+1)) := fun _ _ => rfl
example : ∀ (c : ℕ → ℝ) (n : ℕ) (x : ℝ), envelopeCDF c n x =
    if 0 ≤ x then c n + ∑ i : Fin n,
      if gridPoint (i.val+1) ≤ x then c i.val-c (i.val+1) else 0 else 0 := fun _ _ _ => rfl
example : ∀ (c : ℕ → ℝ) (n : ℕ),
    c n + (∑ i : Fin n, (c i.val-c (i.val+1))) = c 0 := envelope_weights_sum
example : ∀ {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (hmono : Antitone c)
    (n : ℕ) (x : ℝ), 0 ≤ envelopeCDF c n x := @envelopeCDF_nonneg
example : ∀ {c : ℕ → ℝ} {n : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hgrid : x < gridPoint n), envelopeCDF c n x = c n := @envelopeCDF_below_grid
example : ∀ {c : ℕ → ℝ} {n : ℕ} {x : ℝ} (hx : gridPoint (n+1) ≤ x),
    envelopeCDF c (n+1) x = envelopeCDF c n x := @envelopeCDF_succ_above
example : ∀ {F : ℝ → ℝ} {c : ℕ → ℝ} {n : ℕ}
    (hF : Monotone F) (hneg : ∀ x < 0, F x ≤ 0) (htop : ∀ x, F x ≤ c 0)
    (hgrid : ∀ j ≤ n, F (gridPoint j) ≤ c j) (x : ℝ),
    F x ≤ envelopeCDF c n x := @envelopeCDF_dominates
example : ∀ {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (hmono : Antitone c) (n : ℕ) (x : ℝ),
    envelopeLaw c n (Iic x) = ENNReal.ofReal (envelopeCDF c n x) := @envelopeLaw_Iic
example : ∀ {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (hmono : Antitone c) (n : ℕ),
    envelopeLaw c n univ = ENNReal.ofReal (c 0) := @envelopeLaw_mass
example : ∀ {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (hmono : Antitone c)
    (hzero : c 0 = 1) (n : ℕ), IsProbabilityMeasure (envelopeLaw c n) := @envelopeLaw_probability
example : ∀ (c : ℕ → ℝ) (n : ℕ), envelopeLaw c n {0} = ENNReal.ofReal (c n) := envelopeLaw_zero
example : ∀ (c : ℕ → ℝ) {n j : ℕ} (hj : j < n),
    envelopeCDF c n (gridPoint (j+1)) = c j := @envelopeCDF_at_grid
example : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] {c : ℕ → ℝ}
    (hc : ∀ j, 0 ≤ c j) (hmono : Antitone c) (hzero : c 0 = 1)
    (hsupport : μ (Iio 0) = 0) (n : ℕ)
    (hgrid : ∀ j ≤ n, μ.real (Iic (gridPoint j)) ≤ c j) (x : ℝ),
    μ (Iic x) ≤ envelopeLaw c n (Iic x) := @envelopeLaw_dominates
example : ∀ {u : ℕ → ℝ} (hu : ∀ j, 0 ≤ u j) (hu0 : u 0 = 1) (n : ℕ),
    IsProbabilityMeasure (envelopeLaw (prefixMinimum u) n) := @learnedEnvelope_probability
example : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℕ → ℝ}
    (hu : ∀ j, 0 ≤ u j) (hu0 : u 0 = 1) (hsupport : μ (Iio 0) = 0) (n : ℕ)
    (hgrid : ∀ j ≤ n, μ.real (Iic (gridPoint j)) ≤ u j) (x : ℝ),
    μ (Iic x) ≤ envelopeLaw (prefixMinimum u) n (Iic x) := @learnedEnvelope_dominates
"""
    roots = {"ThresholdHC.ArbitraryLawAdaptation." + name for name in [
        "prefixMinimum", "prefixMinimum_le", "prefixMinimum_antitone",
        "prefixMinimum_nonneg", "prefixMinimum_majorizes", "gridPoint",
        "gridPoint_pos", "gridPoint_antitone", "gridPoint_succ_lt",
        "envelopeLaw", "envelopeCDF", "envelope_weights_sum", "envelopeCDF_nonneg",
        "envelopeCDF_below_grid", "envelopeCDF_succ_above", "envelopeCDF_dominates",
        "envelopeLaw_Iic", "envelopeLaw_mass", "envelopeLaw_probability", "envelopeLaw_zero",
        "envelopeCDF_at_grid", "envelopeLaw_dominates", "learnedEnvelope_probability",
        "learnedEnvelope_dominates",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ArbitraryLawAdaptation.CDFEnvelope"],
                   cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
