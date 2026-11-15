"""Audit the convergence of the two dyadic series of the frozen targets H3 and H4.

`Targets.dyadic_sum_v1` and `Targets.dyadic_sum_v2` in the frozen
Statements.lean bound `∑'` sums, which Mathlib sets to zero for a series that
does not converge. This audit restates in full the module that proves both
series converge, with the frozen bounds as `HasSum` statements, and reports
the transitive axioms of every declaration. A declaration of the module that
the registry cannot read, or that is not registered here, is an error.
Prints the kernel report; writes nothing.
"""

import subprocess
from verify_blind_upper_components import (FORBIDDEN, LEAN, bind_restatements,
                                           registered_names, strip_comments,
                                           validate_reports)

MODULE = "ThresholdHC.Proofs.DyadicSummable"
SOURCE = LEAN / "ThresholdHC/Proofs/DyadicSummable.lean"
NAMES = ["dyadic_partial_v1", "dyadic_hasSum_v1", "dyadic_term_v2", "dyadic_partial_v2",
         "dyadic_hasSum_v2"]


def declared_names():
    """Every declaration of the module, after rejecting proof escapes."""
    source = strip_comments(SOURCE.read_text(encoding="utf-8"))
    if FORBIDDEN.search(source):
        raise ValueError("Forbidden proof escape in " + SOURCE.name)
    return registered_names(source)


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing dyadic-summability declaration")
    source = """
import ThresholdHC.Proofs.DyadicSummable
noncomputable section
set_option linter.unusedVariables false
open ThresholdHC.Proofs

example : ∀ {b : ℝ} (hb : 0 < b) (m : ℕ),
    ∑ k ∈ Finset.range m, (2:ℝ)^k * Real.exp (-(b*2^k)) ≤ 2 / b := @dyadic_partial_v1
example : ∀ {b : ℝ} (hb : 0 < b),
    ∃ s, HasSum (fun k : ℕ => (2:ℝ)^k * Real.exp (-(b*2^k))) s ∧ s ≤ 2 / b := @dyadic_hasSum_v1
example : ∀ {b : ℝ} (hb : 0 < b) (k : ℕ),
    ((2:ℝ)^k)^2 * Real.exp (-(b*2^k)) ≤ (2 / b) * ((2:ℝ)^k * Real.exp (-((b/2)*2^k))) :=
  @dyadic_term_v2
example : ∀ {b : ℝ} (hb : 0 < b) (m : ℕ),
    ∑ k ∈ Finset.range m, ((2:ℝ)^k)^2 * Real.exp (-(b*2^k)) ≤ 8 / b^2 := @dyadic_partial_v2
example : ∀ {b : ℝ} (hb : 0 < b),
    ∃ s, HasSum (fun k : ℕ => ((2:ℝ)^k)^2 * Real.exp (-(b*2^k))) s ∧ s ≤ 8 / (3 * b^2) :=
  @dyadic_hasSum_v2
-- The frozen targets the two sums bound, unchanged.
example : ThresholdHC.Targets.dyadic_sum_v1 ↔
    ∀ b : ℝ, 0 < b → ∑' k : ℕ, (2 : ℝ) ^ k * Real.exp (-(b * 2 ^ k)) ≤ 2 / b := Iff.rfl
example : ThresholdHC.Targets.dyadic_sum_v2 ↔
    ∀ b : ℝ, 0 < b → ∑' k : ℕ, ((2 : ℝ) ^ k) ^ 2 * Real.exp (-(b * 2 ^ k)) ≤ 8 / (3 * b ^ 2) :=
  Iff.rfl
"""
    body, _, frozen = source.partition("-- The frozen targets")
    bind_restatements(body, NAMES)
    roots = {"ThresholdHC.Proofs." + name for name in NAMES}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", MODULE], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
