"""Check the closed form of the variational modulus Psi (v6 Proposition 14.9).

The audit restates the three target types in full, so a change to a definition
name or a hypothesis is an elaboration error, and reports the transitive axioms
of every declaration in lean/ThresholdHC/PsiClosedForm/. The specification is
pinned by hash. Prints the kernel report; writes nothing.

Scope: the comparisons after display (W1), the chain (W2) and the regime in
which the resolution is at least the quantile threshold. The two-atom
sharpness example, Theorem 14.11, Lemma 14.12 and Theorem 14.13 are not
checked here.
"""

import subprocess

from verify_blind_upper_components import (DECLARATION, FORBIDDEN, LEAN, sha, strip_comments,
                                           validate_reports)


PREFIX = "ThresholdHC.PsiClosedForm."
SOURCES = LEAN / "ThresholdHC/PsiClosedForm"
MODULES = ("Specification", "Order", "Lower", "Full")
SPEC_HASH = "@SPEC_HASH@"
TARGETS = {
    "entropy_free_order": "EntropyFreeOrderStatement",
    "psi_closed_form": "PsiClosedFormStatement",
    "psi_trivial_regime": "PsiTrivialRegimeStatement",
}
# The definitions of the specification are written out, so the restatements do
# not use the names `inverseSquareCost`, `selectionZero` or `quantileZero`.
EXACT = """
example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    min (ENNReal.ofReal ρ) (⨅ (σ : Measure Gap) (_ : σ ≤ μ),
        ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂σ) ^ (1/2 : ℝ)
          + ThresholdHC.EntropyTail.tailCost (μ - σ) (1 / Real.sqrt B)) ≤
      ThresholdHC.EntropyTail.selection μ ρ B ∧
    min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost
            (ThresholdHC.EntropyTailQuantile.quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) ^ (1/2 : ℝ)) ≤
      ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ∧
    min (ENNReal.ofReal ρ) (⨅ (σ : Measure Gap) (_ : σ ≤ μ),
        ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂σ) ^ (1/2 : ℝ)
          + ThresholdHC.EntropyTail.tailCost (μ - σ) (1 / Real.sqrt B)) ≤
      min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost
            (ThresholdHC.EntropyTailQuantile.quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) ^ (1/2 : ℝ)) :=
  entropy_free_order μ ρ B hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost
            (ThresholdHC.EntropyTailQuantile.quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) ^ (1/2 : ℝ)) ≤
      ENNReal.ofReal (Real.sqrt 2) * rarePsi μ ρ (1 / Real.sqrt B) ∧
    rarePsi μ ρ (1 / Real.sqrt B) ≤
      min (ENNReal.ofReal ρ) (⨅ (σ : Measure Gap) (_ : σ ≤ μ),
        ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂σ) ^ (1/2 : ℝ)
          + ThresholdHC.EntropyTail.tailCost (μ - σ) (1 / Real.sqrt B)) ∧
    min (ENNReal.ofReal ρ) (⨅ (σ : Measure Gap) (_ : σ ≤ μ),
        ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂σ) ^ (1/2 : ℝ)
          + ThresholdHC.EntropyTail.tailCost (μ - σ) (1 / Real.sqrt B)) ≤
      min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost
            (ThresholdHC.EntropyTailQuantile.quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) ^ (1/2 : ℝ)) :=
  psi_closed_form μ ρ B hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (ht : ThresholdHC.EntropyTailQuantile.quantileThreshold μ ρ ≤ 1 / Real.sqrt B) :
    rarePsi μ ρ (1 / Real.sqrt B) = ENNReal.ofReal ρ ∧
    min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost
            (ThresholdHC.EntropyTailQuantile.quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) ^ (1/2 : ℝ)) =
      ENNReal.ofReal ρ :=
  psi_trivial_regime μ ρ B hρ hρ4 hB ht
"""


def declared_roots() -> set[str]:
    """Every declaration in the directory is an audit root; none is hand-listed."""
    found = {path.stem for path in SOURCES.glob("*.lean")}
    if found != set(MODULES):
        raise ValueError("Unregistered or missing Psi closed-form module")
    roots = set()
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in PsiClosedForm/{name}.lean")
        roots |= {PREFIX + declaration for declaration in DECLARATION.findall(source)}
    missing = {PREFIX + name for pair in TARGETS.items() for name in pair} - roots
    if missing:
        raise ValueError("Missing Psi closed-form target: " + ", ".join(sorted(missing)))
    return roots


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed Psi closed-form statement")
    roots = declared_roots()
    source = "\n".join([
        "import ThresholdHC.PsiClosedForm.Full",
        "open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiClosedForm",
        "open scoped ENNReal",
        *[f"example : {statement} := {theorem}" for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    return source, roots


def main() -> None:
    source, roots = audit_input()
    subprocess.run(["lake", "build", PREFIX + "Full"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(TARGETS) + 3} exact statements and {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
