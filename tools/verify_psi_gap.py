"""Check the distance of the variational modulus Psi from the rate (v6 Theorem 14.11).

The audit restates the four target types in full, so a change to a definition
name or a hypothesis is an elaboration error, and reports the transitive axioms
of every declaration in lean/ThresholdHC/PsiGap/. The specification is pinned
by hash. Prints the kernel report; writes nothing.

Scope: the decomposition of the core's cost entropy with the bound on its
entropy, the chain (W4), the two-sided risk bound and the reverse bound under
its two conditions. The intermediate bound by the number of occupied bands,
Lemma 14.12 and Theorem 14.13 are not checked here.
"""

import subprocess

from verify_blind_upper_components import (DECLARATION, FORBIDDEN, LEAN, sha, strip_comments,
                                           validate_reports)


PREFIX = "ThresholdHC.PsiGap."
SOURCES = LEAN / "ThresholdHC/PsiGap"
MODULES = ("Specification", "Entropy", "Full")
SPEC_HASH = "388626ff8735a44986ff008aeb616c0943c7e79f15e61384c178589c92c403d3"
TARGETS = {
    "core_entropy": "CoreEntropyStatement",
    "psi_gap": "PsiGapStatement",
    "psi_gap_risk": "PsiGapRiskStatement",
    "psi_gap_reverse": "PsiGapReverseStatement",
}
# `A` and `E` are written out, so the restatements do not use the names
# `coreCost` and `coreEntropy`. `Q0` is written out as well.
A = "(∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal"
E = ("(∑' j : ℕ, Real.negMulLog (ThresholdHC.EntropyTailQuantile.bandCost (quantileCore μ ρ) j / "
     + A + "))")
Q0 = """(min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
              ∂quantileCore μ ρ) ^ (1/2 : ℝ)))"""
EXACT = """
example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    0 < @A@ ∧
    (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ) = ENNReal.ofReal @A@ ∧
    0 ≤ @E@ ∧
    measureCostEntropy (quantileCore μ ρ) = ENNReal.ofReal (@A@ * (1 + @E@)) ∧
    @E@ ≤ Real.log (Real.logb 2 (1 / quantileThreshold μ ρ)) :=
  core_entropy μ ρ hρ hρ4

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    rarePsi μ ρ (1 / Real.sqrt B) ≤ ThresholdHC.EntropyTail.selection μ ρ B ∧
    ThresholdHC.EntropyTail.selection μ ρ B ≤ closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (Real.sqrt (1 + @E@)) * @Q0@ ∧
    closedQuantileValue μ ρ B ≤
      ENNReal.ofReal (Real.sqrt (2 * (1 + @E@))) * rarePsi μ ρ (1 / Real.sqrt B) :=
  psi_gap μ ρ B hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) * rarePsi μ ρ (1 / Real.sqrt B) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤
      ENNReal.ofReal (30001 * Real.sqrt (2 * (1 + @E@))) * rarePsi μ ρ (1 / Real.sqrt B) :=
  psi_gap_risk μ ρ B hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (htail : ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) ≤
      ENNReal.ofReal (1 / Real.sqrt B) *
        (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ) ^ (1/2 : ℝ))
    (hcap : ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
      ENNReal.ofReal (1 / Real.sqrt B) *
        (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) ^ (1/2 : ℝ) ≤
      ENNReal.ofReal ρ) :
    ENNReal.ofReal (Real.sqrt (1 + @E@) / 2) * @Q0@ ≤ closedQuantileValue μ ρ B ∧
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17 * (Real.sqrt (1 + @E@) / 2)) *
        rarePsi μ ρ (1 / Real.sqrt B) ≤ rareMinimaxRisk μ ρ B :=
  psi_gap_reverse μ ρ B hρ hρ4 hB htail hcap
""".replace("@A@", A).replace("@E@", E).replace("@Q0@", Q0)


def declared_roots() -> set[str]:
    """Every declaration in the directory is an audit root; none is hand-listed."""
    found = {path.stem for path in SOURCES.glob("*.lean")}
    if found != set(MODULES):
        raise ValueError("Unregistered or missing Psi gap module")
    roots = set()
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in PsiGap/{name}.lean")
        roots |= {PREFIX + declaration for declaration in DECLARATION.findall(source)}
    missing = {PREFIX + name for pair in TARGETS.items() for name in pair} - roots
    if missing:
        raise ValueError("Missing Psi gap target: " + ", ".join(sorted(missing)))
    return roots


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed Psi gap statement")
    roots = declared_roots()
    source = "\n".join([
        "import ThresholdHC.PsiGap.Full",
        "open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiGap",
        "open ThresholdHC.EntropyTailQuantile (quantileTail quantileCore quantileThreshold",
        "  closedQuantileValue measureCostEntropy)",
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
    print(f"Verified {2 * len(TARGETS)} exact statements and {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
