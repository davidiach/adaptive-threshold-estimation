"""Check the arbitrary-law Psi lower bound derived from the entropy-tail law.

The audit restates the three target types in full, so a change to a definition
name or a hypothesis is an elaboration error, and reports the transitive axioms
of every declaration in lean/ThresholdHC/PsiSelection/. The specification is
pinned by hash. Prints the kernel report; writes nothing.
"""

import subprocess

from verify_blind_upper_components import (DECLARATION, FORBIDDEN, LEAN, sha, strip_comments,
                                           validate_reports)


PREFIX = "ThresholdHC.PsiSelection."
SOURCES = LEAN / "ThresholdHC/PsiSelection"
MODULES = ("Specification", "Comparison", "Full")
SPEC_HASH = "b18fe14fc8be24db36e132013e85c91197da6b368d511bb2dd014752c60faca9"
TARGETS = {
    "psi_le_selection": "PsiSelectionStatement",
    "psi_risk_lower": "PsiRiskLowerStatement",
    "psi_confidence_lower": "PsiConfidenceLowerStatement",
}
EXACT = """
example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hB : 0 < B) :
    rarePsi μ ρ (1 / Real.sqrt B) ≤ ThresholdHC.EntropyTail.selection μ ρ B :=
  psi_le_selection μ ρ B hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) * rarePsi μ ρ (1 / Real.sqrt B) ≤
      rareMinimaxRisk μ ρ B :=
  psi_risk_lower μ ρ B hρ hρ4 hB

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B δ : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) :
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) *
        rarePsi μ ρ (Real.sqrt (Real.log (1/δ) / B)) ≤
      ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ :=
  psi_confidence_lower μ ρ B δ hρ hρ4 hB hδ hδ4
"""


def declared_roots() -> set[str]:
    """Every declaration in the directory is an audit root; none is hand-listed."""
    found = {path.stem for path in SOURCES.glob("*.lean")}
    if found != set(MODULES):
        raise ValueError("Unregistered or missing Psi-selection module")
    roots = set()
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in PsiSelection/{name}.lean")
        roots |= {PREFIX + declaration for declaration in DECLARATION.findall(source)}
    missing = {PREFIX + name for pair in TARGETS.items() for name in pair} - roots
    if missing:
        raise ValueError("Missing Psi-selection target: " + ", ".join(sorted(missing)))
    return roots


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed Psi-selection statement")
    roots = declared_roots()
    source = "\n".join([
        "import ThresholdHC.PsiSelection.Full",
        "open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiSelection",
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
