"""Audit the square-root cap comparison of the optimized stopping programs.

For every gap law, rarity at most one half and cap N, the ordinary program is
within the factor k of the genie program once B is at most N (k - 1/k)^2. A
cap of 4B/9 therefore passes the factor-two test and gives the factor-sixteen
minimax certificate. The two target statements use only the existing program
definitions and are restated below with their types written out. Every public
declaration of the directory is an axiom-audit root; the one private lemma is
covered by the whole-project audit. The statements were written after the
proof, from the research checkpoint `research/2026-11-17-rms-constants`.
"""
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

PREFIX = "ThresholdHC.SquareRootCap."
SOURCES = LEAN / "ThresholdHC/SquareRootCap"
MODULES = ("Specification", "Full")
SPEC_HASH = "113661a4a80d33d3da28c77f702fbd5e3ee045a71a3a05a5cb37dd9eb91612bb"
TARGETS = {
    "square_root_cap": "SquareRootCapStatement",
    "four_ninths": "FourNinthsCapStatement",
}
COMPONENTS = ("square_root_cap_factor", "four_ninths_cap")
EXACT_COUNT = len(COMPONENTS)

EXACT = """
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B k : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B → 1 < k → ∀ N : ℕ, B ≤ N*(k-1/k)^2 →
    programValue μ ρ B N ≤ ENNReal.ofReal k * genieValue μ ρ B N :=
  @square_root_cap_factor

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B → ∀ N : ℕ, 4*B/9 ≤ N →
    programValue μ ρ B N ≤ 2*genieValue μ ρ B N ∧
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
    programValue μ ρ B N ≤ 16*rareMinimaxRisk μ ρ B :=
  @four_ninths_cap
"""


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES):
        raise ValueError("Unregistered or missing square-root cap module")
    roots: list[str] = []
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in SquareRootCap/{name}.lean")
        roots.extend(public_names(source, f"SquareRootCap/{name}.lean"))
    required = {name for pair in TARGETS.items() for name in pair} | set(COMPONENTS)
    missing = {PREFIX + name for name in required} - set(roots)
    if missing:
        raise ValueError("Missing square-root cap target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed square-root cap statement")
    roots = declared_roots()
    source = "\n".join([
        "import ThresholdHC.SquareRootCap.Full",
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie",
        "open ThresholdHC.RareAboveTwo ThresholdHC.SquareRootCap",
        *[f"example : {statement} := {theorem}" for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT or any(
            len(re.findall(rf":=\s*@?{re.escape(name)}\n", EXACT)) != 1 for name in COMPONENTS):
        raise ValueError("Each component needs exactly one restated statement")
    return source, roots


def main() -> None:
    source, roots = audit_input()
    subprocess.run(["lake", "build", PREFIX + "Full"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {EXACT_COUNT} exact statements and {len(roots)} transitive axiom reports")
    print("Both square-root cap target statements are certified")


if __name__ == "__main__":
    main()
