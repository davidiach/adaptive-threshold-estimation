"""Check two-atom Psi sharpness and the occupied-band entropy bound.

The specification was committed before the proofs. The two target statements
are independently expanded below; every declaration in the new directory is
an axiom-audit root. Existing Psi specifications and published records are
unchanged. This audit does not cover the uniform power-law results.
"""
import subprocess

from verify_blind_upper_components import (
    FORBIDDEN, LEAN, registered_names, sha, strip_comments, validate_reports,
)

PREFIX = "ThresholdHC.PsiSharpness."
SOURCES = LEAN / "ThresholdHC/PsiSharpness"
MODULES = ("Specification", "TwoAtom", "OccupiedBands", "Full")
SPEC_HASH = "5f32b4e683c1f6abfec405e694b1e92d741fb995729099e2ba99c38049ac0123"
TARGETS = {
    "two_atom_sharpness": "TwoAtomSharpnessStatement",
    "occupied_band_entropy": "OccupiedBandEntropyStatement",
}

EXACT = """
example (ρ B : ℝ) (d₁ d₂ : Gap) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hd : (d₂ : ℝ) = (d₁ : ℝ) * Real.sqrt ((1 - ρ) / ρ))
    (hh : 1 / Real.sqrt B ≤ (d₁ : ℝ) / 2) :
    let μ := ENNReal.ofReal ρ • Measure.dirac d₁ +
      ENNReal.ofReal (1 - ρ) • Measure.dirac d₂
    rarePsi μ ρ (1 / Real.sqrt B) =
      ENNReal.ofReal (Real.sqrt 2 * (1 / Real.sqrt B) * ρ / (d₁ : ℝ)) ∧
    (min (ENNReal.ofReal ρ)
      (ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
        ENNReal.ofReal (1 / Real.sqrt B) *
          (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
            ∂quantileCore μ ρ) ^ (1/2 : ℝ))) =
      ENNReal.ofReal (2 * (1 / Real.sqrt B) * ρ / (d₁ : ℝ)) ∧
    (min (ENNReal.ofReal ρ)
      (ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
        ENNReal.ofReal (1 / Real.sqrt B) *
          (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
            ∂quantileCore μ ρ) ^ (1/2 : ℝ))) =
      ENNReal.ofReal (Real.sqrt 2) * rarePsi μ ρ (1 / Real.sqrt B) :=
  two_atom_sharpness ρ B d₁ d₂ hρ hρ4 hB hd hh

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    (Function.support (bandCost (quantileCore μ ρ))).Finite ∧
    0 < (Function.support (bandCost (quantileCore μ ρ))).ncard ∧
    (∑' j : ℕ, Real.negMulLog
      (bandCost (quantileCore μ ρ) j /
        (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal)) ≤
      Real.log (Function.support (bandCost (quantileCore μ ρ))).ncard ∧
    Real.log (Function.support (bandCost (quantileCore μ ρ))).ncard ≤
      Real.log (Real.logb 2 (1 / quantileThreshold μ ρ)) :=
  occupied_band_entropy μ ρ hρ hρ4

example :
    let d₁ : Gap := ⟨1/8, by norm_num, by norm_num⟩
    let d₂ : Gap := ⟨1/4, by norm_num, by norm_num⟩
    let μ := ENNReal.ofReal (1/5) • Measure.dirac d₁ +
      ENNReal.ofReal (4/5) • Measure.dirac d₂
    rarePsi μ (1/5) (1/32) = ENNReal.ofReal (Real.sqrt 2 / 20) ∧
    ThresholdHC.PsiClosedForm.quantileZero μ (1/5) 1024 = ENNReal.ofReal (1/10) := by
  convert sharp_example using 1 <;> norm_num [twoAtomLaw]
"""


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES):
        raise ValueError("Unregistered or missing Psi sharpness module")
    roots = set()
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in PsiSharpness/{name}.lean")
        roots.update(PREFIX + declaration for declaration in registered_names(source))
    missing = {PREFIX + name for pair in TARGETS.items() for name in pair} - roots
    if missing:
        raise ValueError("Missing Psi sharpness target: " + ", ".join(sorted(missing)))
    return roots


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed Psi sharpness statement")
    roots = declared_roots()
    source = "\n".join([
        "import ThresholdHC.PsiSharpness.Full",
        "open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiSharpness",
        "open ThresholdHC.EntropyTailQuantile",
        "open scoped ENNReal",
        *[f"example : {statement} := {theorem}" for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    return source, roots


def main() -> None:
    source, roots = audit_input()
    subprocess.run(["lake", "build", PREFIX + "Full"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(TARGETS) + 3} exact statements and {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
