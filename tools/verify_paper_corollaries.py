"""Audit corollaries that the guides state as paper arguments on Lean results.

* Under a stochastic envelope, the minimax RMS risk over every gap law below a
  reference law is between one sixth and twelve times the reference modulus:
  the reference law belongs to the class, and the distribution-blind family of
  the constant 12 works under every law below it.
* Under a pathwise cap of floor(B) observations, the minimax RMS risk is at
  least one sixth of the modulus, since such algorithms meet the expected
  budget.
* At the quadratic law, along rho_n = exp(-exp n) and B_n = rho_n^-2, the ratio
  of the minimax risk to Psi is at least 7*10^-20 sqrt(1 + log(1 + log(1/rho_n)))
  for n >= 3, and that factor is at least sqrt(1 + n).

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification, whose three statements use only the envelope and
   hard-cap minimax risks, the rare-event risk, Psi and the modulus;
3. restates the three targets and two component theorems with their types
   written out, so a changed statement cannot pass under an old name;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker. The statements were written after the proofs;
they are pinned from this audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "PaperCorollaries"
NAMES = ("Specification", "Transfer", "PsiSequence", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "6488025a6f4b876a3e3dc378cbed39bef6d80a7f3f8e860c2e908c8afd3ca152"
TARGETS = {
    "PaperCorollaries.envelope_rms": "PaperCorollaries.EnvelopeRMSStatement",
    "PaperCorollaries.hard_sharp_lower": "PaperCorollaries.HardSharpLowerStatement",
    "PaperCorollaries.psi_sequence": "PaperCorollaries.PsiSequenceStatement",
}
COMPONENTS = ("PaperCorollaries.sixteen_le_exp", "PaperCorollaries.exp_three_ge")
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) ≤ Envelope.minimaxRMS μ B ∧
    Envelope.minimaxRMS μ B ≤ ENNReal.ofReal (12 * modulus μ (1 / Real.sqrt B)) :=
  PaperCorollaries.envelope_rms

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) ≤ HardBudget.hardMinimaxRisk μ B :=
  PaperCorollaries.hard_sharp_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ExactPowerLaw μ 2 (1/4) →
    ∀ n : ℕ, 3 ≤ n →
    let ρ := Real.exp (-Real.exp n)
    let B := 1 / ρ ^ 2
    ENNReal.ofReal (7 * (10 : ℝ)⁻¹ ^ 20 * Real.sqrt (1 + Real.log (1 + Real.log (1/ρ)))) *
        rarePsi μ ρ (1 / Real.sqrt B) ≤ rareMinimaxRisk μ ρ B ∧
    Real.sqrt (1 + n) ≤ Real.sqrt (1 + Real.log (1 + Real.log (1/ρ))) :=
  PaperCorollaries.psi_sequence

example : ∀ {ℓ : ℝ}, 20 ≤ ℓ → 16 * ℓ * (1 + ℓ) ≤ Real.exp ℓ :=
  @PaperCorollaries.sixteen_le_exp

example : (20 : ℝ) ≤ Real.exp 3 :=
  PaperCorollaries.exp_three_ge
"""


def modules() -> list[str]:
    return [f"{GROUP}.{name}" for name in NAMES]


def declared_roots() -> set[str]:
    found = {p.stem for p in SOURCE.glob("*.lean")}
    if found != set(NAMES) or len(NAMES) != len(set(NAMES)):
        raise ValueError(f"Unregistered or missing {GROUP} module")
    roots: list[str] = []
    for name in NAMES:
        source = strip_comments((SOURCE / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in {GROUP}/{name}.lean")
        names_here = public_names(source, f"{GROUP}/{name}.lean")
        if any(not root.startswith(f"ThresholdHC.{GROUP}.") for root in names_here):
            raise ValueError(f"{GROUP}/{name}.lean must declare in ThresholdHC.{GROUP}")
        roots.extend(names_here)
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate paper-corollary declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing paper-corollary target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed paper-corollary statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.RareAboveTwo",
        *[f"example : {statement} := {theorem}" for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?{re.escape(name)}\n", EXACT)) != 1:
            raise ValueError("Each target and component needs exactly one restated statement")
    return source, roots


def replay_modules() -> list[str]:
    return ["ThresholdHC." + module for module in modules()]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--replay", action="store_true",
                        help="also replay the registered modules through leanchecker")
    parser.add_argument("--jobs", type=int, default=3, help="parallel kernel replays")
    args = parser.parse_args()
    source, roots = audit_input()
    subprocess.run(["lake", "build", *replay_modules()], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {EXACT_COUNT} exact statements and {len(roots)} transitive axiom reports")
    if args.replay:
        from verify_project_axioms import replay
        replay(replay_modules(), "lake", args.jobs)
        print(f"Replayed {len(modules())} modules through the independent kernel checker")
    print("All three paper-corollary target statements are certified")


if __name__ == "__main__":
    main()
