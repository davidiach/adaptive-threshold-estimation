"""Audit the common-pair RMS bound at the quadratic critical law.

Lean proves a common pair for the critical law, with b = rho/32 and
J = a rho L (1 + log L) for some a > 0, and a generic transfer from a common
pair to R >= min{b, sqrt(J/B)}/128, but no theorem composed the two. The
targets state the composition for each algorithm with rare budget B and for
the minimax risk. The constant a is existential, as in the common-pair
theorem; the critical RMS law with explicit constants is checked separately.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the two targets with their types written out;
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

GROUP = "CriticalPairRMS"
NAMES = ("Specification", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "35f189aa0a35493094138d7d2b9d2bda12f0cba268bee882a02b4b07b55136df"
TARGETS = {
    "CriticalPairRMS.critical_pair_rms": "CriticalPairRMS.CriticalPairRMSStatement",
    "CriticalPairRMS.critical_pair_minimax_rms": "CriticalPairRMS.CriticalPairMinimaxRMSStatement",
}
COMPONENTS: tuple[str, ...] = ()
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∃ a : ℝ, 0 < a ∧ ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
      RareBudget ConfidenceTransfer.criticalPositiveLaw A ρ B →
      ENNReal.ofReal (min (ρ/32)
          (Real.sqrt (a*(ρ*CriticalEntropy.criticalLogFactor ρ)/B))/128) ≤
        rareRisk ConfidenceTransfer.criticalPositiveLaw A ρ :=
  CriticalPairRMS.critical_pair_rms

example : ∃ a : ℝ, 0 < a ∧ ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ENNReal.ofReal (min (ρ/32)
        (Real.sqrt (a*(ρ*CriticalEntropy.criticalLogFactor ρ)/B))/128) ≤
      rareMinimaxRisk ConfidenceTransfer.criticalPositiveLaw ρ B :=
  CriticalPairRMS.critical_pair_minimax_rms
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
        raise ValueError("Duplicate critical common-pair RMS declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing critical common-pair RMS target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed critical common-pair RMS specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
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
    print(f"All {len(TARGETS)} critical common-pair RMS targets are certified")


if __name__ == "__main__":
    main()
