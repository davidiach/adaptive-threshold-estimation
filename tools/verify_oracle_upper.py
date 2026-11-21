"""Audit the magnitude-oracle upper bound with coefficient one half.

The second review of the rms-constants package states that for every gap law
and every budget B >= 1 both magnitude-oracle minimax RMS risks are at most
one half of the modulus at B^(-1/2), by an estimator that buys one flip from
each of about n = floor(B) fresh coins with gap at least 1/(2 sqrt n),
selected with probability proportional to the inverse gap; the floor form at
the smaller scale 1/(2 sqrt n) is the intermediate bound. With the audited
sharpness group ThresholdHC.OracleSharpness, one half is exactly the best
universal coefficient for either oracle.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the three targets and three components with their types written out;
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

GROUP = "OracleUpper"
NAMES = ("Specification", "FreshProduct", "FreshOracle", "SeedMoments", "Thinning", "Upper", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "e0a1e4504dfa12b417f51609acac4436cc378dadb233d348568531f1323aeb8c"
TARGETS = {
    "OracleUpper.oracle_upper": "OracleUpper.OracleUpperStatement",
    "OracleUpper.oracle_floor_upper": "OracleUpper.OracleFloorUpperStatement",
    "OracleUpper.oracle_upper_coefficient": "OracleUpper.OracleUpperCoefficientStatement",
}
COMPONENTS = (
    "OracleUpper.modulus_split",
    "OracleUpper.bias_abs_le",
    "OracleUpper.floorScale_le",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    revealedMinimaxRisk μ B ≤ ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 2) ∧
    selectedMinimaxRisk μ B ≤ ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 2) :=
  OracleUpper.oracle_upper

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    revealedMinimaxRisk μ B ≤
      ENNReal.ofReal (modulus μ (1 / (2 * Real.sqrt (Nat.floor B : ℝ))) / 2) ∧
    selectedMinimaxRisk μ B ≤
      ENNReal.ofReal (modulus μ (1 / (2 * Real.sqrt (Nat.floor B : ℝ))) / 2) :=
  OracleUpper.oracle_floor_upper

example :
  ∀ c : ℝ,
    ((∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
        revealedMinimaxRisk μ B ≤ ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c)) ↔
      1/2 ≤ c) ∧
    ((∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
        selectedMinimaxRisk μ B ≤ ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c)) ↔
      1/2 ≤ c) :=
  OracleUpper.oracle_upper_coefficient

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {t : ℝ}, 0 < t →
    modulus μ t = t * upperInvMass μ t + ∫ d, lowPart t d ∂μ :=
  @OracleUpper.modulus_split

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (t : ℝ),
    |∫ d, (if t ≤ (d : ℝ) then 0 else 1/2 - q.val d) ∂μ| ≤ (1/2) * ∫ d, lowPart t d ∂μ :=
  @OracleUpper.bias_abs_le

example : ∀ (B : ℝ), 1 ≤ B → floorScale (Nat.floor B) ≤ 1 / Real.sqrt B :=
  @OracleUpper.floorScale_le
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
        raise ValueError("Duplicate oracle-upper declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing oracle-upper target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed oracle-upper specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.OracleLower ThresholdHC.OracleUpper",
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
    print(f"All {len(TARGETS)} oracle-upper targets are certified")


if __name__ == "__main__":
    main()
