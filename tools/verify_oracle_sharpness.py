"""Audit the sharpness of the magnitude-oracle upper coefficient one half.

The second review of the rms-constants package states that for a budget
B >= 1 the oracle minimax risks of point masses at gaps decreasing to zero
have liminf at least one half, while the modulus at B^(-1/2) equals one, so
no oracle upper coefficient below one half holds. The group states this in
eventual form for both magnitude oracles, with an auxiliary single-gap lower
bound in the ordinary model. The upper bound R <= modulus/2 is not stated
here.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the two targets and two components with their types written out;
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

GROUP = "OracleSharpness"
NAMES = ("Specification", "SignTest", "SignPopulation", "Sharpness", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "ca7b9537847276d89cfa48191c8632f735013a10a452380b6d8fd2f98fa411cf"
TARGETS = {
    "OracleSharpness.oracle_upper_sharpness": "OracleSharpness.OracleUpperSharpnessStatement",
    "OracleSharpness.small_gap_sign_lower": "OracleSharpness.SmallGapSignLowerStatement",
}
COMPONENTS = (
    "OracleSharpness.oracle_point_lower",
    "OracleSharpness.prefix_sign_bound",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (B c : ℝ), 1 ≤ B → c < 1/2 → ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ g : Gap, g.val ≤ g₀ →
    ENNReal.ofReal (modulus (Measure.dirac g) (1 / Real.sqrt B) * c) <
      revealedMinimaxRisk (Measure.dirac g) B ∧
    ENNReal.ofReal (modulus (Measure.dirac g) (1 / Real.sqrt B) * c) <
      selectedMinimaxRisk (Measure.dirac g) B :=
  OracleSharpness.oracle_upper_sharpness

example :
  ∀ (g : Gap) (B c : ℝ), 0 ≤ B → 0 ≤ c → 2 * g.val < 1 →
    2 * g.val * Real.artanh (2 * g.val) * B ≤ 1 - 4 * c^2 →
    ENNReal.ofReal c ≤ minimaxRisk (Measure.dirac g) B :=
  OracleSharpness.small_gap_sign_lower

example : ∀ (g : Gap) (B c : ℝ), ENNReal.ofReal c ≤ minimaxRisk (Measure.dirac g) B →
    ENNReal.ofReal c ≤ revealedMinimaxRisk (Measure.dirac g) B ∧
    ENNReal.ofReal c ≤ selectedMinimaxRisk (Measure.dirac g) B :=
  @OracleSharpness.oracle_point_lower

example : ∀ {n : ℕ} (pol : List Bool → Option ℕ) (s : ℝ), 0 < s → s < 1 → ∀ (X : Prefix n → ℝ),
    (2:ℝ) ≤ SharpRMS.prefixExpect pol s 1 (fun w => (X w-1)^2) +
      SharpRMS.prefixExpect pol s (-1) (fun w => (X w+1)^2) +
      s*Real.artanh s*(SharpRMS.prefixExpect pol s 1 (@workOf n) +
        SharpRMS.prefixExpect pol s (-1) (@workOf n)) :=
  @OracleSharpness.prefix_sign_bound
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
        raise ValueError("Duplicate oracle-sharpness declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing oracle-sharpness target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed oracle-sharpness specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.OracleLower ThresholdHC.OracleSharpness",
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
    print(f"All {len(TARGETS)} oracle-sharpness targets are certified")


if __name__ == "__main__":
    main()
