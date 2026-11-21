"""Audit strictness of the sharp universal RMS lower bound away from B = 4.

The remark after Theorem sharp-rms (v6 Appendix AA) says that equality
R_mu(B) = omega_mu(B^-1/2)/6 requires B = 4: every case of the proof is strict
for B != 4. The targets: for every gap law and every B >= 1 with B != 4 the
minimax RMS risk is strictly above omega/6, with one coefficient above 1/6
for all laws at each such B; equality forces B = 4; the explicit small-budget
bound sqrt((10 - B)/216) for 0 <= B <= 4; strictness at every critical point
mass; and the strict bound under both magnitude oracles.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the six targets and three components with their types written out;
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

GROUP = "SharpStrict"
NAMES = ("Specification", "Strict", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "534242942216d075474e79c9db272dd453affe24834efae35e05171e1398cf52"
TARGETS = {
    "SharpStrict.strict_sharp_lower": "SharpStrict.StrictSharpLowerStatement",
    "SharpStrict.strict_coefficient": "SharpStrict.StrictCoefficientStatement",
    "SharpStrict.sharp_equality_case": "SharpStrict.SharpEqualityCaseStatement",
    "SharpStrict.small_budget_lower": "SharpStrict.SmallBudgetLowerStatement",
    "SharpStrict.critical_strict": "SharpStrict.CriticalStrictStatement",
    "SharpStrict.oracle_strict_sharp_lower": "SharpStrict.OracleStrictSharpLowerStatement",
}
COMPONENTS = (
    "SharpStrict.small_budget_minimax_lower",
    "SharpStrict.tapered_coefficient_gt",
    "SharpStrict.near_perfect_integral_strict",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≠ 4 →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) < minimaxRisk μ B :=
  SharpStrict.strict_sharp_lower

example :
  ∀ B : ℝ, 1 ≤ B → B ≠ 4 → ∃ c : ℝ, 1/6 < c ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ minimaxRisk μ B :=
  SharpStrict.strict_coefficient

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B = ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) → B = 4 :=
  SharpStrict.sharp_equality_case

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 0 ≤ B → B ≤ 4 →
    ENNReal.ofReal (Real.sqrt ((10 - B) / 216)) ≤ minimaxRisk μ B :=
  SharpStrict.small_budget_lower

example :
  ∀ (g : Gap) (B : ℝ), 2 * g.val < 1 → (2 * g.val) ^ 2 * B = 4 →
    ENNReal.ofReal (1/6 : ℝ) < minimaxRisk (Measure.dirac g) B :=
  SharpStrict.critical_strict

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≠ 4 →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) < revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) < selectedMinimaxRisk μ B :=
  SharpStrict.oracle_strict_sharp_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 0 ≤ B → B ≤ 10 →
    ENNReal.ofReal (Real.sqrt ((10-B)/216)) ≤ minimaxRisk μ B :=
  @SharpStrict.small_budget_minimax_lower

example : ∀ (a : ℝ), a < 4/3 → (1/6:ℝ) < Real.sqrt ((20/3-2*a)/144) :=
  @SharpStrict.tapered_coefficient_gt

example : ∀ (s : ℝ), 39/40 ≤ s → s < 1 →
    IntervalIntegrable (nearPerfectEnvelope s) MeasureTheory.volume 0 1 ∧
    (∫ t in (0:ℝ)..1, nearPerfectEnvelope s t) < 2/3 :=
  @SharpStrict.near_perfect_integral_strict
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
        raise ValueError("Duplicate sharp-strictness declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing sharp-strictness target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed sharp-strictness specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.OracleLower ThresholdHC.SharpRMS ThresholdHC.SharpRMS.Window",
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
    print(f"All {len(TARGETS)} sharp-strictness targets are certified")


if __name__ == "__main__":
    main()
