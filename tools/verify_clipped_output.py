"""Audit the clipped-output statements of the upper-constant study.

The study research/2026-11-18-upper-constant states that clipping the output of
an estimator to [0, 1] can only help. The group checks that sentence in the
original adaptive experiment: the clipped estimator keeps the seed law, the
policy, the expected work and the uniform budget, its RMS risk is no larger
for any sign law, and its maximal RMS risk is at most min(1, original). Two
consequences beyond the source are also checked: the minimax risk over
[0, 1]-valued estimators equals minimaxRisk, and the blind family with
constant 12 can be taken [0, 1]-valued. The simulated clipped factors of the
study are not stated.

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

GROUP = "ClippedOutput"
NAMES = ("Specification", "Clip", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "fba139a4327da82d52652506675dc8ba0bcd74dd515e77b6403f5c8e45716632"
TARGETS = {
    "ClippedOutput.unit_clip_monotone": "ClippedOutput.UnitClipMonotoneStatement",
    "ClippedOutput.unit_output_minimax": "ClippedOutput.UnitOutputMinimaxStatement",
    "ClippedOutput.clipped_blind_upper_12": "ClippedOutput.ClippedBlindUpper12Statement",
}
COMPONENTS = (
    "ClippedOutput.unitClip_output_range",
    "ClippedOutput.unitClip_squaredRisk_le",
    "ClippedOutput.unitClip_maximalRMSRisk_le",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
    ∃ A' : AdaptiveEstimator R,
      A'.randomLaw = A.randomLaw ∧ A'.policy = A.policy ∧
      (∀ z, A'.output z = max 0 (min 1 (A.output z))) ∧
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        (∀ q : SignLaw, expectedWork μ A' q = expectedWork μ A q) ∧
        (∀ B : ℝ, UniformBudget μ A' B ↔ UniformBudget μ A B) ∧
        (∀ q : SignLaw,
          rootMeanRisk (experimentLaw μ A' q) (populationOutput A') (signMean μ q.val) ≤
          rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val)) ∧
        maximalRMSRisk μ A' ≤ min 1 (maximalRMSRisk μ A) :=
  ClippedOutput.unit_clip_monotone

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ),
    sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      UniformBudget μ A B ∧ (∀ z, 0 ≤ A.output z ∧ A.output z ≤ 1) ∧
      r = maximalRMSRisk μ A} = minimaxRisk μ B :=
  ClippedOutput.unit_output_minimax

example :
  ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    (∀ B z, 0 ≤ (rule B).output z ∧ (rule B).output z ≤ 1) ∧
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ min 1 (ENNReal.ofReal (12 * modulus μ (1 / Real.sqrt B))) :=
  ClippedOutput.clipped_blind_upper_12

example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (z : R × ProcessTape),
    0 ≤ (unitClip A).output z ∧ (unitClip A).output z ≤ 1 :=
  @ClippedOutput.unitClip_output_range

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw),
    squaredRisk (experimentLaw μ (unitClip A) q) (populationOutput (unitClip A))
        (signMean μ q.val) ≤
      squaredRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) :=
  @ClippedOutput.unitClip_squaredRisk_le

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R),
    maximalRMSRisk μ (unitClip A) ≤ min 1 (maximalRMSRisk μ A) :=
  @ClippedOutput.unitClip_maximalRMSRisk_le
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
        raise ValueError("Duplicate clipped-output declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing clipped-output target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed clipped-output specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ClippedOutput",
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
    print(f"All {len(TARGETS)} clipped-output targets are certified")


if __name__ == "__main__":
    main()
