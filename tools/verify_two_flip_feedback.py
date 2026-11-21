"""Audit the strict acquisition-feedback advantage at a two-flip cap.

Theorem feedback:full-class of
research/2026-10-27-nonlinear-population/lower/full_class-body.tex says that
at the gap law (delta_(1/4) + delta_(1/8))/2, rarity 1/4 and a deterministic
total cap of two flips, a feedback policy (coin 0, then a fresh coin after a
tail and coin 0 again after a head) has worst mean squared error below
0.015443 over every globally rare sign law, while every noninteractive
cap-two design has worst mean squared error above 0.015475. The group
proves the upper bound for the pinned policy and output table, the lower
bound for every member of the seed-conditional normal form under a pathwise
cap of two (to which the paper's dominance step reduces preselected local
designs; that reduction is not formalized), that the class contains genuine
two-flip schedules and has minimax at most 1/64, and the separation by more
than 32/10^6.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the five targets and three components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker. The statements were written before the proofs
and reviewed before the pin; they are pinned from this audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "TwoFlipFeedback"
NAMES = ("Specification", "TwoStep", "TwoGapLaw", "Risk", "UpperPoly", "Upper", "LowerBayes", "Lower", "Members", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "33c62cec3ca7961b9193a44f4b91c643ecf61c21a7dbcf32dcd173b2ee39044d"
TARGETS = {
    "TwoFlipFeedback.feedback_upper_bound": "TwoFlipFeedback.FeedbackUpperStatement",
    "TwoFlipFeedback.noninteractive_class": "TwoFlipFeedback.NoninteractiveClassStatement",
    "TwoFlipFeedback.uniform_lower_bound": "TwoFlipFeedback.UniformLowerStatement",
    "TwoFlipFeedback.noninteractive_lower": "TwoFlipFeedback.NoninteractiveLowerStatement",
    "TwoFlipFeedback.feedback_separation": "TwoFlipFeedback.SeparationStatement",
}
COMPONENTS = (
    "TwoFlipFeedback.riskPoly_le",
    "TwoFlipFeedback.feedback_upper",
    "TwoFlipFeedback.minimax_lower",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∃ A : AdaptiveEstimator Unit,
    (∀ r, A.policy r = stopAt 2 feedbackLabel) ∧
    (∀ x : ProcessTape, A.output ((), x) = feedbackOutput (processPrefix 2 x)) ∧
    PathwiseCap A 2 ∧ ¬ NoninteractiveCapTwo A ∧
    rareSquaredRisk A < ENNReal.ofReal (15443/1000000) :=
  TwoFlipFeedback.feedback_upper_bound

example :
  (∃ A : AdaptiveEstimator Unit, (∀ r, A.policy r = stopAt 2 (fun _ => 0)) ∧
      PathwiseCap A 2 ∧ NoninteractiveCapTwo A) ∧
  (∃ A : AdaptiveEstimator Unit, (∀ r, A.policy r = stopAt 2 (fun xs => xs.length)) ∧
      PathwiseCap A 2 ∧ NoninteractiveCapTwo A) ∧
  noninteractiveMinimax ≤ ENNReal.ofReal (1/64) :=
  TwoFlipFeedback.noninteractive_class

example :
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    PathwiseCap A 2 → NoninteractiveCapTwo A →
    ENNReal.ofReal (1547585/100000000) ≤ rareSquaredRisk A :=
  TwoFlipFeedback.uniform_lower_bound

example :
  ENNReal.ofReal (15475/1000000) < noninteractiveMinimax ∧
  noninteractiveMinimax ≤ ENNReal.ofReal (1/64) :=
  TwoFlipFeedback.noninteractive_lower

example :
  ∃ A : AdaptiveEstimator Unit,
    (∀ r, A.policy r = stopAt 2 feedbackLabel) ∧
    (∀ x : ProcessTape, A.output ((), x) = feedbackOutput (processPrefix 2 x)) ∧
    PathwiseCap A 2 ∧ ¬ NoninteractiveCapTwo A ∧
    rareSquaredRisk A + ENNReal.ofReal (32/1000000) < noninteractiveMinimax :=
  TwoFlipFeedback.feedback_separation

example : ∀ (δ θ : ℝ), 0 ≤ δ → 2 * δ ≤ θ → θ ≤ 4 * δ → θ ≤ 1/4 →
    riskPoly δ θ ≤ upperValue :=
  TwoFlipFeedback.riskPoly_le

example : rareSquaredRisk feedbackEstimator ≤ ENNReal.ofReal upperValue :=
  TwoFlipFeedback.feedback_upper

example : ENNReal.ofReal lowerValue ≤ noninteractiveMinimax :=
  TwoFlipFeedback.minimax_lower
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
        raise ValueError("Duplicate two-flip-feedback declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing two-flip-feedback target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed two-flip-feedback specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget ThresholdHC.TwoFlipFeedback",
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
    print(f"All {len(TARGETS)} two-flip-feedback targets are certified")


if __name__ == "__main__":
    main()
