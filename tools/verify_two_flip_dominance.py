"""Audit the dominance step of the two-flip acquisition-feedback advantage.

At the two-point gap law with a total cap of two flips, the nonlinear-population
package compares the feedback policy with the class of preselected,
independently executed local designs and reduces that class to two schedules
by a dominance argument. The two-flip feedback group checked the bounds
against the seed-conditional normal form only. This group defines the
order-free local class (each coin continues on its own answers), proves that
under a pathwise cap a local design is in the normal form and under an
almost-sure cap almost every seed is, and states the lower bound, the minimax
bracket and the separation for the class itself.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the six targets and three components with their types written out;
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

GROUP = "TwoFlipDominance"
NAMES = ("Specification", "Kernel", "LocalForm", "PathwiseDepth", "AlmostSureDepth", "AlmostSureLower", "Members", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "75774324a450c5fb309d1b87cc3f281f47fdd5de00f846d07c8e4a1f8691ed6e"
TARGETS = {
    "TwoFlipDominance.dominance_pathwise": "TwoFlipDominance.PathwiseDominanceStatement",
    "TwoFlipDominance.dominance_seed": "TwoFlipDominance.SeedDominanceStatement",
    "TwoFlipDominance.local_class": "TwoFlipDominance.LocalClassStatement",
    "TwoFlipDominance.local_uniform_lower_bound": "TwoFlipDominance.LocalUniformLowerStatement",
    "TwoFlipDominance.local_lower": "TwoFlipDominance.LocalLowerStatement",
    "TwoFlipDominance.local_separation": "TwoFlipDominance.LocalSeparationStatement",
}
COMPONENTS = (
    "TwoFlipDominance.local_normal_form",
    "TwoFlipDominance.feedback_not_local",
    "TwoFlipDominance.local_minimax_lower",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    PathwiseCap A 2 → LocalAcquisition A → NoninteractiveCapTwo A :=
  TwoFlipDominance.dominance_pathwise

example :
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    AlmostSureCap A 2 → LocalAcquisition A →
    ∀ᵐ r ∂A.randomLaw,
      (∀ b b' : Bool, A.policy r [] ≠ none → A.policy r [b] ≠ none →
        A.policy r [b, b'] = none) ∧
      ∀ c : ℕ, A.policy r [] = some c →
        (∀ b : Bool, A.policy r [b] = none ∨ A.policy r [b] = some c) ∨
        ((∀ b : Bool, A.policy r [b] ≠ some c) ∧
          (A.policy r [false]).isSome = (A.policy r [true]).isSome) :=
  TwoFlipDominance.dominance_seed

example :
  (∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
      PathwiseCap A 2 → AlmostSureCap A 2) ∧
  (∃ A : AdaptiveEstimator Unit, (∀ r, A.policy r = stopAt 2 (fun _ => 0)) ∧
      PathwiseCap A 2 ∧ LocalAcquisition A) ∧
  (∃ A : AdaptiveEstimator Unit, (∀ r, A.policy r = stopAt 2 (fun xs => xs.length)) ∧
      PathwiseCap A 2 ∧ LocalAcquisition A) ∧
  localMinimax ≤ ENNReal.ofReal (1/64) :=
  TwoFlipDominance.local_class

example :
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    AlmostSureCap A 2 → LocalAcquisition A →
    ENNReal.ofReal (1547585/100000000) ≤ rareSquaredRisk A :=
  TwoFlipDominance.local_uniform_lower_bound

example :
  ENNReal.ofReal (15475/1000000) < localMinimax ∧ localMinimax ≤ ENNReal.ofReal (1/64) :=
  TwoFlipDominance.local_lower

example :
  ∃ A : AdaptiveEstimator Unit,
    (∀ r, A.policy r = stopAt 2 feedbackLabel) ∧
    (∀ x : ProcessTape, A.output ((), x) = feedbackOutput (processPrefix 2 x)) ∧
    PathwiseCap A 2 ∧ AlmostSureCap A 2 ∧ ¬ LocalAcquisition A ∧
    rareSquaredRisk A + ENNReal.ofReal (32/1000000) < localMinimax :=
  TwoFlipDominance.local_separation

example : ∀ (pol : List Bool → Option ℕ) (cont : ℕ → List Bool → Bool), TwoFlipDominance.LocalAt pol cont → TwoFlipDominance.StopsAtTwo pol → TwoFlipDominance.NormalAt pol :=
  TwoFlipDominance.local_normal_form

example : ¬ TwoFlipDominance.LocalAcquisition ThresholdHC.TwoFlipFeedback.feedbackEstimator :=
  TwoFlipDominance.feedback_not_local

example : ENNReal.ofReal ThresholdHC.TwoFlipFeedback.lowerValue ≤ TwoFlipDominance.localMinimax :=
  TwoFlipDominance.local_minimax_lower
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
        raise ValueError("Duplicate two-flip-dominance declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing two-flip-dominance target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed two-flip-dominance specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget ThresholdHC.TwoFlipFeedback ThresholdHC.TwoFlipDominance",
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
    print(f"All {len(TARGETS)} two-flip-dominance targets are certified")


if __name__ == "__main__":
    main()
