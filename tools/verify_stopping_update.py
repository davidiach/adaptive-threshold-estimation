"""Audit the one-stopping-update separation promoted from its research package.

research/2026-11-18-stopping-update: at the gap 1/5 with budget 25, an
algorithm that flips 18 pilot coins once and then follows a seven-action
schedule may replace the rest of that schedule once, at a stopping time of the
observed answers. Every such algorithm has worst RMS risk at least
0.186844275, so the adaptive witness, at most 0.186752, is strictly better.
The research certificate checked each of 19 pilot-count rows in one kernel
evaluation and its build ran out of memory above 13.5 GB. The library first
split each row into 27 pieces; since 23 November 2026 each row is checked
whole, over eleven row modules, in a form whose weights the kernel reduces to
literals (`fastRowCheck`, proved equal to `rowCheck`). The one-update class
of PilotFeedback is contained in this one.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the two targets and three components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker, which re-evaluates every certificate row. The
statements were written before the proofs and reviewed before the pin; they
are pinned from this audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "StoppingUpdate"
NAMES = ("Specification", "StoppingBounds", "StoppingPieces", "StoppingRows0to4", "StoppingRow5", "StoppingRow6", "StoppingRow7", "StoppingRow8", "StoppingRow9", "StoppingRow10", "StoppingRow11", "StoppingRow12", "StoppingRow13", "StoppingRows14to18", "StoppingCertificate", "StoppingPolicy", "StoppingBayes", "StoppingPopulation", "StoppingEmbedding", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "4aa12e08ee298a95005090608b5d11e9027fdebbf0a90d766143f41ec0f71ca9"
TARGETS = {
    "StoppingUpdate.one_stopping_update_rms_lower": "StoppingUpdate.OneStoppingUpdateLowerStatement",
    "StoppingUpdate.one_stopping_update_rms_separation": "StoppingUpdate.OneStoppingUpdateSeparationStatement",
}
COMPONENTS = (
    "StoppingUpdate.certified",
    "StoppingUpdate.total",
    "StoppingUpdate.scheduled_embeds",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ P : Plan, A.policy r = policy P) →
    ENNReal.ofReal (186844275/1000000000 : ℝ) ≤
      maximalRMSRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap) A :=
  StoppingUpdate.one_stopping_update_rms_lower

example :
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ P : Plan, A.policy r = policy P) →
    maximalRMSRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap)
        ThresholdHC.SharpRMS.Pilot.pilotEstimator <
      maximalRMSRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap) A :=
  StoppingUpdate.one_stopping_update_rms_separation

example : ∀ j : Fin 19, StoppingUpdate.rowCheck j = true :=
  StoppingUpdate.certified

example : 186844275^2 * 10^6 ≤ StoppingUpdate.pilotSum 18 0 :=
  StoppingUpdate.total

example : ∀ (P : ThresholdHC.PilotFeedback.Scheduled.Plan),
    ∃ Q : StoppingUpdate.Plan, StoppingUpdate.policy Q = ThresholdHC.PilotFeedback.Scheduled.policy P :=
  StoppingUpdate.scheduled_embeds
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
        raise ValueError("Duplicate stopping-update declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing stopping-update target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed stopping-update specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.StoppingUpdate",
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
    print(f"All {len(TARGETS)} stopping-update targets are certified")


if __name__ == "__main__":
    main()
