"""Audit the countable-reservoir termination counterexample.

The research note research/2026-10-27-minimax-audit/formal/stopping_bridge.tex
shows that finite expected work under one law does not transfer termination
to a second law once coins are drawn from a countable reservoir: querying
fresh coins with gap D and stopping when the walk of observed bits first
reaches +1 has E_P T = 4 and P(T < infinity) = 1 under the sign prior 5/8 at
D = 1/2, while under 3/8 it runs forever with probability 2/5 (8 and 2/9 at
D = 1/4). The group checks the general symmetric-prior law for every
realization of the unrestricted creation model, the two examples, the
refutation of the naive two-law stopping bridge with created labels, the
proposition as an existence claim, and the same counterexample in the
original adaptive experiment.

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

GROUP = "ReservoirTermination"
NAMES = ("Specification", "FirstPassage", "WalkLaw", "Realized", "Examples", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "a7072963c5fb5e1bf39a5f8dca63bb4ff59149b6d345781237fc1289a3f549ee"
TARGETS = {
    "ReservoirTermination.walk_first_passage": "ReservoirTermination.WalkFirstPassageStatement",
    "ReservoirTermination.half_gap_counterexample": "ReservoirTermination.HalfGapExampleStatement",
    "ReservoirTermination.quarter_gap_counterexample": "ReservoirTermination.QuarterGapExampleStatement",
    "ReservoirTermination.naive_bridge_fails": "ReservoirTermination.NaiveBridgeFailsStatement",
    "ReservoirTermination.reservoir_counterexample": "ReservoirTermination.ReservoirCounterexampleStatement",
    "ReservoirTermination.original_experiment": "ReservoirTermination.OriginalExperimentStatement",
}
COMPONENTS = (
    "ReservoirTermination.walk_plus_limits",
    "ReservoirTermination.walk_minus_limits",
    "ReservoirTermination.walkExp_tilt",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (seed : Ω → Seed) (tape : Ω → ProcessTape) (d η : ℝ),
    (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    0 < d → d ≤ 1/2 → 0 < η → η < 1/2 →
    (RealizesCreationPrefixes μ ν seed tape (fun _ => walkPolicy)
        (fun _ _ => d) (fun _ _ => 1/2 + η) →
      ν (RunsForever tape) = 0 ∧
      (∫⁻ ω, totalProcessWork (tape ω) ∂ν) = ENNReal.ofReal (1 / (4 * d * η))) ∧
    (RealizesCreationPrefixes μ ν seed tape (fun _ => walkPolicy)
        (fun _ _ => d) (fun _ _ => 1/2 - η) →
      ν (RunsForever tape) = ENNReal.ofReal (8 * d * η / (1 + 4 * d * η)) ∧
      (∫⁻ ω, totalProcessWork (tape ω) ∂ν) = ∞) :=
  ReservoirTermination.walk_first_passage

example :
  (∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (seed : Ω → Seed) (tape : Ω → ProcessTape),
    (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    RealizesCreationPrefixes μ P seed tape (fun _ => walkPolicy)
      (fun _ _ => 1/2) (fun _ _ => 5/8) →
    P (RunsForever tape) = 0 ∧ (∫⁻ ω, totalProcessWork (tape ω) ∂P) = 4) ∧
  (∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (Q : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (seed : Ω → Seed) (tape : Ω → ProcessTape),
    (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    RealizesCreationPrefixes μ Q seed tape (fun _ => walkPolicy)
      (fun _ _ => 1/2) (fun _ _ => 3/8) →
    Q (RunsForever tape) = 2/5) :=
  ReservoirTermination.half_gap_counterexample

example :
  (∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (seed : Ω → Seed) (tape : Ω → ProcessTape),
    (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    RealizesCreationPrefixes μ P seed tape (fun _ => walkPolicy)
      (fun _ _ => 1/4) (fun _ _ => 5/8) →
    P (RunsForever tape) = 0 ∧ (∫⁻ ω, totalProcessWork (tape ω) ∂P) = 8) ∧
  (∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (Q : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (seed : Ω → Seed) (tape : Ω → ProcessTape),
    (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    RealizesCreationPrefixes μ Q seed tape (fun _ => walkPolicy)
      (fun _ _ => 1/4) (fun _ _ => 3/8) →
    Q (RunsForever tape) = 2/9) :=
  ReservoirTermination.quarter_gap_counterexample

example :
  ¬ CreationTwoLawStoppingStatement :=
  ReservoirTermination.naive_bridge_fails

example :
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P Q : Measure Ω) (tape : Ω → ProcessTape),
    IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
    (∀ n b, MeasurableSet {ω | tape ω n = b}) ∧
    RealizesCreationPrefixes (Measure.dirac ()) P (fun _ => ()) tape (fun _ => walkPolicy)
      (fun _ _ => 1/2) (fun _ _ => 5/8) ∧
    RealizesCreationPrefixes (Measure.dirac ()) Q (fun _ => ()) tape (fun _ => walkPolicy)
      (fun _ _ => 1/2) (fun _ _ => 3/8) ∧
    P (RunsForever tape) = 0 ∧ (∫⁻ ω, totalProcessWork (tape ω) ∂P) = 4 ∧
    Q (RunsForever tape)ᶜ = 3/5 ∧ Q (RunsForever tape) = 2/5 ∧
    (∫⁻ ω, totalProcessWork (tape ω) ∂Q) = ∞ :=
  ReservoirTermination.reservoir_counterexample

example :
  expectedWork (Measure.dirac halfGap) walkEstimator (constantSignLaw (5/8) (by norm_num)) = 4 ∧
  experimentLaw (Measure.dirac halfGap) walkEstimator (constantSignLaw (3/8) (by norm_num))
    (RunsForever (Ω := PopulationSeed Unit × ProcessTape) Prod.snd) = 2/5 ∧
  expectedWork (Measure.dirac halfGap) walkEstimator (constantSignLaw (3/8) (by norm_num)) = ∞ ∧
  expectedWork (Measure.dirac quarterGap) walkEstimator (constantSignLaw (5/8) (by norm_num)) = 8 ∧
  experimentLaw (Measure.dirac quarterGap) walkEstimator (constantSignLaw (3/8) (by norm_num))
    (RunsForever (Ω := PopulationSeed Unit × ProcessTape) Prod.snd) = 2/9 ∧
  ∀ B : ℝ, ¬ UniformBudget (Measure.dirac halfGap) walkEstimator B :=
  ReservoirTermination.original_experiment

example : ∀ (r : ℝ), 1/2 < r → r ≤ 1 →
    Filter.Tendsto (fun n => walkExp r n (fun xs => (xs.length : ℝ))) Filter.atTop (nhds (1/(2*r-1))) ∧
    Filter.Tendsto (fun n => walkExp r n walkAlive) Filter.atTop (nhds 0) :=
  ReservoirTermination.walk_plus_limits

example : ∀ (r : ℝ), 1/2 < r → r < 1 →
    Filter.Tendsto (fun n => walkExp (1-r) n walkAlive) Filter.atTop (nhds (1 - (1-r)/r)) ∧
    ∀ n : ℕ, (n : ℝ) * (1 - (1-r)/r) ≤ walkExp (1-r) n (fun xs => (xs.length : ℝ)) :=
  ReservoirTermination.walk_minus_limits

example : ∀ (r : ℝ), r ≠ 0 → r ≠ 1 → ∀ (n : ℕ) (g : List Bool → ℝ),
    walkExp (1-r) n g = walkExp r n (fun xs => g xs * ((1-r)/r)^(walkValue xs)) :=
  ReservoirTermination.walkExp_tilt
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
        raise ValueError("Duplicate reservoir-termination declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing reservoir-termination target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed reservoir-termination specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.ReservoirTermination",
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
    print(f"All {len(TARGETS)} reservoir-termination targets are certified")


if __name__ == "__main__":
    main()
