"""Audit the pilot-feedback separations at the gap 1/5 with budget 25.

The 18-flip pilot is followed by seven distinct-label follow-ups. In the
original population experiment:

* every precommitted algorithm, which fixes all seven follow-up actions after
  the pilot, has worst RMS risk at least 0.18735887;
* every one-update algorithm, which chooses a split k and the first k actions
  after the pilot and the remaining ones after their answers, has worst RMS
  risk at least 0.186960371;
* the adaptive witness has strictly smaller worst RMS risk than both.

The proof modules are copies, with library imports, the namespace
ThresholdHC.PilotFeedback and three named Decidable instances, of
research/2026-11-18-pilot-feedback and research/2026-11-18-scheduled-update,
which stay unchanged. Since 23 November 2026 ScheduledCertificate.lean
checks each row of the one-update certificate in a form whose weights the
kernel reduces to literals (`fastRows`), proved to give `Row`. The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification file; the policy classes it names, defined in the
   proof modules, are fixed by the definition lock of verify_project_axioms.py;
3. restates the four targets and ten component theorems, including the
   integer certificates and the ordered-transcript reduction, with their types
   written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker, which re-evaluates the integer certificates.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "PilotFeedback"
NAMES = (
    "FeedbackTable", "FeedbackRisk", "FeedbackComparison", "FeedbackSeparation",
    "OrderedPolicy", "OrderedExperiment", "OrderedCounts", "OrderedBayes", "OrderedReduction",
    "OrderedPopulation", "FixedHorizonRisk", "ScheduledPolicy", "ScheduledBounds",
    "ScheduledCertificate", "ScheduledBayes", "ScheduledPopulation", "Specification", "Full",
)
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "581ac69149e51c6b513beae83c6419cfd088a5705ad41ac4c12fb81325e8fa72"
TARGETS = {
    "PilotFeedback.precommitted_rms_lower": "PilotFeedback.PrecommittedLowerStatement",
    "PilotFeedback.precommitted_rms_separation": "PilotFeedback.PrecommittedSeparationStatement",
    "PilotFeedback.one_update_rms_lower": "PilotFeedback.OneUpdateLowerStatement",
    "PilotFeedback.one_update_rms_separation": "PilotFeedback.OneUpdateSeparationStatement",
}
COMPONENTS = (
    "PilotFeedback.all_rows",
    "PilotFeedback.total_bound",
    "PilotFeedback.worstFour_lower",
    "PilotFeedback.strict_separation",
    "PilotFeedback.Ordered.ordered_reduction",
    "PilotFeedback.Ordered.counts_marginal",
    "PilotFeedback.Ordered.original_lower",
    "PilotFeedback.Scheduled.certified",
    "PilotFeedback.Scheduled.certificate_total",
    "PilotFeedback.Scheduled.four_lower",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ s : PilotFeedback.Ordered.Schedule, A.policy r = PilotFeedback.Ordered.policy s) →
    ENNReal.ofReal (18735887/100000000 : ℝ) ≤ maximalRMSRisk (Measure.dirac fifthGap) A :=
  PilotFeedback.precommitted_rms_lower

example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ s : PilotFeedback.Ordered.Schedule, A.policy r = PilotFeedback.Ordered.policy s) →
    maximalRMSRisk (Measure.dirac fifthGap) pilotEstimator <
      maximalRMSRisk (Measure.dirac fifthGap) A :=
  PilotFeedback.precommitted_rms_separation

example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ P : PilotFeedback.Scheduled.Plan, A.policy r = PilotFeedback.Scheduled.policy P) →
    ENNReal.ofReal (186960371/1000000000 : ℝ) ≤ maximalRMSRisk (Measure.dirac fifthGap) A :=
  PilotFeedback.one_update_rms_lower

example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ P : PilotFeedback.Scheduled.Plan, A.policy r = PilotFeedback.Scheduled.policy P) →
    maximalRMSRisk (Measure.dirac fifthGap) pilotEstimator <
      maximalRMSRisk (Measure.dirac fifthGap) A :=
  PilotFeedback.one_update_rms_separation

example : ∀ (j : Fin 19) (h t : Fin 8), PilotFeedback.legal j h t →
    PilotFeedback.rowBound j ≤ PilotFeedback.rowFloor j h t :=
  PilotFeedback.all_rows

example : PilotFeedback.sumTo PilotFeedback.rowBound 19 = 351033484000000 :=
  PilotFeedback.total_bound

example : ∀ {Ω : Type _} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → PilotFeedback.Rule),
    (∀ i, Measurable fun z => ENNReal.ofReal (PilotFeedback.pointMSE (r z) i)) →
    ENNReal.ofReal ((18735887/100000000 : ℝ)^2) ≤
      ⨆ i : Fin 4, ∫⁻ z, ENNReal.ofReal (PilotFeedback.pointMSE (r z) i) ∂μ :=
  @PilotFeedback.worstFour_lower

example : ∀ {Ω : Type _} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → PilotFeedback.Rule),
    (∀ i, Measurable fun z => ENNReal.ofReal (PilotFeedback.pointMSE (r z) i)) →
    (⨆ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator q)
      (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) q.val)) <
      ⨆ i : Fin 4, ∫⁻ z, ENNReal.ofReal (PilotFeedback.pointMSE (r z) i) ∂μ :=
  @PilotFeedback.strict_separation

example : ∀ (s : PilotFeedback.Ordered.Schedule) (p : ℝ), p ∈ Set.Icc 0 1 →
    ∀ (X : List Bool → ℝ),
    (∑ w : Prefix 25, SharpRMS.Revisit.law (PilotFeedback.Ordered.policy s) p w *
      X (Proofs.fullHist w)) =
    ∑ g ∈ PilotFeedback.Ordered.support s,
      PilotFeedback.Ordered.groupedMass s p g * PilotFeedback.Ordered.uniformOrder s g X :=
  PilotFeedback.Ordered.ordered_reduction

example : ∀ (s : PilotFeedback.Ordered.Schedule) (p : ℝ), p ∈ Set.Icc 0 1 →
    ∀ (g : PilotFeedback.Ordered.Counts), g ∈ PilotFeedback.Ordered.support s →
    (∑ w : Prefix 25, SharpRMS.Revisit.law (PilotFeedback.Ordered.policy s) p w *
      (if PilotFeedback.Ordered.counts s [] (Proofs.fullHist w) = g then (1:ℝ) else 0)) =
      PilotFeedback.Ordered.groupedMass s p g :=
  @PilotFeedback.Ordered.counts_marginal

example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ s : PilotFeedback.Ordered.Schedule, A.policy r = PilotFeedback.Ordered.policy s) →
    ENNReal.ofReal ((18735887/100000000 : ℝ)^2) ≤ PilotFeedback.Ordered.fourRisk A :=
  @PilotFeedback.Ordered.original_lower

example : ∀ j : Fin 19, PilotFeedback.Scheduled.Row j :=
  PilotFeedback.Scheduled.certified

example : 186960371^2 * 10^6 ≤ PilotFeedback.Scheduled.pilotSum 18 0 :=
  PilotFeedback.Scheduled.certificate_total

example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ r, ∃ P : PilotFeedback.Scheduled.Plan, A.policy r = PilotFeedback.Scheduled.policy P) →
    ENNReal.ofReal ((186960371/1000000000 : ℝ)^2) ≤ PilotFeedback.Ordered.fourRisk A :=
  @PilotFeedback.Scheduled.four_lower
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
        raise ValueError("Duplicate pilot-feedback declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing pilot-feedback target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed pilot-feedback specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.SharpRMS",
        "open ThresholdHC.SharpRMS.LargeBudget ThresholdHC.SharpRMS.Pilot",
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
    print(f"All {len(TARGETS)} pilot-feedback targets are certified")


if __name__ == "__main__":
    main()
