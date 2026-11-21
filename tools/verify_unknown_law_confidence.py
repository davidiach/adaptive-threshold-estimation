"""Audit the simpler unknown-law confidence sequence.

docs/UNKNOWN_LAW_CONFIDENCE.md describes a confidence sequence that uses
neither the gap law nor a bound on its small-gap tail: at stage j it buys
m_j flips from each of n_j fresh items, declares strict positive and negative
items with Hoeffding margins, and intersects the stage intervals completed
within the budget. For every probability law of positive gaps and every
measurable gap-dependent sign law, and a supplied bound u >= theta (or
u = 1), one event of probability at least 1 - delta gives coverage at every
integer budget and the stage width bound P(D <= 2 r_j) + 3 a_j + 3 tau_j, and
the width tends to zero on that event. The group proves this for the
controller in the observable simulation, the measurability of the success
event, and the corollary at a data-dependent stopping budget.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the two targets and three components with their types written out;
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

GROUP = "UnknownLawConfidence"
NAMES = ("Specification", "Counts", "Word", "Item", "Population", "Sample", "Controller", "Limit", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "774f298459475aa0f025afc3b02e269886cf2857112ce02163e6b78809a11631"
TARGETS = {
    "UnknownLawConfidence.unknown_law_confidence": "UnknownLawConfidence.UnknownLawConfidenceStatement",
    "UnknownLawConfidence.unknown_law_stopping": "UnknownLawConfidence.UnknownLawStoppingStatement",
}
COMPONENTS = (
    "UnknownLawConfidence.measurableSet_successEvent",
    "UnknownLawConfidence.successEvent_probability",
    "UnknownLawConfidence.widthBound_tendsto",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ {δ : ℝ} (u : ℝ), 0 < δ → δ < 1 →
    (∀ B : ℕ, ∀ upper : Bool, PathwiseCap (controller δ u B upper) B) ∧
    (∀ B C : ℕ, B ≤ C → ∀ (upper upper' : Bool) (r : Seed) (xs : List Bool),
      xs.length < ArbitraryLawController.spent (R := fun _ => Unit) (stage δ)
        (stageCount (B : ℝ)) →
      (controller δ u C upper').policy r xs = (controller δ u B upper).policy r xs) ∧
    (∀ B C : ℕ, B ≤ C → ∀ z : Seed × Table,
      (interval δ u B z).1 ≤ (interval δ u C z).1 ∧
        (interval δ u C z).2 ≤ (interval δ u B z).2) ∧
    (∀ (B : ℕ) (z : Seed × Table), 0 ≤ (interval δ u B z).1 ∧ (interval δ u B z).2 ≤ u) ∧
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
      (∀ (B : ℕ) (upper : Bool),
        originalSimulationLaw μ (controller δ u B upper) q = streamLaw μ q δ) ∧
      (signMean μ q.val ≤ u → 1 - ENNReal.ofReal δ ≤ streamLaw μ q δ (successEvent μ q δ u)) ∧
      1 - ENNReal.ofReal δ ≤ streamLaw μ q δ (successEvent μ q δ 1)) ∧
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ], Tendsto (widthBound μ δ) atTop (𝓝 0)) ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (z : Seed × Table),
      z ∈ successEvent μ q δ u →
        Tendsto (fun B : ℕ => Anytime.halfWidth (interval δ u B z)) atTop (𝓝 0) :=
  UnknownLawConfidence.unknown_law_confidence

example :
  ∀ (μ : Measure Gap) (q : SignLaw) (δ u : ℝ) (z : Seed × Table),
    z ∈ successEvent μ q δ u → ∀ τ : Seed × Table → ℕ,
      ((interval δ u (τ z) z).1 ≤ signMean μ q.val ∧
        signMean μ q.val ≤ (interval δ u (τ z) z).2) ∧
      ∀ j : ℕ, j < stageCount ((τ z : ℕ) : ℝ) →
        2 * Anytime.halfWidth (interval δ u (τ z) z) ≤ widthBound μ δ j :=
  UnknownLawConfidence.unknown_law_stopping

example : ∀ (μ : Measure Gap) (q : SignLaw) (δ u : ℝ),
    MeasurableSet (successEvent μ q δ u) :=
  UnknownLawConfidence.measurableSet_successEvent

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {δ u : ℝ},
    0 < δ → signMean μ q.val ≤ u →
    1 - ENNReal.ofReal δ ≤ streamLaw μ q δ (successEvent μ q δ u) :=
  @UnknownLawConfidence.successEvent_probability

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {δ : ℝ}, 0 < δ → δ ≤ 1 →
    Tendsto (widthBound μ δ) atTop (𝓝 0) :=
  @UnknownLawConfidence.widthBound_tendsto
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
        raise ValueError("Duplicate unknown-law-confidence declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing unknown-law-confidence target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed unknown-law-confidence specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open Filter Topology ThresholdHC ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation ThresholdHC.UnknownLawConfidence",
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
    print(f"All {len(TARGETS)} unknown-law-confidence targets are certified")


if __name__ == "__main__":
    main()
