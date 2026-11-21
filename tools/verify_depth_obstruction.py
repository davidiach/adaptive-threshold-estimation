"""Audit part 1 of the bounded-depth obstruction of the nonlinear-population package.

Theorem thm:cap of research/2026-10-27-nonlinear-population/upper/proof-body.tex
says that feedback does not repair bounded-depth nonidentifiability: when
every coin word of length at most 2K has the same probability under two sign
profiles, every population procedure using at most 2K observations per coin,
with arbitrary pilots, interleaving and cross-coin feedback, has the same
transcript law under both, so its worst RMS error is at least half the target
separation. The group proves this for every per-coin cap N, every gap law and
every pair of sign laws with matching odd moments through depth N, with the
whole seed-and-transcript law equal; the floor from equal laws; a Lean-only
extension (half the cap-N diameter floors the rare-prior RMS risk of every
per-coin-capped procedure); and a bridge from the history-count cap used by
RestrictedRMS. The explicit odd-Legendre pair and its separation (part 2) and
the depth-tail bound are not stated.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the four targets and three components with their types written out;
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

GROUP = "DepthObstruction"
NAMES = ("Specification", "CappedPath", "OneCoin", "Bridge", "CappedTranscript", "Floor", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "08cc83afab8e7853102f3357bd5840d6c3af839106efb1bf88b7ed83e42cbf50"
TARGETS = {
    "DepthObstruction.capped_transcript": "DepthObstruction.CappedTranscriptStatement",
    "DepthObstruction.equal_law_floor": "DepthObstruction.EqualLawFloorStatement",
    "DepthObstruction.population_cap_floor": "DepthObstruction.PopulationCapFloorStatement",
    "DepthObstruction.history_cap_bridge": "DepthObstruction.HistoryCapBridgeStatement",
}
COMPONENTS = (
    "DepthObstruction.observable_law_capTapes",
    "DepthObstruction.squared_pair_floor",
    "DepthObstruction.measurable_capTapes",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (qH qL : SignLaw) (N : ℕ) (A : AdaptiveEstimator R),
    OddMomentMatch μ qH qL N → PerCoinCap A N →
    (experimentLaw μ A qH).map (fun z => (z.1.1, z.2)) =
      (experimentLaw μ A qL).map (fun z => (z.1.1, z.2)) :=
  DepthObstruction.capped_transcript

example :
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (qH qL : SignLaw),
    (experimentLaw μ A qH).map (fun z => (z.1.1, z.2)) =
      (experimentLaw μ A qL).map (fun z => (z.1.1, z.2)) →
    ENNReal.ofReal (|signMean μ qH.val - signMean μ qL.val| / 2) ≤
      max (rootMeanRisk (experimentLaw μ A qH) (populationOutput A) (signMean μ qH.val))
          (rootMeanRisk (experimentLaw μ A qL) (populationOutput A) (signMean μ qL.val)) :=
  DepthObstruction.equal_law_floor

example :
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (N : ℕ) (A : AdaptiveEstimator R), 0 ≤ ρ → PerCoinCap A N →
    ENNReal.ofReal (capDiameter μ ρ N / 2) ≤ rareRisk μ A ρ :=
  DepthObstruction.population_cap_floor

example :
  ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R) (N : ℕ),
    (∀ (s : R) (xs : List Bool) (j : ℕ), A.policy s xs = some j →
      (List.range xs.length).countP (fun i => decide (A.policy s (xs.take i) = some j)) < N) →
    PerCoinCap A N :=
  DepthObstruction.history_cap_bridge

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (N : ℕ), PerCoinCap A N →
    (experimentLaw μ A q).map (fun z => (z.1.1, z.2)) =
      (A.randomLaw.prod ((Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map
        (capTapes N))).map (fun z => (z.1, populationPath (A.policy z.1) z.2)) :=
  @DepthObstruction.observable_law_capTapes

example : ∀ {Ω : Type} [MeasurableSpace Ω] (M : Measure Ω) [IsProbabilityMeasure M]
    (f : Ω → ℝ), Measurable f → ∀ (a b : ℝ),
    ENNReal.ofReal ((a-b)^2/4) ≤
      max (∫⁻ w, ENNReal.ofReal ((f w - a)^2) ∂M) (∫⁻ w, ENNReal.ofReal ((f w - b)^2) ∂M) :=
  @DepthObstruction.squared_pair_floor

example : ∀ (N : ℕ), Measurable (capTapes N) :=
  DepthObstruction.measurable_capTapes
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
        raise ValueError("Duplicate depth-obstruction declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing depth-obstruction target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed depth-obstruction specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.CapIdentification ThresholdHC.RareAboveTwo ThresholdHC.DepthObstruction",
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
    print(f"All {len(TARGETS)} depth-obstruction targets are certified")


if __name__ == "__main__":
    main()
