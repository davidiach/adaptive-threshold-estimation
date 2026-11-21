"""Audit the Giles--Haji-Ali assumptions for the nested-simulation class.

The final sentence of Corollary cor:nested (paper/v6/core.tex) says that every
measurable conditional model with U uniform on [0, 1], X in {-1, 1} and
D(U) = |E[X | U]|/2 uniform on (0, 1/4] satisfies Assumptions 2.1 and 2.4 of
Giles and Haji-Ali with uniform constants. The group defines that class,
transcribes the two assumptions from the in-repository paraphrases, and checks
the bounded density 2 at every delta_0 > 0 and the standardized moment
3^(q/2) at every q > 2 for every model of the class, with constants chosen
before the model. It also checks that the class is inhabited and contains
every hard sign-cell design of the continuous-state lower bounds, with the
same per-query law. The transcription has not been compared with the
verbatim text of arXiv:1802.05016v2.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the five targets and three components with their types written out;
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

GROUP = "NestedAssumptions"
NAMES = ("Specification", "Binary", "Model", "HardDesign", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "5d49c371b06a69b5ba594709becff795a9f8d14ae3a10d6853e2374e01374568"
TARGETS = {
    "NestedAssumptions.nested_assumptions": "NestedAssumptions.NestedAssumptionsStatement",
    "NestedAssumptions.uniform_constants": "NestedAssumptions.UniformConstantsStatement",
    "NestedAssumptions.hard_design_nested": "NestedAssumptions.HardDesignStatement",
    "NestedAssumptions.hard_design_law": "NestedAssumptions.HardDesignLawStatement",
    "NestedAssumptions.nested_model_nonempty": "NestedAssumptions.NestedModelNonemptyStatement",
}
COMPONENTS = (
    "NestedAssumptions.nested_density",
    "NestedAssumptions.condSD_binaryLaw",
    "NestedAssumptions.halfMagnitude_binaryLaw",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ p : unitInterval → unitInterval, NestedModel p →
    (∀ δ₀ : ℝ, 0 < δ₀ → GHABoundedDensity volume (binaryLaw p) 2 δ₀) ∧
    ∀ q : ℝ, 2 < q → GHAStandardizedMoment volume (binaryLaw p) q ((3 : ℝ) ^ (q / 2)) :=
  NestedAssumptions.nested_assumptions

example :
  ∃ ρ₀ δ₀ q C : ℝ, ∀ p : unitInterval → unitInterval, NestedModel p →
    GHABoundedDensity volume (binaryLaw p) ρ₀ δ₀ ∧ GHAStandardizedMoment volume (binaryLaw p) q C :=
  NestedAssumptions.uniform_constants

example :
  ∀ (h : Gap) (δ : ℝ) (D : CellDesign uniformGaps h δ) (s : Fin D.count → Bool),
    NestedModel (stateParameter (CellDesign.queryDesign uniformGaps h δ D) s) :=
  NestedAssumptions.hard_design_nested

example :
  ∀ (h : Gap) (δ : ℝ) (D : CellDesign uniformGaps h δ) (s : Fin D.count → Bool)
    (u : unitInterval),
    binaryLaw (stateParameter (CellDesign.queryDesign uniformGaps h δ D) s) u =
      (bernoulliMeasure true false (gapParameter (s (D.cell u)) (D.gap u))).map binaryValue :=
  NestedAssumptions.hard_design_law

example :
  ∃ p : unitInterval → unitInterval, NestedModel p :=
  NestedAssumptions.nested_model_nonempty

example : ∀ {p : unitInterval → unitInterval}, NestedModel p →
    volume.map (normalizedMean (binaryLaw p)) =
      volume.withDensity (fun z => ENNReal.ofReal (normalizedDensity z)) :=
  @NestedAssumptions.nested_density

example : ∀ (p : unitInterval → unitInterval) (u : unitInterval),
    condSD (binaryLaw p) u = Real.sqrt (1 - (condMean (binaryLaw p) u) ^ 2) :=
  NestedAssumptions.condSD_binaryLaw

example : ∀ (p : unitInterval → unitInterval) (u : unitInterval),
    |condMean (binaryLaw p) u| / 2 = |(p u : ℝ) - 1 / 2| :=
  NestedAssumptions.halfMagnitude_binaryLaw
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
        raise ValueError("Duplicate nested-assumptions declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing nested-assumptions target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed nested-assumptions specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.ObservedState ThresholdHC.ObservableSimulation ThresholdHC.ContinuousObserved ThresholdHC.NestedAssumptions",
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
    print(f"All {len(TARGETS)} nested-assumptions targets are certified")


if __name__ == "__main__":
    main()
