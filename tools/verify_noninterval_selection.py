"""Audit the noninterval optimal assignment of the rare-event paper.

At the three-atom law with masses (1-e)/2, e, (1-e)/2 at the gaps 1/2, 1/4,
1/8 (e = 1/1024), rho = 1/4 and h = B^(-1/2) = 1/1024, the paper's table gives
open rational enclosures of the inner cost divided by h for the eight hard
retained sets, the unique minimum retains {1/2, 1/8}, the cap is inactive, and
no interval retention is optimal. The group checks the eight enclosures with
kernel-checked interval certificates, the strict minimum, attainment by the
original functional, and the noninterval conclusion.

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

GROUP = "NonintervalSelection"
NAMES = ("Specification", "Instance", "Certificates", "Table", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "5c9c21d80309ddcb810e406c061c2891d50a0ae2565a228e66fa2fcdc7036ac5"
TARGETS = {
    "NonintervalSelection.setup": "NonintervalSelection.SetupStatement",
    "NonintervalSelection.enclosure": "NonintervalSelection.EnclosureStatement",
    "NonintervalSelection.unique_hard_minimum": "NonintervalSelection.UniqueHardMinimumStatement",
    "NonintervalSelection.original_optimizer": "NonintervalSelection.OriginalOptimizerStatement",
    "NonintervalSelection.noninterval": "NonintervalSelection.NonintervalStatement",
}
COMPONENTS = (
    "NonintervalSelection.objective_toReal",
    "NonintervalSelection.enclosures_bounds",
    "NonintervalSelection.selection_attained",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  IsProbabilityMeasure law ∧ 1 / Real.sqrt 1048576 = (1/1024 : ℝ) ∧
    (∀ i, (1/1024 : ℝ) < (atoms i : ℝ)) ∧ ∀ s, retained s ≤ law :=
  NonintervalSelection.setup

example :
  (∀ s, ∃ e ∈ enclosures, e.1 = s) ∧
  ∀ e ∈ enclosures,
    (e.2.1 : ℝ) < (selectionObjective law (1/4) 1048576 (retained e.1)).toReal / (1 / Real.sqrt 1048576) ∧
    (selectionObjective law (1/4) 1048576 (retained e.1)).toReal / (1 / Real.sqrt 1048576) < (e.2.2 : ℝ) :=
  NonintervalSelection.enclosure

example :
  ∀ s : Fin 3 → Bool, s ≠ optimalMask →
    selectionObjective law (1/4) 1048576 (retained optimalMask) <
      selectionObjective law (1/4) 1048576 (retained s) :=
  NonintervalSelection.unique_hard_minimum

example :
  selectionObjective law (1/4) 1048576 (retained optimalMask) < ENNReal.ofReal (1/4) ∧
  selection law (1/4) 1048576 = selectionObjective law (1/4) 1048576 (retained optimalMask) ∧
  retained optimalMask = law.restrict {d : Gap | (d : ℝ) = 1/2 ∨ (d : ℝ) = 1/8} :=
  NonintervalSelection.original_optimizer

example :
  0 < masses 1 ∧
  (¬ ∃ I : Set ℝ, I.OrdConnected ∧ ∀ i, (optimalMask i = true ↔ (atoms i : ℝ) ∈ I)) ∧
  ∀ I : Set ℝ, I.OrdConnected →
    selection law (1/4) 1048576 <
      selectionObjective law (1/4) 1048576 (law.restrict {d : Gap | (d : ℝ) ∈ I}) :=
  NonintervalSelection.noninterval

example : ∀ (s : Fin 3 → Bool), NonintervalSelection.J s < 1/4 →
    (selectionObjective law (1/4) 1048576 (retained s)).toReal = NonintervalSelection.J s :=
  @NonintervalSelection.objective_toReal

example : ∀ e ∈ enclosures,
    ((e.2.1 : ℝ) + 1/10^7)/1024 ≤ NonintervalSelection.J e.1 ∧
      NonintervalSelection.J e.1 ≤ ((e.2.2 : ℝ) - 1/10^7)/1024 :=
  @NonintervalSelection.enclosures_bounds

example : ∃ s : Fin 3 → Bool, (selection law (1/4) 1048576).toReal = NonintervalSelection.J s :=
  NonintervalSelection.selection_attained
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
        raise ValueError("Duplicate noninterval-selection declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing noninterval-selection target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed noninterval-selection specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.NonintervalSelection",
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
    print(f"All {len(TARGETS)} noninterval-selection targets are certified")


if __name__ == "__main__":
    main()
