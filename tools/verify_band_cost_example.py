"""Audit the 64-band example of the band-cost selection algorithm.

The finite-law section of the v6 paper says the selection algorithm certifies
an optimizer on a 64-band example with 65 terminal states, and
docs/BAND_COST_SELECTION.md defines it: gaps 2^-i and masses proportional to
their squares for i = 1, ..., 64, rho = 1/4 and budget 2^32. Every nonempty
suffix has the same cost; the run checks 4160 transitions and 65 terminal
states and certifies that retaining the two largest gaps attains K. The group
checks the instance, the equal one-atom costs, the optimizer against every
submeasure with the cap inactive, the strict uniqueness of the two-gap mask
among all 2^64 hard masks (an added strengthening), and the run of the formal
solver on the actual support menus. The Python toolkit run is not checked.

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

GROUP = "BandCostExample"
NAMES = ("Specification", "Instance", "Objective", "Rearrange", "Optimal", "Frontier", "Solver", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "9b6b9c0d444eaeea1b0517a59159bf213b4895d322585adf7b0f0f0da62b0182"
TARGETS = {
    "BandCostExample.setup": "BandCostExample.SetupStatement",
    "BandCostExample.equal_cost": "BandCostExample.EqualCostStatement",
    "BandCostExample.unique_hard_minimum": "BandCostExample.UniqueHardMinimumStatement",
    "BandCostExample.optimizer": "BandCostExample.OptimizerStatement",
    "BandCostExample.solver_run": "BandCostExample.SolverRunStatement",
}
COMPONENTS = (
    "BandCostExample.mem_menus",
    "BandCostExample.zsum_eq",
    "BandCostExample.J_eq",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  IsProbabilityMeasure law ∧ law.support = Set.range atoms ∧
  (∀ i, atoms i ∈ band i.val) ∧ 1 / Real.sqrt 4294967296 = (1/65536 : ℝ) ∧
  ∀ s, retained s ≤ law :=
  BandCostExample.setup

example :
  (∀ i : Fin 64, GapLawMenus.cost law ({atoms i} : Finset Gap) = 1 / ∑ j, (atoms j : ℝ)^2) ∧
  0 < 1 / ∑ j : Fin 64, (atoms j : ℝ)^2 :=
  BandCostExample.equal_cost

example :
  ∀ s : Fin 64 → Bool, s ≠ topTwo →
    selectionObjective law (1/4) 4294967296 (retained topTwo) <
      selectionObjective law (1/4) 4294967296 (retained s) :=
  BandCostExample.unique_hard_minimum

example :
  selectionObjective law (1/4) 4294967296 (retained topTwo) < ENNReal.ofReal (1/4) ∧
  selection law (1/4) 4294967296 =
    selectionObjective law (1/4) 4294967296 (retained topTwo) ∧
  retained topTwo = law.restrict {d : Gap | (d : ℝ) = 1/2 ∨ (d : ℝ) = 1/4} :=
  BandCostExample.optimizer

example :
  (suffixChoices atomSet).card = 2^64 ∧
  (menus atomSet (occupiedBands atomSet)).length = 64 ∧
  (∀ M ∈ menus atomSet (occupiedBands atomSet), M.card = 2) ∧
  transitionCount (GapLawMenus.cost law) (GapLawMenus.saving law (1 / Real.sqrt 4294967296))
      (menus atomSet (occupiedBands atomSet)) = 4160 ∧
  (solve (GapLawMenus.cost law) (GapLawMenus.saving law (1 / Real.sqrt 4294967296))
      (menus atomSet (occupiedBands atomSet))).card = 65 ∧
  ∃ xs ∈ solve (GapLawMenus.cost law) (GapLawMenus.saving law (1 / Real.sqrt 4294967296))
      (menus atomSet (occupiedBands atomSet)),
    (traceSet xs : Set Gap) = {d : Gap | (d : ℝ) = 1/2 ∨ (d : ℝ) = 1/4} ∧
    selection law (1/4) 4294967296 =
      ENNReal.ofReal (menuObjective law (1/4) 4294967296 xs) :=
  BandCostExample.solver_run

example : ∀ {M : Finset (Finset Gap)}, M ∈ menus atomSet (occupiedBands atomSet) →
    ∃ i : Fin 64, M = {∅, {atoms i}} :=
  @BandCostExample.mem_menus

example : zsum = (1 - (1/4 : ℝ)^64)/3 :=
  BandCostExample.zsum_eq

example : ∀ (s : Fin 64 → Bool), J s = min (1/4) (V s) :=
  BandCostExample.J_eq
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
        raise ValueError("Duplicate band-cost-example declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing band-cost-example target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed band-cost-example specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix ThresholdHC.BandCostSelection ThresholdHC.GapLawMenus ThresholdHC.BandCostExample",
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
    print(f"All {len(TARGETS)} band-cost-example targets are certified")


if __name__ == "__main__":
    main()
