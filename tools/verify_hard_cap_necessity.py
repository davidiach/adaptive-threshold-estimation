"""Audit the hard-cap counterexamples of the hard-budget RMS note.

Section 5 of research/2026-10-30-hard-budget-rms/NOTE.md shows that the
independent timeout-fallback ladder is needed: at mu = delta_(1/2) and
rho = 1/4, a base that reads b/4 fresh flips and, with probability 1/8,
first buys 4b discarded flips meets the stage premise of the observable
fallback reduction, but a single cap at 4b with the midpoint on timeout, or
one delay seed shared by every stage, keeps the squared risk at least
rho^2/32 = 1/512 at theta = 0. The group builds that base family, proves
the premise uniformly over the rare sign laws, gives the independent ladder
the reduction's bound 32 K(B)^2 (which falls below the floor), and proves
both floors for every estimator with the pinned seed law and output.

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

GROUP = "HardCapNecessity"
NAMES = ("Specification", "Rate", "Fresh", "Base", "Controllers", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "5e55ae53230299191f1698754eb31c8d35806aee25a1cb720cfee440daeb87bd"
TARGETS = {
    "HardCapNecessity.hard_cap_necessity": "HardCapNecessity.HardCapNecessityStatement",
    "HardCapNecessity.rare_rate": "HardCapNecessity.RareRateStatement",
}
COMPONENTS = (
    "HardCapNecessity.capBase_premise",
    "HardCapNecessity.ladder_floor",
    "HardCapNecessity.single_floor",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∃ (S : Type) (_ : MeasurableSpace S) (base : ℕ → AdaptiveEstimator S),
    (∀ j, (base j).randomLaw = (base 0).randomLaw) ∧ RarePremise base ∧
    (∃ indep : ℝ → AdaptiveEstimator (ℕ → S), ∀ B : ℝ, 0 ≤ B →
      (indep B).randomLaw = Measure.infinitePi (fun j => (base j).randomLaw) ∧
      PathwiseCap (indep B) ⌊B⌋₊ ∧
      (∀ m : ℕ, (reservation m : ℝ) ≤ B → B < reservation (m+1) → ∀ r table,
        (indep B).output (r, populationPath ((indep B).policy r) table) =
          idealFallback (R := fun _ => S) base (1/4) r table (m+1)) ∧
      (4 ≤ B → ∀ q : SignLaw, RarePrior (Measure.dirac halfGap) (1/4) q →
        squaredRisk (experimentLaw (Measure.dirac halfGap) (indep B) q) (populationOutput (indep B))
          (signMean (Measure.dirac halfGap) q.val) ≤ ENNReal.ofReal (32 * (rareRate B)^2))) ∧
    (∃ shared : ℝ → AdaptiveEstimator S, ∀ B : ℝ, 0 ≤ B →
      (shared B).randomLaw = (base 0).randomLaw ∧ PathwiseCap (shared B) ⌊B⌋₊ ∧
      (B < 4 → ∀ r table, (shared B).output (r, populationPath ((shared B).policy r) table) = 1/8) ∧
      (∀ m : ℕ, (reservation m : ℝ) ≤ B → B < reservation (m+1) → ∀ r table,
        (shared B).output (r, populationPath ((shared B).policy r) table) =
          idealFallback (R := fun _ => S) base (1/4) (fun _ => r) table (m+1))) ∧
    (∀ (k : ℕ) (A : AdaptiveEstimator S), A.randomLaw = (base 0).randomLaw →
      (∀ r table, A.output (r, populationPath (A.policy r) table) =
        idealFallback (R := fun _ => S) base (1/4) (fun _ => r) table k) →
      ENNReal.ofReal (1/512) ≤
        squaredRisk (experimentLaw (Measure.dirac halfGap) A zeroSigns)
          (populationOutput A) (signMean (Measure.dirac halfGap) zeroSigns.val)) ∧
    ∀ j : ℕ, 2 ≤ j →
      (∃ A : AdaptiveEstimator S, A.randomLaw = (base j).randomLaw ∧ PathwiseCap A (stageCap j) ∧
        ∀ r table, A.output (r, populationPath (A.policy r) table) =
          (stageResult (base j) (stageCap j) (1/4) r table).getD (1/8)) ∧
      ∀ A : AdaptiveEstimator S, A.randomLaw = (base j).randomLaw →
        (∀ r table, A.output (r, populationPath (A.policy r) table) =
          (stageResult (base j) (stageCap j) (1/4) r table).getD (1/8)) →
        ENNReal.ofReal (1/512) ≤
          squaredRisk (experimentLaw (Measure.dirac halfGap) A zeroSigns)
            (populationOutput A) (signMean (Measure.dirac halfGap) zeroSigns.val) :=
  HardCapNecessity.hard_cap_necessity

example :
  rareRate (1/2) = 1/4 ∧ (∀ b, 1/2 ≤ b → 0 ≤ rareRate b) ∧
  (∀ b b', 1/2 ≤ b → b ≤ b' → rareRate b ≤ Real.sqrt (b'/b) * rareRate b') ∧
  ∀ C : ℝ, ∃ B₀ : ℝ, 4 ≤ B₀ ∧ ∀ B : ℝ, B₀ ≤ B → 32 * C^2 * (rareRate B)^2 < 1/512 :=
  HardCapNecessity.rare_rate

example : RarePremise capBase :=
  HardCapNecessity.capBase_premise

example : ∀ (k : ℕ) (A : AdaptiveEstimator (Bool × Unit)),
    A.randomLaw = (capBase 0).randomLaw →
    (∀ r table, A.output (r, populationPath (A.policy r) table) =
      idealFallback (R := fun _ => Bool × Unit) capBase (1/4) (fun _ => r) table k) →
    ENNReal.ofReal (1/512) ≤
      squaredRisk (experimentLaw (Measure.dirac halfGap) A zeroSigns) (populationOutput A)
        (signMean (Measure.dirac halfGap) zeroSigns.val) :=
  HardCapNecessity.ladder_floor

example : ∀ (j : ℕ), 2 ≤ j → ∀ (A : AdaptiveEstimator (Bool × Unit)),
    A.randomLaw = (capBase j).randomLaw →
    (∀ r table, A.output (r, populationPath (A.policy r) table) =
      (stageResult (capBase j) (stageCap j) (1/4) r table).getD (1/8)) →
    ENNReal.ofReal (1/512) ≤
      squaredRisk (experimentLaw (Measure.dirac halfGap) A zeroSigns) (populationOutput A)
        (signMean (Measure.dirac halfGap) zeroSigns.val) :=
  HardCapNecessity.single_floor
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
        raise ValueError("Duplicate hard-cap-necessity declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing hard-cap-necessity target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed hard-cap-necessity specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.HardBudget ThresholdHC.RareAboveTwo ThresholdHC.HardCapNecessity",
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
    print(f"All {len(TARGETS)} hard-cap-necessity targets are certified")


if __name__ == "__main__":
    main()
