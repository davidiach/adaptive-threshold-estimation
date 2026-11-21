"""Audit the 20+5 revisit witness of the rms-constants package.

The package research/2026-11-17-rms-constants proves, in research-only Lean
files, that a deterministic rule with a 20-flip pilot and five revisits of
pilot heads or tails, or five fresh flips, has RMS risk at most 0.188087 at
the gap 1/5 under a hard cap of 25 flips. The group moves those proofs into
the audited library with only their imports, namespace and option scoping
changed, and states the witness against the original experiment: the
labelling rule, the output as a function of the two head counts, the pathwise
cap, the uniform budget under every gap law and the risk bound. The minimax
and coefficient corollaries at 0.188087 are components; the audited
LargeBudgetRMS witness at 0.186752 is sharper.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the target and four components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker, including the decide +kernel risk certificate.
The statement was written after the proofs; it is pinned from this audit
onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "RevisitUpper"
NAMES = ("Specification", "RevisitHistory", "RevisitCertificate", "RevisitExperiment", "RevisitRisk", "RevisitWitness", "LabelRule", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "eadde0425717ac8a25880e358c2890f5274d215c75da038b3d489be1e937d7a0"
TARGETS = {
    "RevisitUpper.revisit_witness": "RevisitUpper.RevisitWitnessStatement",
}
COMPONENTS = (
    "RevisitUpper.label_rule",
    "RevisitUpper.revisit_squared_risk",
    "RevisitUpper.revisit_upper_25",
    "RevisitUpper.revisit_coefficient_upper",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∃ (L : List Bool → ℕ) (A : AdaptiveEstimator Unit) (f : ℕ → ℕ → ℝ),
    RevisitRule L ∧
    (∀ r, A.policy r = HardBudget.stopAt 25 L) ∧
    (∀ x : ProcessTape, A.output ((), x) =
      f (((Proofs.fullHist (processPrefix 25 x)).take 20).count true)
        (((Proofs.fullHist (processPrefix 25 x)).drop 20).count true)) ∧
    HardBudget.PathwiseCap A 25 ∧
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ], UniformBudget μ A 25) ∧
    maximalRMSRisk (Measure.dirac LargeBudgetRMS.fifthGap) A ≤
      ENNReal.ofReal (188087/1000000 : ℝ) :=
  RevisitUpper.revisit_witness

example : RevisitRule ThresholdHC.SharpRMS.Revisit.label :=
  RevisitUpper.label_rule

example : ∀ (q : SignLaw),
    squaredRisk (experimentLaw (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap) revisitEstimator q)
      (populationOutput revisitEstimator)
      (signMean (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap) q.val) ≤
        ENNReal.ofReal ((188087/1000000 : ℝ)^2) :=
  RevisitUpper.revisit_squared_risk

example : minimaxRisk (Measure.dirac ThresholdHC.SharpRMS.LargeBudget.fifthGap) 25 ≤
    ENNReal.ofReal (188087/1000000 : ℝ) :=
  RevisitUpper.revisit_upper_25

example : ∀ (c : ℝ), (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B) * c) ≤ minimaxRisk μ B) →
    c ≤ (188087/1000000 : ℝ) :=
  RevisitUpper.revisit_coefficient_upper
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
        raise ValueError("Duplicate revisit-upper declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing revisit-upper target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed revisit-upper specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RevisitUpper",
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
    print("The revisit-upper target is certified")


if __name__ == "__main__":
    main()
