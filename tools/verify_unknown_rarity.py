"""Audit the obstruction to completely uniform adaptation to unknown rarity.

docs/process/TRACK_D.md (restated in docs/SECONDARY_CLAIMS.md) fixes a known
gap 0 < d < 1/2 and a budget-indexed family of estimators that does not
receive the rarity bound rho and stops almost surely at every constant
positive-sign prior theta in [0, 1/4]. No finite C makes the RMS error at
most C min(rho, sqrt(rho)/(d sqrt B)) for every budget, every
rho in (0, 1/4] and every theta <= rho. The group proves this in the Tier 6
adaptive experiment at the gap law dirac d, the remark that finite expected
work gives the same obstruction, the stopped-transcript absolute continuity
the proof uses, and, beyond the source, the obstruction for one estimator at
one budget B > 4C^2/d^2 that stops almost surely at theta = 1/4 only.

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

GROUP = "UnknownRarity"
NAMES = ("Specification", "Transfer", "Risk", "Obstruction", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "8c334564fd9085d8f0d281a728653f02959d2337815f335a376c7f0197c9b560"
TARGETS = {
    "UnknownRarity.unknown_rarity_obstruction": "UnknownRarity.UnknownRarityObstructionStatement",
    "UnknownRarity.fixed_budget_obstruction": "UnknownRarity.FixedBudgetObstructionStatement",
    "UnknownRarity.expected_work_obstruction": "UnknownRarity.ExpectedWorkObstructionStatement",
    "UnknownRarity.stopped_transcript_ac": "UnknownRarity.StoppedTranscriptACStatement",
}
COMPONENTS = (
    "UnknownRarity.dirac_null_transfer",
    "UnknownRarity.stops_of_expectedWork",
    "UnknownRarity.bound_quarter_lt",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (d : Gap), (d : ℝ) < 1/2 →
  ∀ (C : ℝ) (R : ℝ → Type) [∀ B, MeasurableSpace (R B)] (A : ∀ B, AdaptiveEstimator (R B)),
    (∀ B : ℝ, 1 ≤ B → ∀ (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1), θ ≤ 1/4 →
      ∀ᵐ z ∂experimentLaw (Measure.dirac d) (A B) (constantPrior θ hθ),
        ∃ n, (A B).policy z.1.1 (processHistory z.2 n) = none) →
    ¬ ∀ B : ℝ, 1 ≤ B → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1/4 →
      ∀ (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1), θ ≤ ρ →
        rootMeanRisk (experimentLaw (Measure.dirac d) (A B) (constantPrior θ hθ))
            (populationOutput (A B)) θ ≤
          ENNReal.ofReal (C * min ρ (Real.sqrt ρ / ((d : ℝ) * Real.sqrt B))) :=
  UnknownRarity.unknown_rarity_obstruction

example :
  ∀ (d : Gap), (d : ℝ) < 1/2 → ∀ (C B : ℝ), 4 * C^2 / (d : ℝ)^2 < B →
  ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ᵐ z ∂experimentLaw (Measure.dirac d) A (constantPrior (1/4) (by norm_num)),
        ∃ n, A.policy z.1.1 (processHistory z.2 n) = none) →
    ¬ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1/4 → ∀ (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1), θ ≤ ρ →
        rootMeanRisk (experimentLaw (Measure.dirac d) A (constantPrior θ hθ))
            (populationOutput A) θ ≤
          ENNReal.ofReal (C * min ρ (Real.sqrt ρ / ((d : ℝ) * Real.sqrt B))) :=
  UnknownRarity.fixed_budget_obstruction

example :
  ∀ (d : Gap), (d : ℝ) < 1/2 →
  ∀ (C : ℝ) (R : ℝ → Type) [∀ B, MeasurableSpace (R B)] (A : ∀ B, AdaptiveEstimator (R B)),
    (∀ B : ℝ, 1 ≤ B → ∀ (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1), θ ≤ 1/4 →
      expectedWork (Measure.dirac d) (A B) (constantPrior θ hθ) < ∞) →
    ¬ ∀ B : ℝ, 1 ≤ B → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1/4 →
      ∀ (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1), θ ≤ ρ →
        rootMeanRisk (experimentLaw (Measure.dirac d) (A B) (constantPrior θ hθ))
            (populationOutput (A B)) θ ≤
          ENNReal.ofReal (C * min ρ (Real.sqrt ρ / ((d : ℝ) * Real.sqrt B))) :=
  UnknownRarity.expected_work_obstruction

example :
  ∀ (d : Gap), (d : ℝ) < 1/2 →
  ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R) (q v : SignLaw),
    (∀ᵐ z ∂experimentLaw (Measure.dirac d) A v,
        ∃ n, A.policy z.1.1 (processHistory z.2 n) = none) →
    (experimentLaw (Measure.dirac d) A v).map (fun z => (z.1.1, z.2)) ≪
      (experimentLaw (Measure.dirac d) A q).map (fun z => (z.1.1, z.2)) :=
  UnknownRarity.stopped_transcript_ac

example : ∀ {R : Type} [MeasurableSpace R] (g : Gap), (g : ℝ) < 1/2 →
    ∀ (A : AdaptiveEstimator R) (q v : SignLaw),
    (∀ᵐ z ∂experimentLaw (Measure.dirac g) A v,
      ∃ n, A.policy z.1.1 (processHistory z.2 n) = none) →
    ∀ (S : Set (R × ProcessTape)), MeasurableSet S →
    (∀ᵐ z ∂experimentLaw (Measure.dirac g) A q, (z.1.1, z.2) ∉ S) →
    ∀ᵐ z ∂experimentLaw (Measure.dirac g) A v, (z.1.1, z.2) ∉ S :=
  @UnknownRarity.dirac_null_transfer

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw), expectedWork μ A q < ∞ →
    ∀ᵐ z ∂experimentLaw μ A q, ∃ n, A.policy z.1.1 (processHistory z.2 n) = none :=
  @UnknownRarity.stops_of_expectedWork

example : ∀ (d C B : ℝ), 0 < d → 4 * C^2 / d^2 < B →
    ¬ ENNReal.ofReal (1/4) ≤
      ENNReal.ofReal (C * min (1/4) (Real.sqrt (1/4) / (d * Real.sqrt B))) :=
  UnknownRarity.bound_quarter_lt
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
        raise ValueError("Duplicate unknown-rarity declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing unknown-rarity target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed unknown-rarity specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.UnknownRarity",
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
    print(f"All {len(TARGETS)} unknown-rarity targets are certified")


if __name__ == "__main__":
    main()
