"""Audit the factor 3 sqrt(7)/2 between the infinite stopping program and risk.

The rms-constants review (research/2026-11-17-rms-constants) states that the
infinite stopping program satisfies R <= P_inf <= (3 sqrt 7 / 2) R, so with a
cap N >= 4B/9 the finite program gives R <= P_N <= 3 sqrt 7 R < 8 R, and any
feasible upper bound U and genie lower bound L with U <= 2L give the same
factor for U. The checked factor was 8. The proof replaces the fixed-weight
absorption of the factor-8 route by an endpoint weight chosen from the
information price.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the four targets and three components with their types written out;
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

GROUP = "ProgramFactor"
NAMES = ("Specification", "Absorption", "Population", "Modulus", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "dc4c41bad547925a1a1ad45c67134fc739b8a6acdd62a9b7c79eb450b052e9ca"
TARGETS = {
    "ProgramFactor.infinite_program_factor": "ProgramFactor.InfiniteProgramFactorStatement",
    "ProgramFactor.four_ninths_factor": "ProgramFactor.FourNinthsFactorStatement",
    "ProgramFactor.genie_test_factor": "ProgramFactor.GenieTestFactorStatement",
    "ProgramFactor.below_eight": "ProgramFactor.BelowEightStatement",
}
COMPONENTS = (
    "ProgramFactor.weighted_stopped_hellinger_work",
    "ProgramFactor.weight_choice",
    "ProgramFactor.rareMinimaxRisk_pos_lt_top",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ infiniteProgramValue μ ρ B ∧
    infiniteProgramValue μ ρ B ≤ ENNReal.ofReal (3 * Real.sqrt 7 / 2) * rareMinimaxRisk μ ρ B :=
  ProgramFactor.infinite_program_factor

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B → ∀ N : ℕ, 4 * B / 9 ≤ N →
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
    programValue μ ρ B N ≤ ENNReal.ofReal (3 * Real.sqrt 7) * rareMinimaxRisk μ ρ B :=
  ProgramFactor.four_ninths_factor

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B → ∀ N : ℕ, 0 < N → ∀ U L : ℝ≥0∞,
    programValue μ ρ B N ≤ U → L ≤ genieValue μ ρ B N → U ≤ 2 * L →
    rareMinimaxRisk μ ρ B ≤ U ∧
    U ≤ ENNReal.ofReal (3 * Real.sqrt 7) * rareMinimaxRisk μ ρ B :=
  ProgramFactor.genie_test_factor

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    ENNReal.ofReal (3 * Real.sqrt 7) * rareMinimaxRisk μ ρ B < 8 * rareMinimaxRisk μ ρ B :=
  ProgramFactor.below_eight

example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (Q : FourPriors) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1), a < 1 →
    ∀ (A : StoppedProcedure R E) (N : ℕ), 0 < N → informationRatio μ N Q ≠ ⊤ →
    (∀ z, A.stop z ≤ N) →
    stoppedHellinger μ ν (weightedLow Q a ha) (weightedHigh Q a ha) A N ≤
      (a^2/(2*(1-a)^2)*(informationRatio μ N Q).toReal)*
        (populationExpectedWork μ ν (gapParameter false) (gapParameter true)
          (signUnit (StoppingProgram.midpointPrior (weightedLow Q a ha) (weightedHigh Q a ha))) A).toReal :=
  @ProgramFactor.weighted_stopped_hellinger_work

example : ∀ (x : ℝ), 0 ≤ x →
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      2/(3*Real.sqrt 7)*(1/Real.sqrt (4+x)) ≤ a/2*(1-a^2/(2*(1-a)^2)*x) :=
  @ProgramFactor.weight_choice

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    0 < rareMinimaxRisk μ ρ B ∧ rareMinimaxRisk μ ρ B < ⊤ :=
  @ProgramFactor.rareMinimaxRisk_pos_lt_top
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
        raise ValueError("Duplicate program-factor declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing program-factor target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed program-factor specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie ThresholdHC.RareAboveTwo ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.ProgramFactor",
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
    print(f"All {len(TARGETS)} program-factor targets are certified")


if __name__ == "__main__":
    main()
