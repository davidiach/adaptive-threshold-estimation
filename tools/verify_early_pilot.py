"""Audit the early-stopping pilot of the arbitrary-law adaptation.

The learning stage of the arbitrary-law controller buys a capped multi-depth
pilot whose probes stop as soon as their certificate is decided; the paper
remarks that this early stopping saves work on easy laws. The group builds
such a pilot as one adaptive estimator per index (an early-pilot family with
the full pilot's certificates on table paths), proves that one exists,
transfers the pilot event (A8) to the original experiment, bounds its expected
work by the probes' capped work envelopes, and for laws with every gap at
least a bounds it by 512 m M J (J + 3)/a^2, a vanishing fraction of the cap at
a depth that does not depend on the law. The event and work statements are
conditional on the predicate, which the existence statement inhabits. The
early pilot is not installed in the learning stage.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the five targets and three components with their types written out;
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

GROUP = "EarlyPilot"
NAMES = ("Specification", "VarReader", "ProbeStop", "Estimator", "Law", "Easy", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "1894436e2edfd95e1cb1a433bf53ce2b8716ed13585791a601a3a78ffde303e5"
TARGETS = {
    "EarlyPilot.early_pilot_exists": "EarlyPilot.EarlyPilotExistsStatement",
    "EarlyPilot.early_pilot_event": "EarlyPilot.EarlyPilotEventStatement",
    "EarlyPilot.early_pilot_work": "EarlyPilot.EarlyPilotWorkStatement",
    "EarlyPilot.easy_law_work": "EarlyPilot.EasyLawWorkStatement",
    "EarlyPilot.easy_law_vanishing": "EarlyPilot.EasyLawVanishingStatement",
}
COMPONENTS = (
    "EarlyPilot.probeFlips_le_min",
    "EarlyPilot.sum_range_add_two",
    "EarlyPilot.pilotCoinCap_le",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (J m : ℕ) (ρ : ℝ), 0 < ρ → 0 < m → ∃ A : ℕ → AdaptiveEstimator Unit, IsEarlyPilot J m ρ A :=
  EarlyPilot.early_pilot_exists

example :
  ∀ (J m : ℕ) (ρ : ℝ) (A : ℕ → AdaptiveEstimator Unit), IsEarlyPilot J m ρ A →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (i₀ : ℕ) (ε : ℝ),
      0 < ρ → 1 ≤ J → 0 < m → 0 < ε → 8 * Real.log (2 * (J : ℝ) / ε) ≤ m →
      1 - ε ≤ (experimentLaw μ (A i₀) q).real
        {z | ∀ i, i < J →
          μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤ (A i).output (z.1.1, z.2) ∧
          (A i).output (z.1.1, z.2) ≤ pilotBound μ J ρ (i + 1)} :=
  EarlyPilot.early_pilot_event

example :
  ∀ (J m : ℕ) (ρ : ℝ) (A : ℕ → AdaptiveEstimator Unit), IsEarlyPilot J m ρ A →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (i : ℕ),
      expectedWork μ (A i) q ≤ ENNReal.ofReal ((m : ℝ) * ∑ j ∈ Finset.range J,
        min (pilotBudget J (j + 1) : ℝ)
          ((pilotCoinCap J ρ : ℝ) * ∫ d : Gap, tailWorkEnvelope (j + 1) d ∂μ)) :=
  EarlyPilot.early_pilot_work

example :
  ∀ (J m : ℕ) (ρ : ℝ) (A : ℕ → AdaptiveEstimator Unit), IsEarlyPilot J m ρ A →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (i : ℕ) (a : ℝ),
      0 < a → (∀ᵐ d : Gap ∂μ, a ≤ (d : ℝ)) →
      expectedWork μ (A i) q ≤
        ENNReal.ofReal (512 * m * pilotCoinCap J ρ * J * (J + 3) / a ^ 2) :=
  EarlyPilot.easy_law_work

example :
  ∀ (a ρ ε : ℝ), 0 < a → 0 < ρ → 0 < ε → ∃ J₀ : ℕ,
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], (∀ᵐ d : Gap ∂μ, a ≤ (d : ℝ)) →
    ∀ (J m : ℕ) (A : ℕ → AdaptiveEstimator Unit), J₀ ≤ J → IsEarlyPilot J m ρ A →
      ∀ (q : SignLaw) (i : ℕ), expectedWork μ (A i) q ≤ ENNReal.ofReal (ε * pilotCost J m) :=
  EarlyPilot.easy_law_vanishing

example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool), probeFlips J b M ω ≤ min b (probeWork J ω M) :=
  EarlyPilot.probeFlips_le_min

example : ∀ (J : ℕ), ∑ j ∈ Finset.range J, ((j : ℝ) + 1 + 1) = (J : ℝ) * (J + 3) / 2 :=
  EarlyPilot.sum_range_add_two

example : ∀ (J : ℕ) {ρ : ℝ}, 0 < ρ → (pilotCoinCap J ρ : ℝ) ≤ (Real.sqrt (64 / ρ) + 1) * 2 ^ J :=
  @EarlyPilot.pilotCoinCap_le
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
        raise ValueError("Duplicate early-pilot declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing early-pilot target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed early-pilot specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EarlyPilot",
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
    print(f"All {len(TARGETS)} early-pilot targets are certified")


if __name__ == "__main__":
    main()
