"""Audit the pilot events (A8) and (A11) under the law of the whole learning stage.

Displays (A8) and (A11) of docs/ARBITRARY_LAW_ADAPTATION.md, (UA8) and (UA11)
of paper/v6/arbitrary-law-adaptation.tex, describe the capped multi-depth
pilot of the paid learning stage: with m >= 8 log(2J/eps) probes per depth,
with probability at least 1 - eps the certificates satisfy
F(2^-j) <= U_j <= 128(u_j + W_j/b_j + 1/M) at every depth j <= J, the learned
law dominates the gap law, and on the same event its selection functional is
at most 2^24 times the oracle's for every J >= J_0(mu, rho). The audited
library stated these events on the coin array of the original simulation
law. The group states them under the original hidden-gap experiment of the
whole stage, reading the certificates off the paid chronological prefix of
the observed history, with (A11) on the full event (A8) and the onset J_0
chosen before the seed type, the sign law, the stage, m and eps.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the three targets and three components with their types written out;
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

GROUP = "StagePilotLaw"
NAMES = ("Specification", "Transfer", "CoinEvent", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "6f5ee851b6e688fbef4988ac3128643d2aa660040359947fe52a111ff11d4fd7"
TARGETS = {
    "StagePilotLaw.stage_pilot_event": "StagePilotLaw.StagePilotEventStatement",
    "StagePilotLaw.stage_pilot_oracle": "StagePilotLaw.StagePilotOracleStatement",
    "StagePilotLaw.stage_pilot_oracle_eventually": "StagePilotLaw.StagePilotOracleEventuallyStatement",
}
COMPONENTS = (
    "StagePilotLaw.pilot_prefix_tape_real",
    "StagePilotLaw.original_pilotStage_oracle_event",
    "StagePilotLaw.measurable_pilot_prefix",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (S : LearnedStage R) (J m : ℕ) (ρ ε : ℝ),
    0 < ρ → 1 ≤ J → 0 < m → 0 < ε → 8 * Real.log (2 * (J : ℝ) / ε) ≤ m →
    1 - ε ≤ (experimentLaw μ ((pilotStage S J m ρ).endpoint false) q).real
      {z | (∀ i, i < J →
          μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
            (pilotStage S J m ρ).upper ((processHistory z.2 (pilotStage S J m ρ).cap).take
              (pilotStage S J m ρ).pilotCost) i ∧
          (pilotStage S J m ρ).upper ((processHistory z.2 (pilotStage S J m ρ).cap).take
              (pilotStage S J m ρ).pilotCost) i ≤ pilotBound μ J ρ (i + 1)) ∧
        ∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
          (pilotStage S J m ρ).learnedLaw ((processHistory z.2 (pilotStage S J m ρ).cap).take
            (pilotStage S J m ρ).pilotCost) (Set.Iic x)} :=
  StagePilotLaw.stage_pilot_event

example :
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (S : LearnedStage R) (J m : ℕ) (ρ ε : ℝ),
    0 < ρ → ρ ≤ 1 / 4 → 1 ≤ J → PilotOnset μ ρ J → 0 < m → 0 < ε →
    8 * Real.log (2 * (J : ℝ) / ε) ≤ m →
    1 - ε ≤ (experimentLaw μ ((pilotStage S J m ρ).endpoint false) q).real
      {z | (∀ i, i < J →
          μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
            (pilotStage S J m ρ).upper ((processHistory z.2 (pilotStage S J m ρ).cap).take
              (pilotStage S J m ρ).pilotCost) i ∧
          (pilotStage S J m ρ).upper ((processHistory z.2 (pilotStage S J m ρ).cap).take
              (pilotStage S J m ρ).pilotCost) i ≤ pilotBound μ J ρ (i + 1)) ∧
        (∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
          (pilotStage S J m ρ).learnedLaw ((processHistory z.2 (pilotStage S J m ρ).cap).take
            (pilotStage S J m ρ).pilotCost) (Set.Iic x)) ∧
        zeroSelection ((pilotStage S J m ρ).learnedLaw ((processHistory z.2
            (pilotStage S J m ρ).cap).take (pilotStage S J m ρ).pilotCost)) ρ (4 ^ J) ≤
          16777216 * EntropyTail.selection μ ρ (4 ^ J)} :=
  StagePilotLaw.stage_pilot_oracle

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ), 0 < ρ → ρ ≤ 1 / 4 →
    ∃ J₀ : ℕ, 1 ≤ J₀ ∧ ∀ (R : Type) [MeasurableSpace R] (q : SignLaw) (S : LearnedStage R)
      (J m : ℕ) (ε : ℝ), J₀ ≤ J → 0 < m → 0 < ε → 8 * Real.log (2 * (J : ℝ) / ε) ≤ m →
      1 - ε ≤ (experimentLaw μ ((pilotStage S J m ρ).endpoint false) q).real
        {z | (∀ i, i < J →
            μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
              (pilotStage S J m ρ).upper ((processHistory z.2 (pilotStage S J m ρ).cap).take
                (pilotStage S J m ρ).pilotCost) i ∧
            (pilotStage S J m ρ).upper ((processHistory z.2 (pilotStage S J m ρ).cap).take
                (pilotStage S J m ρ).pilotCost) i ≤ pilotBound μ J ρ (i + 1)) ∧
          (∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
            (pilotStage S J m ρ).learnedLaw ((processHistory z.2 (pilotStage S J m ρ).cap).take
              (pilotStage S J m ρ).pilotCost) (Set.Iic x)) ∧
          zeroSelection ((pilotStage S J m ρ).learnedLaw ((processHistory z.2
              (pilotStage S J m ρ).cap).take (pilotStage S J m ρ).pilotCost)) ρ (4 ^ J) ≤
            16777216 * EntropyTail.selection μ ρ (4 ^ J)} :=
  StagePilotLaw.stage_pilot_oracle_eventually

example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (μ : Measure Gap)
    [IsProbabilityMeasure μ] (q : SignLaw) (good : List Bool → Prop),
    (experimentLaw μ (S.endpoint false) q).real
        {z | good ((processHistory z.2 S.cap).take S.pilotCost)} =
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {s | good (readBlock S.pilotCost S.pilot (s ∘ Nat.pair 0)).1} :=
  @StagePilotLaw.pilot_prefix_tape_real

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (S : LearnedStage R) (J m : ℕ) {ρ ε : ℝ}, 0 < ρ → ρ ≤ 1 / 4 → 1 ≤ J →
    PilotOnset μ ρ J → 0 < m → 0 < ε → 8 * Real.log (2 * (J : ℝ) / ε) ≤ m →
    1 - ε ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {ω | (∀ i, i < J →
            μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
              (pilotStage S J m ρ).upper (pilotStageWord J m ρ ω) i ∧
            (pilotStage S J m ρ).upper (pilotStageWord J m ρ ω) i ≤
              pilotBound μ J ρ (i + 1)) ∧
          (∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
            (pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω) (Set.Iic x)) ∧
          zeroSelection ((pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω)) ρ (4 ^ J) ≤
            16777216 * EntropyTail.selection μ ρ (4 ^ J)} :=
  @StagePilotLaw.original_pilotStage_oracle_event

example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R),
    Measurable (fun w : R × ProcessTape => (processHistory w.2 S.cap).take S.pilotCost) :=
  @StagePilotLaw.measurable_pilot_prefix
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
        raise ValueError("Duplicate stage-pilot-law declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing stage-pilot-law target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed stage-pilot-law specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation ThresholdHC.HardBudget ThresholdHC.BlindUpper ThresholdHC.StagePilotLaw",
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
    print(f"All {len(TARGETS)} stage-pilot-law targets are certified")


if __name__ == "__main__":
    main()
