"""Audit the upper constant 27 of the RMS law.

One budget-indexed family, chosen before the gap law, keeps the uniform
expected-work budget and has RMS risk at most 27 times the modulus at every
budget of at least one; hence the minimax RMS risk is at most 27 times the
modulus. The dyadic family of `BlindUpper` runs the calibrated batch at the
level 2^L with 4*2^L <= B < 8*2^L and leaves up to half the budget unused. This
family tosses a coin first and runs level L+1 with probability
p = B/(4*2^L) - 1, so its expected work is at most B. The work and squared
risk of the mixture are the same mixtures of those of the two levels, whose
mean-square error is bounded by `UpperMoment`. The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification, whose two statements use only the original
   experiment, budget, risk and modulus definitions;
3. restates the two targets and six component theorems with their types
   written out, so a changed statement cannot pass under an old name;
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

PREFIX = "ThresholdHC.UpperMixture."
SOURCES = LEAN / "ThresholdHC/UpperMixture"
MODULES = ("Specification", "Mixture", "Full")
SPEC_HASH = "7a17d40ff5d9cd8685ec95a56d3c311f51e6442eb9e556af2c32082c90e74e3f"
TARGETS = {
    "blind_upper_27": "BlindUpper27Statement",
    "minimax_upper_27": "MinimaxUpper27Statement",
}
COMPONENTS = (
    "mix_expectedWork", "mix_squaredRisk", "modulus_sq_scale", "batch_squaredRisk_le",
    "budgetMixture_uniformBudget", "budgetMixture_maximalRMSRisk",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (27*modulus μ (1/Real.sqrt B)) :=
  UpperMixture.blind_upper_27

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    minimaxRisk μ B ≤ ENNReal.ofReal (27*modulus μ (1/Real.sqrt B)) :=
  UpperMixture.minimax_upper_27

example : ∀ {R : Type} [MeasurableSpace R] (p : ℝ) (A₀ A₁ : AdaptiveEstimator R),
    A₁.randomLaw = A₀.randomLaw → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    expectedWork μ (UpperMixture.mixEstimator p A₀ A₁) q =
      ENNReal.ofReal (UpperMixture.clip p) * expectedWork μ A₁ q +
        ENNReal.ofReal (1 - UpperMixture.clip p) * expectedWork μ A₀ q :=
  @UpperMixture.mix_expectedWork

example : ∀ {R : Type} [MeasurableSpace R] (p : ℝ) (A₀ A₁ : AdaptiveEstimator R),
    A₁.randomLaw = A₀.randomLaw → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (a : ℝ),
    squaredRisk (experimentLaw μ (UpperMixture.mixEstimator p A₀ A₁) q)
        (populationOutput (UpperMixture.mixEstimator p A₀ A₁)) a =
      ENNReal.ofReal (UpperMixture.clip p) *
          squaredRisk (experimentLaw μ A₁ q) (populationOutput A₁) a +
        ENNReal.ofReal (1 - UpperMixture.clip p) *
          squaredRisk (experimentLaw μ A₀ q) (populationOutput A₀) a :=
  @UpperMixture.mix_squaredRisk

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N B : ℝ), 0 < N → N ≤ B →
    N * (modulus μ (1 / Real.sqrt N)) ^ 2 ≤ B * (modulus μ (1 / Real.sqrt B)) ^ 2 :=
  @UpperMixture.modulus_sq_scale

example : ∀ (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    squaredRisk (experimentLaw μ (BlindUpper.batchEstimator L) q)
        (populationOutput (BlindUpper.batchEstimator L)) (signMean μ q.val) ≤
      ENNReal.ofReal ((19781/125) * (modulus μ (1 / Real.sqrt ((2 : ℝ) ^ L))) ^ 2) :=
  @UpperMixture.batch_squaredRisk_le

example : ∀ (B : ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ],
    UniformBudget μ (UpperMixture.budgetMixture B) B :=
  @UpperMixture.budgetMixture_uniformBudget

example : ∀ (B : ℝ), 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    maximalRMSRisk μ (UpperMixture.budgetMixture B) ≤
      ENNReal.ofReal (27 * modulus μ (1 / Real.sqrt B)) :=
  @UpperMixture.budgetMixture_maximalRMSRisk
"""


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES) or len(MODULES) != len(set(MODULES)):
        raise ValueError("Unregistered or missing upper-mixture module")
    roots: list[str] = []
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in UpperMixture/{name}.lean")
        roots.extend(public_names(source, f"UpperMixture/{name}.lean"))
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate upper-mixture declaration")
    required = {PREFIX + name for pair in TARGETS.items() for name in pair}
    required |= {PREFIX + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing upper-mixture target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed upper-mixture statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import {PREFIX}{name}" for name in MODULES],
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6",
        *[f"example : UpperMixture.{statement} := UpperMixture.{theorem}"
          for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?UpperMixture\.{re.escape(name)}\n", EXACT)) != 1:
            raise ValueError("Each target and component needs exactly one restated statement")
    return source, roots


def replay_modules() -> list[str]:
    return [PREFIX + name for name in MODULES]


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
        print(f"Replayed {len(MODULES)} modules through the independent kernel checker")
    print("Both upper-mixture target statements are certified")


if __name__ == "__main__":
    main()
