"""Audit explicit constants that frozen statements leave existential or prove only per algorithm.

* Theorem 2.1's hidden-model confidence coefficient 15/(256 sqrt 2), for each
  algorithm and for the minimax radius, with the upper constant 8192.
* The rare-event lower coefficient 1/256 for every gap law supported below a,
  for each algorithm and for the minimax risk.
* The single-coin second moment 28 rho of the observable rare-event estimator.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the five targets with their types written out, so a changed
   statement cannot pass under an old name;
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

GROUP = "ExplicitConstants"
NAMES = ("Specification", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "9cda691a16db1ebbfdf0cbb443f1e01266a61f9a2df1ad69dfc89423522414ce"
TARGETS = {
    "ExplicitConstants.hidden_confidence": "ExplicitConstants.HiddenConfidenceLowerStatement",
    "ExplicitConstants.hidden_confidence_minimax": "ExplicitConstants.HiddenConfidenceMinimaxStatement",
    "ExplicitConstants.rare_lower_256": "ExplicitConstants.RareSupportedLower256Statement",
    "ExplicitConstants.rare_minimax_256": "ExplicitConstants.RareSupportedMinimax256Statement",
    "ExplicitConstants.rare_single_coin_28": "ExplicitConstants.RareSingleCoin28Statement",
}
COMPONENTS = ()
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (B δ r : ℝ),
    1 ≤ B → 0 < δ → δ ≤ 1/4 → 0 ≤ r →
    UniformBudget μ A B → Confidence.UniformConfidence μ A r δ →
    (15/(256*Real.sqrt 2)) * modulus μ (Confidence.confidenceScale B δ) ≤ r :=
  ExplicitConstants.hidden_confidence

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B δ : ℝ),
    1 ≤ B → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal ((15/(256*Real.sqrt 2)) * modulus μ (Confidence.confidenceScale B δ)) ≤
        Confidence.minimaxConfidenceRadius μ B δ ∧
      Confidence.minimaxConfidenceRadius μ B δ ≤
        ENNReal.ofReal (8192 * modulus μ (Confidence.confidenceScale B δ)) :=
  ExplicitConstants.hidden_confidence_minimax

example : ∀ a ρ B : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 1 ≤ B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], (∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a) →
    ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R), RareBudget μ A ρ B →
      ENNReal.ofReal ((1/256) * aboveTwoRate a ρ B) ≤ rareRisk μ A ρ :=
  ExplicitConstants.rare_lower_256

example : ∀ a ρ B : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 1 ≤ B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], (∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a) →
      ENNReal.ofReal ((1/256) * aboveTwoRate a ρ B) ≤ rareMinimaxRisk μ ρ B :=
  ExplicitConstants.rare_minimax_256

example : ∃ single : ℝ → ℝ → AdaptiveEstimator ℕ,
    (∀ a ρ j xs, (single a ρ).policy j xs = none ∨ (single a ρ).policy j xs = some 0) ∧
    ∀ α : ℝ, 2 < α → ∃ W : ℝ, 0 < W ∧
    ∀ a ρ : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], PowerMargin μ α a →
    ∀ q : SignLaw, RarePrior μ ρ q →
      Integrable (populationOutput (single a ρ)) (experimentLaw μ (single a ρ) q) ∧
      (∫ z, populationOutput (single a ρ) z ∂experimentLaw μ (single a ρ) q) = signMean μ q.val ∧
      (∫⁻ z, ENNReal.ofReal ((populationOutput (single a ρ) z)^2)
        ∂experimentLaw μ (single a ρ) q) ≤ ENNReal.ofReal (28*ρ) ∧
      expectedWork μ (single a ρ) q ≤ ENNReal.ofReal (W/a^2) :=
  ExplicitConstants.rare_single_coin_28
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
        raise ValueError("Duplicate explicit-constant declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing explicit-constant target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed explicit-constant specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.RareAboveTwo",
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
    print(f"All {len(TARGETS)} explicit-constant targets are certified")


if __name__ == "__main__":
    main()
