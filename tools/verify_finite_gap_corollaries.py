"""Audit the two corollaries of the finite-gap manuscript.

* Corollary cor:one-gap: at a point mass the rare-event minimax risk lies
  between 10^-17 and 28000 times min{rho, sqrt(rho)/(d sqrt B)}. These are the
  constants of the explicit entropy-tail law; the manuscript's proof through
  its Theorem 1.1 gives weaker ones.
* Corollary cor:mse, first display: for every finitely supported law the
  squared minimax risk lies between c_0^2 and 2 C_0^2 times
  min{rho^2, T_h^2 + rho Gamma_kappa/B}, with c_0 = 10^-20 and C_0 = 30001.
* Corollary cor:mse, second display: if B >= d^-2 at every atom, the same
  holds with min{rho^2, (J_nu^2 + rho Gamma_kappa)/B}, J_nu = int d^-1 dnu.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the three targets and three components with their types written out;
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

GROUP = "FiniteGapCorollaries"
NAMES = ("Specification", "Corollaries", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "5b4719ced32684b37e6832f2e16c8bf56c237f14127397ffc3137815f3a667af"
TARGETS = {
    "FiniteGapCorollaries.one_gap_rate": "FiniteGapCorollaries.OneGapStatement",
    "FiniteGapCorollaries.mean_square_form": "FiniteGapCorollaries.MeanSquareStatement",
    "FiniteGapCorollaries.large_budget_mean_square_form":
        "FiniteGapCorollaries.LargeBudgetMeanSquareStatement",
}
COMPONENTS = (
    "FiniteGapCorollaries.closed_quantile_sq",
    "FiniteGapCorollaries.sq_add_le",
    "FiniteGapCorollaries.tail_linear",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∀ (d : Gap) (ρ B : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17 * aboveTwoRate (d : ℝ) ρ B) ≤
        rareMinimaxRisk (Measure.dirac d) ρ B ∧
      rareMinimaxRisk (Measure.dirac d) ρ B ≤ ENNReal.ofReal (28000 * aboveTwoRate (d : ℝ) ρ B) :=
  FiniteGapCorollaries.one_gap_rate

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ.support.Finite →
    ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    let M := min (ENNReal.ofReal ρ ^ 2)
      (ENNReal.ofReal (EntropyTailQuantile.tailModulus (EntropyTailQuantile.quantileTail μ ρ)
          (EntropyTailQuantile.budgetScale B)) ^ 2 +
        ENNReal.ofReal ρ * EntropyTailQuantile.measureCostEntropy
          (EntropyTailQuantile.quantileCore μ ρ) / ENNReal.ofReal B)
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) ^ 2 * M ≤ (rareMinimaxRisk μ ρ B) ^ 2 ∧
      (rareMinimaxRisk μ ρ B) ^ 2 ≤ 2 * 30001 ^ 2 * M :=
  FiniteGapCorollaries.mean_square_form

example : ∀ (μ : Measure Gap) (ρ B : ℝ), 0 < B →
    let M := min (ENNReal.ofReal ρ ^ 2)
      (ENNReal.ofReal (EntropyTailQuantile.tailModulus (EntropyTailQuantile.quantileTail μ ρ)
          (EntropyTailQuantile.budgetScale B)) ^ 2 +
        ENNReal.ofReal ρ * EntropyTailQuantile.measureCostEntropy
          (EntropyTailQuantile.quantileCore μ ρ) / ENNReal.ofReal B)
    M ≤ (EntropyTailQuantile.closedQuantileValue μ ρ B) ^ 2 ∧
      (EntropyTailQuantile.closedQuantileValue μ ρ B) ^ 2 ≤ 2 * M :=
  FiniteGapCorollaries.closed_quantile_sq

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ.support.Finite →
    ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → (∀ d ∈ μ.support, ((d : ℝ) ^ 2)⁻¹ ≤ B) →
    let J := ∫ d : Gap, (d : ℝ)⁻¹ ∂(EntropyTailQuantile.quantileTail μ ρ)
    let M := min (ENNReal.ofReal ρ ^ 2)
      ((ENNReal.ofReal J ^ 2 + ENNReal.ofReal ρ * EntropyTailQuantile.measureCostEntropy
          (EntropyTailQuantile.quantileCore μ ρ)) / ENNReal.ofReal B)
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 20) ^ 2 * M ≤ (rareMinimaxRisk μ ρ B) ^ 2 ∧
      (rareMinimaxRisk μ ρ B) ^ 2 ≤ 2 * 30001 ^ 2 * M :=
  FiniteGapCorollaries.large_budget_mean_square_form

example : ∀ (x y : ℝ≥0∞), (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) :=
  FiniteGapCorollaries.sq_add_le

example : ∀ (μ : Measure Gap) (ρ h : ℝ), (∀ d ∈ μ.support, h ≤ (d : ℝ)) →
    EntropyTailQuantile.tailModulus (EntropyTailQuantile.quantileTail μ ρ) h =
      h * ∫ d : Gap, (d : ℝ)⁻¹ ∂(EntropyTailQuantile.quantileTail μ ρ) :=
  FiniteGapCorollaries.tail_linear
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
        raise ValueError("Duplicate finite-gap declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing finite-gap target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed finite-gap specification")
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
    print(f"All {len(TARGETS)} finite-gap corollary targets are certified")


if __name__ == "__main__":
    main()
