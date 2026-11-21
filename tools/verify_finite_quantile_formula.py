"""Audit the explicit quantile formula for finite laws.

Section 14.2 of the v6 manuscript (displays (67)-(69): fg:eq:quantile-split,
fg:eq:core-entropy and fg:eq:closed-functional): for a finite law with gaps
d_1 < ... < d_n and weights w_i, the quantile tail and core are the atoms with
masses tau_i = min{w_i, (rho - sum_{l<i} w_l)_+} and w_i - tau_i, and the
closed quantile functional is min{rho, T + h sqrt(rho Gamma)} with the
explicit tail sum T and core entropy Gamma, h = B^{-1/2}. With it the direct
finite-law theorem fg:thm:direct-main holds with Q(B) given by the formula:
10^-20 Q <= R <= 30001 Q, one estimator attaining the upper bound and every
budgeted estimator obeying the lower one. The upper half comes from the
general-law route, not the direct finite construction of the finite-upper
appendix; the constant bookkeeping of Appendix E is not part of this group.

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

GROUP = "FiniteQuantileFormula"
NAMES = ("Specification", "Atoms", "Split", "Formula", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "53c97142e893b8e1dfafdcc92405d65da3bdf4b37e06169574d7670bae62b13f"
TARGETS = {
    "FiniteQuantileFormula.finite_formula": "FiniteQuantileFormula.FiniteFormulaStatement",
    "FiniteQuantileFormula.explicit_finite_law": "FiniteQuantileFormula.ExplicitFiniteLawStatement",
}
COMPONENTS = (
    "FiniteQuantileFormula.coreGamma_eq_costEntropy",
    "FiniteQuantileFormula.coreGamma_nonneg",
    "FiniteQuantileFormula.tailSum_nonneg",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (n : ℕ) (d : Fin n → Gap) (w : Fin n → ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ],
    StrictMono (fun i => (d i : ℝ)) → (∀ i, 0 < w i) → ∑ i, w i = 1 →
    μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) →
    ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → ∀ N : ℕ, (∀ i, bandEdge N < (d i : ℝ)) →
      quantileTail μ ρ = ∑ i, ENNReal.ofReal (tailWeight w ρ i) • Measure.dirac (d i) ∧
      quantileCore μ ρ = ∑ i, ENNReal.ofReal (w i - tailWeight w ρ i) • Measure.dirac (d i) ∧
      closedQuantileValue μ ρ B = ENNReal.ofReal (finiteQuantile d w ρ B N) :=
  FiniteQuantileFormula.finite_formula

example :
  ∀ (n : ℕ) (d : Fin n → Gap) (w : Fin n → ℝ) (μ : Measure Gap) [IsProbabilityMeasure μ],
    StrictMono (fun i => (d i : ℝ)) → (∀ i, 0 < w i) → ∑ i, w i = 1 →
    μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) →
    ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → ∀ N : ℕ, (∀ i, bandEdge N < (d i : ℝ)) →
      ENNReal.ofReal ((10:ℝ)⁻¹^20 * finiteQuantile d w ρ B N) ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (30001 * finiteQuantile d w ρ B N) ∧
      (∃ (S : Type) (_ : MeasurableSpace S) (A : AdaptiveEstimator S), RareBudget μ A ρ B ∧
        rareRisk μ A ρ ≤ ENNReal.ofReal (30001 * finiteQuantile d w ρ B N)) ∧
      (∀ (S : Type) [MeasurableSpace S] (A : AdaptiveEstimator S), RareBudget μ A ρ B →
        ENNReal.ofReal ((10:ℝ)⁻¹^20 * finiteQuantile d w ρ B N) ≤ rareRisk μ A ρ) :=
  FiniteQuantileFormula.explicit_finite_law

example : ∀ {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℝ) (ρ : ℝ) (N : ℕ),
    coreGamma d w ρ N = costEntropy (fun j : Fin N => finiteCoreCost d w ρ j) :=
  @FiniteQuantileFormula.coreGamma_eq_costEntropy

example : ∀ {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℝ) (ρ : ℝ) (N : ℕ),
    0 ≤ coreGamma d w ρ N :=
  @FiniteQuantileFormula.coreGamma_nonneg

example : ∀ {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℝ), (∀ i, 0 ≤ w i) → ∀ (ρ : ℝ)
    {h : ℝ}, 0 ≤ h → 0 ≤ tailSum d w ρ h :=
  @FiniteQuantileFormula.tailSum_nonneg
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
        raise ValueError("Duplicate finite-quantile-formula declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing finite-quantile-formula target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed finite-quantile-formula specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open scoped Classical open ThresholdHC ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile ThresholdHC.FiniteQuantileFormula",
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
    print(f"All {len(TARGETS)} finite-quantile-formula targets are certified")


if __name__ == "__main__":
    main()
