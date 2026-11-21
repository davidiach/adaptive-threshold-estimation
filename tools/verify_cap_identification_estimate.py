"""Audit the explicit lower estimate after the fixed-cap identification theorem.

With L = ceil(N/2), V_L = span{d, d^3, ..., d^(2L-1)} in L^2(mu) and
h = 1 - proj_{V_L} 1: if 1 is not in V_L, then h is nonzero and bounded,
orthogonal to the odd monomials of V_L, int h dmu = int h^2 dmu > 0, and

    Delta_N / 2 >= rho ||h||^2_{L^2(mu)} / (4 ||h||_{L^inf(mu)}),

for every probability law of gaps, 0 < rho <= 1 and every cap N. The audited
fixed-cap identification theorem states positivity of Delta_N but not this
estimate.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the target and three components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker. The statement was written after the proof; it is
pinned from this audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "CapIdentificationEstimate"
NAMES = ("Specification", "Estimate", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "ba7fa5087af44a596be4887d8511961ed21f46391ed555c11865dbdb0e882d7f"
TARGETS = {
    "CapIdentificationEstimate.explicit_cap_estimate": "CapIdentificationEstimate.ExplicitCapEstimateStatement",
}
COMPONENTS = (
    "CapIdentificationEstimate.residual_integral_eq_norm_sq",
    "CapIdentificationEstimate.exists_bounded_representative",
    "CapIdentificationEstimate.exists_law_constant_not_mem",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ N : ℕ,
    polynomialL2 μ 1 ∉ oddL2Span μ ((N+1)/2) →
    let h : Lp ℝ 2 μ := polynomialL2 μ 1 -
      (oddL2Span μ ((N+1)/2)).starProjection (polynomialL2 μ 1)
    h ≠ 0 ∧ eLpNorm (⇑h) ∞ μ ≠ ∞ ∧ 0 < (eLpNorm (⇑h) ∞ μ).toReal ∧
      (∀ j : Fin ((N+1)/2), ∫ d, h d * (d : ℝ) ^ (2*j.val+1) ∂μ = 0) ∧
      (∫ d, h d ∂μ) = ∫ d, (h d) ^ 2 ∂μ ∧
      0 < ∫ d, (h d) ^ 2 ∂μ ∧
      ‖h‖ ^ 2 = ∫ d, (h d) ^ 2 ∂μ ∧
      ρ * ‖h‖ ^ 2 / (4 * (eLpNorm (⇑h) ∞ μ).toReal) ≤ capDiameter μ ρ N / 2 :=
  CapIdentificationEstimate.explicit_cap_estimate

example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (L : ℕ),
    ∫ d, (polynomialL2 μ 1 - (oddL2Span μ L).starProjection (polynomialL2 μ 1)) d ∂μ =
      ‖polynomialL2 μ 1 - (oddL2Span μ L).starProjection (polynomialL2 μ 1)‖ ^ 2 :=
  @CapIdentificationEstimate.residual_integral_eq_norm_sq

example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) (H : Polynomial ℝ),
    polynomialL2 μ H = f →
    ∃ g : Gap → ℝ, Measurable g ∧ (∀ d, |g d| ≤ (eLpNorm (⇑f) ∞ μ).toReal) ∧ g =ᵐ[μ] ⇑f :=
  @CapIdentificationEstimate.exists_bounded_representative

example : ∀ (L : ℕ), ∃ μ : ProbabilityMeasure Gap,
    polynomialL2 (μ : Measure Gap) 1 ∉ oddL2Span (μ : Measure Gap) L :=
  @CapIdentificationEstimate.exists_law_constant_not_mem
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
        raise ValueError("Duplicate fixed-cap estimate declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing fixed-cap estimate target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed fixed-cap estimate specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.CapIdentification",
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
    print("The fixed-cap estimate target is certified")


if __name__ == "__main__":
    main()
