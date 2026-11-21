"""Audit the per-coin creation fee of the v6 model paragraph.

The model paragraph of paper/v6/core.tex (sec:model) ends: every coin
actually created by the upper algorithm receives at least one observation,
and charging a fixed additional amount per new outer draw therefore changes
its cost by at most a constant factor. In the Lean model a coin is created
when its label is first selected. The group checks, for every adaptive
estimator, that created labels were selected at observed steps and number
at most the work (almost surely); that a fee c >= 0 per created coin keeps
the expected cost between the work and (1+c) times it; that the audited
distribution-blind constant-12 family keeps the charged budget (1+c)B; and,
beyond the source, that the charged minimax risk lies between the minimax
risks at budgets B and B/(1+c), with the rate
omega(B^-1/2)/6 <= R_c <= 12 sqrt(1+c) omega(B^-1/2) for B >= 1+c.

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

GROUP = "CreationCharge"
NAMES = ("Specification", "Count", "Charge", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "be9ad18ac6bc257270014facc5767e4a405ed913847d217ef13de50ce9c41d01"
TARGETS = {
    "CreationCharge.created_observed": "CreationCharge.CreatedObservedStatement",
    "CreationCharge.charged_work": "CreationCharge.ChargedWorkStatement",
    "CreationCharge.charged_blind_upper": "CreationCharge.ChargedBlindUpperStatement",
    "CreationCharge.charged_minimax": "CreationCharge.ChargedMinimaxStatement",
    "CreationCharge.charged_rate": "CreationCharge.ChargedRateStatement",
}
COMPONENTS = (
    "CreationCharge.totalCreated_le_of_valid",
    "CreationCharge.chargedBudget_of_budget",
    "CreationCharge.uniformBudget_of_charged",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw),
    ∀ᵐ z ∂experimentLaw μ A q,
      (∀ n : ℕ, ∀ i ∈ createdLabels (A.policy z.1.1) z.2 n,
        ∃ k < n, A.policy z.1.1 (processHistory z.2 k) = some i ∧ (z.2 k).isSome) ∧
      totalCreated (A.policy z.1.1) z.2 ≤ totalProcessWork z.2 :=
  CreationCharge.created_observed

example :
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (c : ℝ), 0 ≤ c →
    expectedWork μ A q ≤ chargedExpectedWork μ A q c ∧
    chargedExpectedWork μ A q c ≤ ENNReal.ofReal (1 + c) * expectedWork μ A q :=
  CreationCharge.charged_work

example :
  ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      (∀ c : ℝ, 0 ≤ c → ChargedUniformBudget μ (rule B) c ((1 + c) * B)) ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (12 * modulus μ (1 / Real.sqrt B)) :=
  CreationCharge.charged_blind_upper

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (c B : ℝ), 0 ≤ c →
    minimaxRisk μ B ≤ chargedMinimaxRisk μ c B ∧
    chargedMinimaxRisk μ c B ≤ minimaxRisk μ (B / (1 + c)) :=
  CreationCharge.charged_minimax

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (c B : ℝ), 0 ≤ c → 1 + c ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) ≤ chargedMinimaxRisk μ c B ∧
    chargedMinimaxRisk μ c B ≤
      ENNReal.ofReal (12 * Real.sqrt (1 + c) * modulus μ (1 / Real.sqrt B)) :=
  CreationCharge.charged_rate

example : ∀ (pol : List Bool → Option ℕ) (x : ProcessTape),
    (∀ k, (x k).isSome = (pol (processHistory x k)).isSome) →
    totalCreated pol x ≤ totalProcessWork x :=
  CreationCharge.totalCreated_le_of_valid

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) {c B : ℝ}, 0 ≤ c → UniformBudget μ A B →
    ChargedUniformBudget μ A c ((1 + c) * B) :=
  @CreationCharge.chargedBudget_of_budget

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) {c B : ℝ}, ChargedUniformBudget μ A c B → UniformBudget μ A B :=
  @CreationCharge.uniformBudget_of_charged
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
        raise ValueError("Duplicate creation-charge declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing creation-charge target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed creation-charge specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CreationCharge",
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
    print(f"All {len(TARGETS)} creation-charge targets are certified")


if __name__ == "__main__":
    main()
