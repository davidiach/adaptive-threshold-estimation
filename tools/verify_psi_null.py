"""Audit Proposition prop:psi-null and its corollary eq:psi-budget-lower.

Proposition prop:psi-null of the v6 transfer appendix bounds the null-work
obstruction: for every probability law of gaps, 0 < rho <= 1/4, 0 <= b <= rho/64
and h > 0, every capped observable procedure with bounded output, extended
variance at most V and bias at most b on the capped prior class X_rho has
V * W_0 >= (Psi(h) - 4b)_+^2 / (192 h^2), where W_0 is its expected work at the
all-negative population. The corollary eq:psi-budget-lower is
R(B) >= Psi(B^(-1/2)) / 8192 for every budget B > 0.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the two targets and four components with their types written out;
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

GROUP = "PsiNull"
NAMES = ("Specification", "StoppedKL", "OneSided", "Response", "Population", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "67373606ecb7ec418c7dfd7f45cce54f600df52db133028259eb10de332bdff1"
TARGETS = {
    "PsiNull.psi_null": "PsiNull.PsiNullStatement",
    "PsiNull.psi_budget_lower": "PsiNull.PsiBudgetLowerStatement",
}
COMPONENTS = (
    "PsiNull.psi_objective_bound",
    "PsiNull.gap_response_bound",
    "PsiNull.capped_transcript_kl",
    "PsiNull.kl_mean_one_sided",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ b h : ℝ), 0 < ρ → ρ ≤ 1/4 →
    0 ≤ b → b ≤ ρ/64 → 0 < h →
    NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b
      ((max ((rarePsi μ ρ h).toReal - 4*b) 0)^2 / (192*h^2)) :=
  PsiNull.psi_null

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ENNReal.ofReal (1/8192) * rarePsi μ ρ (1 / Real.sqrt B) ≤ rareMinimaxRisk μ ρ B :=
  PsiNull.psi_budget_lower

example :
  ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (A : StoppedProcedure R ℝ) (m : ℕ), (∀ z, A.stop z ≤ m) →
    ∀ {C : ℝ}, (∀ z, |A.output z| ≤ C) →
    ∀ {ρ b V h : ℝ}, 0 < ρ → ρ ≤ 1/4 → b ≤ ρ/64 → 0 ≤ h → 0 ≤ V →
    (∀ q : Gap → unitInterval, CappedPrior μ ρ q →
      evariance (A.output ∘ populationInput (gapParameter false) (gapParameter true) q)
        (populationMeasure μ ν) ≤ ENNReal.ofReal V) →
    (∀ q : Gap → unitInterval, CappedPrior μ ρ q →
      |populationMean μ ν (gapParameter false) (gapParameter true) q A -
        (∫ d, (q d : ℝ) ∂μ)| ≤ b) →
    ∀ {v : Gap → ℝ}, Tier3.FeasibleAllocation μ ρ v →
    Tier3.rareObjective μ (fun d => (d : ℝ)) h v ≤
      4*b + h * Real.sqrt (192 * V * (populationExpectedWork μ ν (gapParameter false)
        (gapParameter true) (fun _ => 0) A).toReal) :=
  @PsiNull.psi_objective_bound

example :
  ∀ {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ) (m : ℕ),
    (∀ z, A.stop z ≤ m) → ∀ (C : ℝ), (∀ z, |A.output z| ≤ C) → ∀ (d : Gap),
    (conditionalMean ν (gapParameter true d) A -
        conditionalMean ν (gapParameter false d) A)^2 ≤
      64 * (d : ℝ)^2 * (expectedStoppedProcedureWork ν (gapParameter false d) A).toReal *
        ((conditionalSecondMoment ν (gapParameter false d) A).toReal +
          (conditionalSecondMoment ν (gapParameter true d) A).toReal) :=
  @PsiNull.gap_response_bound

example :
  ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E) (m : ℕ),
    (∀ z, A.stop z ≤ m) → ∀ (p q : unitInterval), 0 < (p : ℝ) → (p : ℝ) < 1 →
    0 < (q : ℝ) → (q : ℝ) < 1 →
    klDiv ((ν.prod (Tier2.tapeMeasure p)).map (cappedTranscript A m))
      ((ν.prod (Tier2.tapeMeasure q)).map (cappedTranscript A m)) =
      ENNReal.ofReal ((expectedStoppedProcedureWork ν p A).toReal * klB p q) :=
  @PsiNull.capped_transcript_kl

example :
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {f : Ω → ℝ}, MemLp f 2 P → MemLp f 2 Q → klDiv P Q ≠ ∞ →
    ((∫ x, f x ∂P) - (∫ x, f x ∂Q))^2 ≤
      2 * (klDiv P Q).toReal * ((∫ x, f x ^ 2 ∂P) + (∫ x, f x ^ 2 ∂Q)) :=
  @PsiNull.kl_mean_one_sided
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
        raise ValueError("Duplicate psi-null declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing psi-null target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed psi-null specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open InformationTheory ThresholdHC ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ConfidenceLocalization ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo ThresholdHC.PsiNull",
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
    print(f"All {len(TARGETS)} psi-null targets are certified")


if __name__ == "__main__":
    main()
