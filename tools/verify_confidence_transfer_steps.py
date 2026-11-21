"""Audit the residual steps of the confidence-transfer note.

The note research/2026-10-30-confidence-transfer/NOTE.md derives two
confidence-radius bounds with a written proof only: its equation (17), the
lower bound r_exp(B, delta) >= Psi(sqrt(log(1/delta)/B))/8192 for every gap
law, and its equation (22), r(B, delta) of order
min(rho, sqrt(rho log(1/delta))/(a sqrt B)) for an exact power law with
exponent alpha > 2, under either budget convention, with the remark that one
hard-cap procedure, fixed before the law, serves the whole power-margin
class. The group checks all three, with the universal lower constant 1/8192
and an existential upper constant per alpha.

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

GROUP = "ConfidenceTransferSteps"
NAMES = ("Specification", "Lower", "Upper", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "5e3b299d1439900685b52af31289d864ab0d65627fbe01b9eddfb21631338321"
TARGETS = {
    "ConfidenceTransferSteps.psi_confidence_null": "ConfidenceTransferSteps.PsiConfidenceNullStatement",
    "ConfidenceTransferSteps.above_two_confidence_family": "ConfidenceTransferSteps.AboveTwoConfidenceFamilyStatement",
    "ConfidenceTransferSteps.above_two_confidence": "ConfidenceTransferSteps.AboveTwoConfidenceStatement",
}
COMPONENTS = (
    "ConfidenceTransferSteps.exact_power_confidence_lower",
    "ConfidenceTransferSteps.confidence_resolution_rate",
    "ConfidenceTransferSteps.aboveTwoRate_confidence",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
      ENNReal.ofReal (1/8192) * rarePsi μ ρ (ThresholdHC.Confidence.confidenceScale B δ) ≤
        ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ :=
  ConfidenceTransferSteps.psi_confidence_null

example :
  ∀ α : ℝ, 2 < α → ∃ C : ℝ, 0 < C ∧
    ∀ a ρ B δ : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      ThresholdHC.HardBudget.PathwiseCap A ⌊B⌋₊ ∧
      ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
        RareBudget ν A ρ B ∧ ∀ q : SignLaw, RarePrior ν ρ q →
          ThresholdHC.Confidence.failureProbability ν A q
            (C * min ρ (Real.sqrt (ρ * Real.log (1/δ)) / (a * Real.sqrt B))) ≤ ENNReal.ofReal δ :=
  ConfidenceTransferSteps.above_two_confidence_family

example :
  ∀ α : ℝ, 2 < α → ∃ C : ℝ, 0 < C ∧
    ∀ a ρ B δ : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ExactPowerLaw μ α a →
      let z := min ρ (Real.sqrt (ρ * Real.log (1/δ)) / (a * Real.sqrt B))
      ENNReal.ofReal (z/8192) ≤ ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ∧
      ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ≤
        ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ∧
      ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ≤ ENNReal.ofReal (C*z) :=
  ConfidenceTransferSteps.above_two_confidence

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ B δ : ℝ},
    0 < a → 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 → ExactPowerLaw μ α a →
    ENNReal.ofReal (min ρ (Real.sqrt (ρ * Real.log (1/δ)) / (a * Real.sqrt B)) / 8192) ≤
      ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ :=
  @ConfidenceTransferSteps.exact_power_confidence_lower

example : ∀ {a ρ B δ : ℝ}, 0 ≤ ρ → 0 < B → 0 < δ → δ ≤ 1/4 →
    ThresholdHC.Confidence.confidenceScale B δ * Real.sqrt ρ / a =
      Real.sqrt (ρ * Real.log (1/δ)) / (a * Real.sqrt B) :=
  @ConfidenceTransferSteps.confidence_resolution_rate

example : ∀ {a ρ B δ : ℝ}, 0 ≤ ρ → 0 < B → 0 < δ → δ ≤ 1/4 →
    aboveTwoRate a ρ (B/Real.log (1/δ)) =
      min ρ (Real.sqrt (ρ * Real.log (1/δ)) / (a * Real.sqrt B)) :=
  @ConfidenceTransferSteps.aboveTwoRate_confidence
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
        raise ValueError("Duplicate confidence-transfer-steps declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing confidence-transfer-steps target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed confidence-transfer-steps specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.ConfidenceTransferSteps",
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
    print(f"All {len(TARGETS)} confidence-transfer-steps targets are certified")


if __name__ == "__main__":
    main()
