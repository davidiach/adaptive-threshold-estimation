"""Audit the rows of the power-margin table through the closed quantile form.

Remark rem:power-quantile of the v6 rare-event section (The power-margin
regimes): for the exact power law F(d) = (d/a)^alpha each row of the RMS table
(alpha < 1, alpha = 1, 1 < alpha < 2, alpha = 2, alpha > 2) also follows, with
constants depending on alpha, from the comparison of the minimax risk with the
closed quantile functional Q. The group proves that the uniform rate (W7), Q
and the rare-event minimax risk are each within alpha-dependent factors of the
row, and identifies the alpha = 2 row at a = 1/4 with the table entry. For
alpha > 4 the quantile and risk statements rest on a Lean-only extension of
Theorem 14.13, whose paper statement covers 0 < alpha <= 4.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the four targets and three components with their types written out;
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

GROUP = "PowerQuantileRows"
NAMES = ("Specification", "AllExponents", "Bounds", "Rows", "Bridges", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "55912163131668442306d0f56f38aca64234f1a85b92b8066166572d815f3834"
TARGETS = {
    "PowerQuantileRows.power_row_rate": "PowerQuantileRows.PowerRowRateStatement",
    "PowerQuantileRows.power_row_quantile": "PowerQuantileRows.PowerRowQuantileStatement",
    "PowerQuantileRows.power_row_risk": "PowerQuantileRows.PowerRowRiskStatement",
    "PowerQuantileRows.quadratic_row_form": "PowerQuantileRows.QuadraticRowFormStatement",
}
COMPONENTS = (
    "PowerQuantileRows.power_quantile_all",
    "PowerQuantileRows.powerRow_eq_linearRate",
    "PowerQuantileRows.powerRow_eq_aboveTwoRate",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ α : ℝ, 0 < α → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ ρ x : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < x →
      c * powerRow α x ρ ≤ uniformRate α x ρ ∧ uniformRate α x ρ ≤ C * powerRow α x ρ :=
  PowerQuantileRows.power_row_rate

example :
  ∀ α : ℝ, 0 < α → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (a ρ B : ℝ),
      0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
      ENNReal.ofReal (c * powerRow α (1 / (a * Real.sqrt B)) ρ) ≤ closedQuantileValue μ ρ B ∧
      closedQuantileValue μ ρ B ≤ ENNReal.ofReal (C * powerRow α (1 / (a * Real.sqrt B)) ρ) :=
  PowerQuantileRows.power_row_quantile

example :
  ∀ α : ℝ, 0 < α → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (a ρ B : ℝ),
      0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
      ENNReal.ofReal (c * powerRow α (1 / (a * Real.sqrt B)) ρ) ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (C * powerRow α (1 / (a * Real.sqrt B)) ρ) :=
  PowerQuantileRows.power_row_risk

example :
  ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    powerRow 2 (1 / ((1/4) * Real.sqrt B)) ρ =
      min ρ (4 * Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ / B)) :=
  PowerQuantileRows.quadratic_row_form

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ B : ℝ},
    0 < α → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    ENNReal.ofReal (uniformRate α (1 / (a * Real.sqrt B)) ρ / Real.sqrt 2) ≤
      closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (2 * uniformRate α (1 / (a * Real.sqrt B)) ρ) :=
  @PowerQuantileRows.power_quantile_all

example : ∀ (x ρ : ℝ), powerRow 1 x ρ = ThresholdHC.ShiftedPower.linearRate ρ x :=
  PowerQuantileRows.powerRow_eq_linearRate

example : ∀ {α : ℝ}, 2 < α → ∀ (a ρ B : ℝ),
    powerRow α (1 / (a * Real.sqrt B)) ρ = ThresholdHC.RareAboveTwo.aboveTwoRate a ρ B :=
  @PowerQuantileRows.powerRow_eq_aboveTwoRate
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
        raise ValueError("Duplicate power-quantile-rows declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing power-quantile-rows target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed power-quantile-rows specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PowerWindow ThresholdHC.EntropyTailQuantile ThresholdHC.PowerQuantileRows",
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
    print(f"All {len(TARGETS)} power-quantile-rows targets are certified")


if __name__ == "__main__":
    main()
