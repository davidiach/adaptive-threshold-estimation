"""Audit Corollary 14.14 and Remark 14.15 of v6 (the critical window).

The uniform power-law theorem of `PowerWindow` gives the minimax risk of every
exact power law within universal factors of the rate (W7). On the window
3/2 <= alpha <= 3 the corollary simplifies that rate to min{rho, Y}, within the
factor 5.13, and derives display (W9) with the paper's constants 10^-18 and
3.4*10^5, the bounds on Psi, and the ratio of the risk to Psi when Y <= rho.
The remark identifies the quadratic law with the rate of the critical theorem
and reads off the regimes away from and near exponent two; near two the risk
behaves like that of the quadratic law.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification, whose twelve statements use only the definitions of
   `PowerWindow`, the rare-event minimax risk, the variational modulus and the
   critical log factor;
3. restates the twelve targets and five component theorems with their types
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

GROUP = "CriticalWindow"
NAMES = ("Specification", "Rate", "Measures", "Remark", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "b37967496af9c8618c95c6d4d5e61cb3e08c0e9f8a96022c81e2f3178d848193"
TARGETS = {
    "CriticalWindow.critical_window_rate": "CriticalWindow.WindowRateStatement",
    "CriticalWindow.critical_window_risk": "CriticalWindow.WindowRiskStatement",
    "CriticalWindow.critical_window_psi": "CriticalWindow.WindowPsiStatement",
    "CriticalWindow.critical_window_ratio": "CriticalWindow.WindowRatioStatement",
    "CriticalWindow.window_quadratic_rate": "CriticalWindow.QuadraticWindowStatement",
    "CriticalWindow.window_quadratic_risk": "CriticalWindow.QuadraticRiskStatement",
    "CriticalWindow.window_away_scales": "CriticalWindow.AwayScalesStatement",
    "CriticalWindow.window_away_phi": "CriticalWindow.AwayPhiStatement",
    "CriticalWindow.window_away_risk": "CriticalWindow.AwayRiskStatement",
    "CriticalWindow.window_near_two": "CriticalWindow.NearTwoStatement",
    "CriticalWindow.window_quadratic_scales": "CriticalWindow.QuadraticScalesStatement",
    "CriticalWindow.window_near_two_risk": "CriticalWindow.NearTwoRiskStatement",
}
COMPONENTS = (
    "CriticalWindow.rho_phi_lower", "CriticalWindow.power_tail_upper",
    "CriticalWindow.window_rate_bounds", "CriticalWindow.power_quantileZero",
    "CriticalWindow.away_rate_bounds",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∀ (α ρ x : ℝ), 3/2 ≤ α → α ≤ 3 → 0 < ρ → ρ ≤ 1/4 → 0 < x →
    let Y := x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ)))
    min ρ Y ≤ uniformRate α x ρ ∧ uniformRate α x ρ ≤ 513/100 * min ρ Y :=
  CriticalWindow.critical_window_rate

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    3/2 ≤ α → α ≤ 3 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    let Y := 1 / (a * Real.sqrt B) *
      Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ)))
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 * min ρ Y) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (340000 * min ρ Y) :=
  CriticalWindow.critical_window_risk

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    3/2 ≤ α → α ≤ 3 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    let Y₀ := 1 / (a * Real.sqrt B) * Real.sqrt (ρ * powerPhi α ρ)
    ENNReal.ofReal (min ρ Y₀ / Real.sqrt 2) ≤ rarePsi μ ρ (1 / Real.sqrt B) ∧
    rarePsi μ ρ (1 / Real.sqrt B) ≤ ENNReal.ofReal (513/100 * min ρ Y₀) :=
  CriticalWindow.critical_window_psi

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    3/2 ≤ α → α ≤ 3 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    1 / (a * Real.sqrt B) *
      Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) ≤ ρ →
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 19 * Real.sqrt (1 + Real.log (effectiveScales α ρ))) *
        rarePsi μ ρ (1 / Real.sqrt B) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤
      ENNReal.ofReal (500000 * Real.sqrt (1 + Real.log (effectiveScales α ρ))) *
        rarePsi μ ρ (1 / Real.sqrt B) :=
  CriticalWindow.critical_window_ratio

example : ∀ (ρ B : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B →
    powerPhi 2 ρ = Real.log (1/ρ) ∧
    effectiveScales 2 ρ = 1 + Real.logb 2 (1/ρ) / 2 ∧
    2 * Real.sqrt (ρ * CriticalEntropy.criticalLogFactor ρ / B) ≤
      1 / ((1/4) * Real.sqrt B) *
        Real.sqrt (ρ * powerPhi 2 ρ * (1 + Real.log (effectiveScales 2 ρ))) ∧
    1 / ((1/4) * Real.sqrt B) *
        Real.sqrt (ρ * powerPhi 2 ρ * (1 + Real.log (effectiveScales 2 ρ))) ≤
      4 * Real.sqrt (ρ * CriticalEntropy.criticalLogFactor ρ / B) :=
  CriticalWindow.window_quadratic_rate

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ 2 (1/4) →
    let C := Real.sqrt (ρ * CriticalEntropy.criticalLogFactor ρ / B)
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 * min ρ C) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (1360000 * min ρ C) :=
  CriticalWindow.window_quadratic_risk

example : ∀ (α ρ : ℝ), 3/2 ≤ α → α ≤ 3 → α ≠ 2 → 0 < ρ → ρ ≤ 1/4 →
    1 ≤ |1 - 2/α| * Real.log (1/ρ) →
    effectiveScales α ρ = 1 / |α - 2| :=
  CriticalWindow.window_away_scales

example : ∀ (α ρ : ℝ), 3/2 ≤ α → α ≤ 3 → 0 < ρ → ρ ≤ 1/4 →
    1 ≤ |1 - 2/α| * Real.log (1/ρ) →
    (2 < α → (1 - Real.exp (-1)) * (α / (α - 2)) ≤ powerPhi α ρ ∧
      powerPhi α ρ ≤ α / (α - 2)) ∧
    (α < 2 → (1 - Real.exp (-1)) * (α * ρ ^ (1 - 2/α) / (2 - α)) ≤ powerPhi α ρ ∧
      powerPhi α ρ ≤ α * ρ ^ (1 - 2/α) / (2 - α)) :=
  CriticalWindow.window_away_phi

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    3/2 ≤ α → α ≤ 3 → α ≠ 2 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ExactPowerLaw μ α a → 1 ≤ |1 - 2/α| * Real.log (1/ρ) →
    let Z := 1 / (a * Real.sqrt B) * ρ ^ (min (1/2) (1 - 1/α)) *
      Real.sqrt ((1 + Real.log (1 / |α - 2|)) / |α - 2|)
    ENNReal.ofReal (5 * (10 : ℝ)⁻¹ ^ 19 * min ρ Z) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (700000 * min ρ Z) :=
  CriticalWindow.window_away_risk

example : ∀ (α ρ : ℝ), 3/2 ≤ α → α ≤ 3 → 0 < ρ → ρ ≤ 1/4 →
    |α - 2| * Real.log (1/ρ) ≤ 1 →
    Real.log (1/ρ) / 2 ≤ powerPhi α ρ ∧ powerPhi α ρ ≤ 2 * Real.log (1/ρ) ∧
    Real.log (1/ρ) / 3 ≤ effectiveScales α ρ ∧ effectiveScales α ρ ≤ 2 * Real.log (1/ρ) :=
  CriticalWindow.window_near_two

example : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1/4 →
    (1 + Real.log (1/ρ)) / 2 ≤ powerPhi 2 ρ ∧ powerPhi 2 ρ ≤ 1 + Real.log (1/ρ) ∧
    effectiveScales 2 ρ ≤ 1 + Real.log (1/ρ) ∧ 1 + Real.log (1/ρ) ≤ effectiveScales 2 ρ ^ 2 :=
  CriticalWindow.window_quadratic_scales

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    3/2 ≤ α → α ≤ 3 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    |α - 2| * Real.log (1/ρ) ≤ 1 →
    let Z := 1 / (a * Real.sqrt B) * Real.sqrt (ρ * CriticalEntropy.criticalLogFactor ρ)
    ENNReal.ofReal (2 * (10 : ℝ)⁻¹ ^ 19 * min ρ Z) ≤ rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (700000 * min ρ Z) :=
  CriticalWindow.window_near_two_risk

example : ∀ {α ρ : ℝ}, 3/2 ≤ α → α ≤ 3 → 0 < ρ → ρ ≤ 1/4 →
    (53/100 : ℝ) * ρ ^ (2 - 2/α) ≤ ρ * powerPhi α ρ :=
  @CriticalWindow.rho_phi_lower

example : ∀ {α x ρ : ℝ}, 3/2 ≤ α → 0 < ρ → 0 < x →
    powerTail α x ρ ≤ 3 * x * ρ ^ (1 - 1/α) :=
  @CriticalWindow.power_tail_upper

example : ∀ {α ρ x K : ℝ}, 3/2 ≤ α → α ≤ 3 → 0 < ρ → ρ ≤ 1/4 → 0 < x → 1 ≤ K →
    min ρ (x * Real.sqrt (ρ * powerPhi α ρ * K)) ≤ CriticalWindow.windowRate α x ρ K ∧
    CriticalWindow.windowRate α x ρ K ≤
      (513/100) * min ρ (x * Real.sqrt (ρ * powerPhi α ρ * K)) :=
  @CriticalWindow.window_rate_bounds

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ B : ℝ},
    0 < α → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    PsiClosedForm.quantileZero μ ρ B =
      ENNReal.ofReal (CriticalWindow.windowRate α (1 / (a * Real.sqrt B)) ρ 1) :=
  @CriticalWindow.power_quantileZero

example : ∀ {α ρ x : ℝ}, 3/2 ≤ α → α ≤ 3 → α ≠ 2 → 0 < ρ → ρ ≤ 1/4 → 0 < x →
    1 ≤ |1 - 2/α| * Real.log (1/ρ) →
    x * ρ ^ (min (1/2) (1 - 1/α)) * Real.sqrt ((1 + Real.log (1 / |α - 2|)) / |α - 2|) / 2 ≤
      x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) ∧
    x * Real.sqrt (ρ * powerPhi α ρ * (1 + Real.log (effectiveScales α ρ))) ≤
      2 * (x * ρ ^ (min (1/2) (1 - 1/α)) *
        Real.sqrt ((1 + Real.log (1 / |α - 2|)) / |α - 2|)) :=
  @CriticalWindow.away_rate_bounds
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
        raise ValueError("Duplicate critical-window declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing critical-window target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed critical-window statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PowerWindow",
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
    print("All twelve critical-window target statements are certified")


if __name__ == "__main__":
    main()
