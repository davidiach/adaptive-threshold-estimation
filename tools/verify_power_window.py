"""Audit the uniform power-law entropy, quantile, RMS and confidence bounds.

The critical-window corollary and asymptotic reading remain outside this scope.
"""
import subprocess

from verify_blind_upper_components import (
    FORBIDDEN, LEAN, registered_names, sha, strip_comments, validate_reports,
)

PREFIX = "ThresholdHC.PowerWindow."
SOURCES = LEAN / "ThresholdHC/PowerWindow"
MODULES = ("Specification", "Phi", "Law", "CoreCost", "Statistics", "TailIntegral",
           "Quantile", "FiniteEntropy", "LogMoments", "EntropyBounds", "DensityBounds",
           "WindowBands", "CoreCoordinates", "BandCost", "CoreEntropy", "Full")
SPEC_HASH = "924c8032dbabaaabddec452d35e2bb0aa68781c7201517ed6cf47dd8d5445a06"
TARGETS = {"power_phi_closed": "PowerPhiStatement", "power_core": "PowerCoreStatement",
           "power_quantile": "PowerQuantileStatement", "power_risk": "PowerRiskStatement",
           "power_confidence": "PowerConfidenceStatement"}
EXACT_COUNT = 16

EXACT = """
example (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (α * ∫ s in (ρ ^ (1/α))..1, s ^ (α - 3)) =
      if α = 2 then Real.log (1/ρ) else α * (1 - ρ ^ (1 - 2/α)) / (α - 2) :=
  power_phi_closed α ρ hα hρ hρ1

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ : ℝ)
    (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    quantileTail μ ρ =
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).restrict (Set.Iic ρ)).map
        (powerQuantile α a hα ha ha2) :=
  power_quantile_tail μ hα ha ha2 hρ hρ1 hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ : ℝ)
    (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    quantileCore μ ρ = (volume.restrict (Set.Ioc ρ 1)).map
      (powerQuantile α a hα ha ha2) :=
  power_quantile_core μ hα ha ha2 hρ hρ1 hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ : ℝ)
    (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    a^2 * (∫⁻ d : Gap, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal =
      α * ∫ s in (ρ ^ (1/α))..1, s ^ (α - 3) :=
  power_core_cost μ hα ha ha2 hρ hρ1 hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (a ρ : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^(2 : ℝ))) :
    a^2 * (∫⁻ d : Gap, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal =
      Real.log (1/ρ) :=
  quadratic_core_cost μ ha ha2 hρ hρ1 hm

example (hQ : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    0 < α → α ≤ 4 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    ENNReal.ofReal (uniformRate α (1 / (a * Real.sqrt B)) ρ / Real.sqrt 2) ≤
      closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (2 * uniformRate α (1 / (a * Real.sqrt B)) ρ))
    (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ)
    (hα : 0 < α) (hα4 : α ≤ 4) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hm : ExactPowerLaw μ α a) :
    ENNReal.ofReal ((10 : ℝ)⁻¹^17 / Real.sqrt 2 * uniformRate α (1 / (a * Real.sqrt B)) ρ) ≤
      rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (60002 * uniformRate α (1 / (a * Real.sqrt B)) ρ) :=
  power_risk_of_quantile hQ μ α a ρ B hα hα4 ha ha2 hρ hρ4 hB hm

example (hQ : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    0 < α → α ≤ 4 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    ENNReal.ofReal (uniformRate α (1 / (a * Real.sqrt B)) ρ / Real.sqrt 2) ≤
      closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (2 * uniformRate α (1 / (a * Real.sqrt B)) ρ))
    (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B δ : ℝ)
    (hα : 0 < α) (hα4 : α ≤ 4) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hδ : 0 < δ) (hδ4 : δ ≤ 1/4)
    (hm : ExactPowerLaw μ α a) :
    let x := Real.sqrt (Real.log (1 / δ) / B) / a
    ENNReal.ofReal ((10 : ℝ)⁻¹^17 / Real.sqrt 2 * uniformRate α x ρ) ≤
      ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ∧
    ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ≤
      ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ∧
    ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ≤
      ENNReal.ofReal (1500000 * uniformRate α x ρ) :=
  power_confidence_of_quantile hQ μ α a ρ B δ hα hα4 ha ha2 hρ hρ4 hB hδ hδ4 hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ : ℝ)
    (hα : 0 < α) (hα4 : α ≤ 4) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    a^2 * (∫⁻ d : Gap, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal =
        powerPhi α ρ ∧
    (1/2 : ℝ) * (1 + Real.log (effectiveScales α ρ)) ≤ 1 + ThresholdHC.PsiGap.coreEntropy μ ρ ∧
    1 + ThresholdHC.PsiGap.coreEntropy μ ρ ≤ (383/100 : ℝ) * (1 + Real.log (effectiveScales α ρ)) :=
  power_core μ α a ρ hα hα4 ha ha2 hρ hρ1 hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ)
    (hα : 0 < α) (hα4 : α ≤ 4) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    ENNReal.ofReal (uniformRate α (1 / (a * Real.sqrt B)) ρ / Real.sqrt 2) ≤
      closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (2 * uniformRate α (1 / (a * Real.sqrt B)) ρ) :=
  power_quantile μ α a ρ B hα hα4 ha ha2 hρ hρ4 hB hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ)
    (hα : 0 < α) (hα4 : α ≤ 4) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    ENNReal.ofReal ((10 : ℝ)⁻¹^17 / Real.sqrt 2 * uniformRate α (1 / (a * Real.sqrt B)) ρ) ≤
      rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (60002 * uniformRate α (1 / (a * Real.sqrt B)) ρ) :=
  power_risk μ α a ρ B hα hα4 ha ha2 hρ hρ4 hB hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B δ : ℝ)
    (hα : 0 < α) (hα4 : α ≤ 4) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hδ : 0 < δ) (hδ4 : δ ≤ 1/4)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    let x := Real.sqrt (Real.log (1 / δ) / B) / a
    ENNReal.ofReal ((10 : ℝ)⁻¹^17 / Real.sqrt 2 * uniformRate α x ρ) ≤
      ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ∧
    ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ≤
      ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ∧
    ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ≤
      ENNReal.ofReal (1500000 * uniformRate α x ρ) :=
  power_confidence μ α a ρ B δ hα hα4 ha ha2 hρ hρ4 hB hδ hδ4 hm
"""


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES):
        raise ValueError("Unregistered or missing power-window module")
    roots = set()
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in PowerWindow/{name}.lean")
        roots.update(PREFIX + declaration for declaration in registered_names(source))
    required = {name for pair in TARGETS.items() for name in pair} | {
        "power_core_cost", "power_quantile_tail", "power_quantile_core", "quadratic_core_cost",
        "power_risk_of_quantile", "power_confidence_of_quantile"}
    missing = {PREFIX + name for name in required} - roots
    if missing:
        raise ValueError("Missing power-window target: " + ", ".join(sorted(missing)))
    return roots


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed power-window statement")
    roots = declared_roots()
    source = "\n".join([
        "import ThresholdHC.PowerWindow.Full",
        "open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PowerWindow",
        "open ThresholdHC.EntropyTailQuantile",
        "open scoped ENNReal",
        *[f"example : {statement} := {theorem}" for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    return source, roots


def main() -> None:
    source, roots = audit_input()
    subprocess.run(["lake", "build", PREFIX + "Full"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {EXACT_COUNT} exact statements and {len(roots)} transitive axiom reports")
    print("All five frozen power-window target statements are certified")


if __name__ == "__main__":
    main()
