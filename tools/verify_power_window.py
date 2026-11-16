"""Audit the power-law quantile split and inverse-square cost identity.

This is a foundation audit, not a proof of the uniform entropy or statistical
targets. PowerCoreStatement (which includes entropy), PowerQuantileStatement,
PowerRiskStatement and PowerConfidenceStatement remain unproved specifications.
"""
import subprocess

from verify_blind_upper_components import (
    FORBIDDEN, LEAN, registered_names, sha, strip_comments, validate_reports,
)

PREFIX = "ThresholdHC.PowerWindow."
SOURCES = LEAN / "ThresholdHC/PowerWindow"
MODULES = ("Specification", "Phi", "Law", "CoreCost", "Full")
SPEC_HASH = "924c8032dbabaaabddec452d35e2bb0aa68781c7201517ed6cf47dd8d5445a06"
TARGETS = {"power_phi_closed": "PowerPhiStatement"}
PENDING = ("PowerCoreStatement", "PowerQuantileStatement", "PowerRiskStatement",
           "PowerConfidenceStatement")
EXACT_COUNT = 6

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
    required = {name for pair in TARGETS.items() for name in pair} | set(PENDING) | {
        "power_core_cost", "power_quantile_tail", "power_quantile_core", "quadratic_core_cost"}
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
    print("Unproved targets (not certified by this audit): " + ", ".join(PENDING))


if __name__ == "__main__":
    main()
