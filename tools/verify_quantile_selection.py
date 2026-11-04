"""Check Lemmas 1–2 and Theorem 4 against the independently committed comparison statements."""
import subprocess

from verify_blind_upper_components import DECLARATION, FORBIDDEN, sha, strip_comments, validate_reports
from verify_entropy_tail_components import LEAN, dependency_order, validate_sources as validate_model
from verify_quantile_comparison import validate_sources as validate_scalar

PREFIX = "ThresholdHC.QuantileSelection."
SOURCE = LEAN / "ThresholdHC/QuantileSelection"
TARGETS = {
    "Interaction": ("entropy_interaction", "InteractionStatement"),
    "SeparatedCost": ("separated_cost", "SeparatedCostStatement"),
    "Full": ("quantile_selection_comparison", "ComparisonStatement"),
}
SPEC_SHA256 = "98a1053482176d3212ad86944313d4b90641ef20204b78ae2a93b17a12f81e98"


def audit_input(modules):
    if sha(SOURCE / "Specification.lean") != SPEC_SHA256:
        raise ValueError("Changed comparison specification from 952803d")
    validate_model()
    validate_scalar()
    closure = dependency_order([SOURCE / (m + ".lean") for m in modules])
    paths = {p for p in closure if p.parent == SOURCE}
    if "Full" in modules and paths != set(SOURCE.rglob("*.lean")):
        raise ValueError("Unregistered comparison module")
    roots = set()
    for path in closure:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in {path}")
        if path in paths:
            for name in DECLARATION.findall(source):
                if PREFIX + name in roots:
                    raise ValueError(f"Duplicate comparison declaration {name}")
                roots.add(PREFIX + name)
    exact = [f"example : {PREFIX}{TARGETS[m][1]} := {PREFIX}{TARGETS[m][0]}" for m in modules]
    if "Full" in modules:
        exact.append(
            "example (μ : MeasureTheory.Measure ThresholdHC.Tier6.Gap) "
            "[MeasureTheory.IsProbabilityMeasure μ] {ρ B : ℝ} "
            "(hρ : 0 < ρ) (hr : ρ ≤ 1/4) (hb : 0 < B) : "
            "ThresholdHC.EntropyTail.selection μ ρ B ≤ ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ∧ "
            "ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ≤ ENNReal.ofReal (8/5) * "
            "ThresholdHC.EntropyTail.selection μ ρ B := "
            f"{PREFIX}locked_selection_comparison μ hρ hr hb"
        )
    commands = ([f"import {PREFIX}{m}" for m in modules] + exact
                + [f"#print axioms {name}" for name in sorted(roots)])
    return "\n".join(commands) + "\n", roots


def main():
    modules = list(TARGETS)
    source, roots = audit_input(modules)
    subprocess.run(["lake", "build", PREFIX + "Full"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    report = run.stdout + run.stderr
    print(report, end="")
    validate_reports(report, run.returncode, roots)
    print(f"Verified Lemmas 1 and 2, Theorem 4, its statistical-functional form and {len(roots)} axiom reports")


if __name__ == "__main__":
    main()
