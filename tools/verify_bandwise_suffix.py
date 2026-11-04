"""Kernel-check the finite-law suffix optimizer and the bound on its finite search family."""
import json
import subprocess

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, sha, strip_comments, validate_dependency_freeze, validate_reports,
)
from verify_entropy_tail import FREEZE, FROZEN, ROOT
from verify_entropy_tail_components import LEAN, dependency_order

PREFIX = "ThresholdHC.BandwiseSuffix."
SOURCE = LEAN / "ThresholdHC/BandwiseSuffix"
SPEC_SHA256 = "e1ea3f7e38a3dea09bfab1d5df07b278a12d284ccc4a1ddd46cdf65640fb1206"


def audit_input(module="Search"):
    if sha(SOURCE / "Specification.lean") != SPEC_SHA256:
        raise ValueError("Changed suffix optimizer statement from a2ee4e8")
    freeze = json.loads(FREEZE.read_text(encoding="utf-8"))
    if freeze["source_sha256"] != FROZEN or any(sha(ROOT / p) != h for p, h in FROZEN.items()):
        raise ValueError("Changed original entropy-tail specification")
    validate_dependency_freeze(LEAN / "ThresholdHC/EntropyTail/Specification.lean", freeze)
    closure = dependency_order([SOURCE / (module + ".lean")])
    paths = {p for p in closure if p.parent == SOURCE}
    if module == "Search" and paths != set(SOURCE.rglob("*.lean")):
        raise ValueError("Unregistered bandwise-suffix module")
    roots = set()
    for path in closure:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in {path}")
        if path in paths:
            for name in DECLARATION.findall(source):
                if PREFIX + name in roots:
                    raise ValueError(f"Duplicate suffix declaration {name}")
                roots.add(PREFIX + name)
    checks = [f"import {PREFIX}{module}", "open MeasureTheory ThresholdHC.Tier6 ThresholdHC.EntropyTail",
              "open ThresholdHC.BandwiseSuffix", "open scoped ENNReal BigOperators"]
    if SOURCE / "Attainment.lean" in paths:
        checks.append(
            "example (μ : Measure Gap) [IsProbabilityMeasure μ] (hs : μ.support.Finite) "
            "{ρ B : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ 1/4) (hb : 0 < B) : "
            "∃ S : Finset Gap, (S : Set Gap) ⊆ μ.support ∧ ∀ σ : Measure Gap, σ ≤ μ → "
            "selectionObjective μ ρ B (μ.restrict S) ≤ selectionObjective μ ρ B σ := "
            "exists_optimal_hard μ hs hρ hr hb"
        )
    if SOURCE / "Exchange.lean" in paths:
        checks.append(
            "example (μ : Measure Gap) [IsProbabilityMeasure μ] (S : Finset Gap) {ρ B : ℝ} "
            "(hb : 0 < B) {j : ℕ} {x y : Gap} (hlt : x < y) (hx : x ∈ S) (hy : y ∉ S) "
            "(hxj : x ∈ band j) (hyj : y ∈ band j) (hxm : 0 < μ {x}) (hym : 0 < μ {y}) "
            "(hf : selectionObjective μ ρ B (μ.restrict S) ≠ ⊤) : ∃ τ : Measure Gap, τ ≤ μ ∧ "
            "selectionObjective μ ρ B τ < selectionObjective μ ρ B (μ.restrict S) := "
            "improve_inversion μ S hb hlt hx hy hxj hyj hxm hym hf"
        )
    if SOURCE / "Full.lean" in paths:
        checks.append("example : BandwiseSuffixStatement := bandwise_suffix")
    if module == "Search":
        checks += [
            "example (F : Finset Gap) : (suffixChoices F).card ≤ "
            "∏ j ∈ F.image bandIndex, ((slice F j).card + 1) := suffixChoices_card_le F",
            "example (μ : Measure Gap) [IsProbabilityMeasure μ] (hs : μ.support.Finite) "
            "{ρ B : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ 1/4) (hB : 0 < B) : "
            "∃ S ∈ suffixChoices hs.toFinset, ∀ σ : Measure Gap, σ ≤ μ → "
            "selectionObjective μ ρ B (μ.restrict S) ≤ selectionObjective μ ρ B σ := "
            "search_attains μ hs hρ hr hB",
        ]
    return "\n".join(checks + ["#print axioms " + name for name in sorted(roots)]) + "\n", roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", PREFIX + "Search"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], input=source, cwd=LEAN,
                         text=True, capture_output=True, encoding="utf-8")
    report = run.stdout + run.stderr
    print(report, end="")
    validate_reports(report, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
