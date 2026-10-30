"""Check entropy-tail upper ingredients, not the full statistical upper theorem.

The default rebuilds the entire local dependency closure. The explicit
--cached-dependencies checkpoint mode rebuilds the assembly modules and
audits all upper/assembly declaration axioms using existing dependency
objects. Both modes record every local dependency's source identity.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, sha, strip_comments, validate_reports,
)
from verify_entropy_tail_components import dependency_order, validate_sources

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
ASSEMBLY = LEAN / "ThresholdHC/EntropyTailAssembly"
UPPER = LEAN / "ThresholdHC/EntropyTailUpper"

# Independent type assertions spell out the actual kernels, finite-level
# certificate and truncation limit. No theorem's inferred type is reused.
EXACT_CHECKS = r"""
open MeasureTheory Filter Set Real
open scoped ENNReal Topology BigOperators
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.EntropyTailAssembly
example : ∀ (ξ : Measure Gap) [IsFiniteMeasure ξ] (K : ℕ),
    (∑ k ∈ Finset.range (K+1), sqrt (eta ξ (4^k)*ordinaryCost ξ (4^k))) ≤
      208*(∫ d : Gap, min ((2:ℝ)^K) (d:ℝ)⁻¹ ∂ξ) := dyadic_kernel_sum
example : ∀ (ξ : Measure Gap) [IsFiniteMeasure ξ],
    (∑' k : ℕ, ENNReal.ofReal (sqrt (eta ξ (4^k)*ordinaryCost ξ (4^k)))) ≤
      ENNReal.ofReal 208*(∫⁻ d : Gap, ENNReal.ofReal ((d:ℝ)⁻¹) ∂ξ) := dyadic_kernel_tsum_extended
example : ∀ (σ : Measure Gap) [IsFiniteMeasure σ], measureCostEntropy σ < ⊤ →
    Tendsto (fun n => ∫ d : Gap, (d:ℝ)⁻¹ ∂σ.restrict {d : Gap | (d:ℝ) < bandEdge n})
      atTop (𝓝 0) := selectedRemainder_inverse_tendsto
example : ∀ (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ],
    Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ → Integrable (fun d : Gap => (d:ℝ)⁻¹) τ →
    ∀ (ρ Γ z : ℝ) (hρ : 0 < ρ), 0 ≤ Γ → 0 ≤ z →
    (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) ≤ Γ → ρ/128 < (σ+τ).real univ →
    ∀ J : ℕ, z ≤ levelAccuracy ρ J/8 →
    (∑ l ∈ Finset.range (J+1), sqrt (17*levelAccuracy ρ l*
      adjacentCost (levelWorkCertificate σ τ ρ Γ z hρ) l)) ≤
      28000*(sqrt (ρ*Γ)+(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) :=
  fun σ τ _ _ hσ hτ ρ Γ z hρ hΓ hz hA hm J hzJ =>
    multilevel_budget_certificate σ τ hσ hτ hρ hΓ hz hA hm J hzJ
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--cached-dependencies", action="store_true")
    args = parser.parse_args()
    validate_sources()  # Retain the existing frozen model/specification checks.
    paths = sorted(UPPER.glob("*.lean")) + sorted(ASSEMBLY.glob("*.lean"))
    if not paths or not list(ASSEMBLY.glob("*.lean")):
        raise ValueError("Missing upper-construction sources")
    roots: set[str] = set()
    for path in paths:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + str(path))
        prefix = "ThresholdHC." + path.parent.name + "."
        for name in DECLARATION.findall(source):
            root = prefix + name
            if root in roots:
                raise ValueError("Duplicate declaration root: " + root)
            roots.add(root)
    ordered = dependency_order(paths)
    rebuilt = [p for p in ordered if p.parent == ASSEMBLY] if args.cached_dependencies else ordered
    protected = set(ordered) | {
        Path(__file__).resolve(), ROOT / "tools/verify_entropy_tail_components.py",
        ROOT / "tools/verify_blind_upper_components.py", ROOT / "tools/verify_tier6.py",
        ROOT / "tools/entropy_tail_specification_freeze.json", LEAN / "lean-toolchain",
        LEAN / "lake-manifest.json", LEAN / "lakefile.toml",
    }
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT / ".runtime/entropy-tail-assembly" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    status = dict(
        valid=False, scope="Single-coin upper ingredients and finite multilevel analytic budget certificate only.",
        entropy_tail_upper_verified=False, entropy_tail_lower_verified=False,
        closed_quantile_minimax_verified=False, marked_poisson_realization_verified=False,
        local_dependency_rebuild_performed=not args.cached_dependencies,
        module_count=len(paths), declaration_count=len(roots), source_sha256=hashes,
        roots=sorted(roots), exact_types_checked=0, rebuilt_local_modules=len(rebuilt), commands=[],
    )

    def save() -> None:
        (output / "status.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")

    save()
    audit = LEAN / ".audit/EntropyTailAssembly.lean"
    audit.parent.mkdir(exist_ok=True)
    audit_text = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    audit_text += EXACT_CHECKS + "\n" + "".join("#print axioms " + r + "\n" for r in sorted(roots))
    if FORBIDDEN.search(strip_comments(audit_text)):
        raise ValueError("Forbidden audit source")
    audit.write_text(audit_text, encoding="utf-8")
    status["audit_source_sha256"] = sha(audit)
    commands = []
    for path in rebuilt:
        relative = path.relative_to(LEAN)
        olean = Path(".lake/build/lib/lean") / relative.with_suffix(".olean")
        (LEAN / olean).parent.mkdir(parents=True, exist_ok=True)
        commands.append([args.lake, "env", "lean", "-j", "1", "-o", str(olean), str(relative)])
    commands.append([args.lake, "env", "lean", "-j", "1", str(audit.relative_to(LEAN))])
    for index, command in enumerate(commands, 1):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
        report = result.stdout + result.stderr
        (output / f"{index:03d}.log").write_text(report, encoding="utf-8")
        status["commands"].append(dict(command=command, exit_code=result.returncode))
        save()
        print(f"{index}/{len(commands)} {command[-1]}: exit {result.returncode}", flush=True)
        if result.returncode:
            print(report, flush=True)
            return result.returncode
    status["axioms"] = validate_reports(report, result.returncode, roots)
    validate_sources()
    if any(sha(ROOT / path) != digest for path, digest in hashes.items()):
        raise ValueError("Protected source changed during audit")
    if sha(audit) != status["audit_source_sha256"]:
        raise ValueError("Audit source changed during checking")
    status.update(valid=True, exact_types_checked=4)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
