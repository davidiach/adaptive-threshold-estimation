"""Audit the actual information-ratio Bellman characterization and deterministic attainment.

Default: rebuild every local dependency. --cached-dependencies: rebuild the
seven Bellman-connection modules and record all other dependency source hashes.
Neither mode claims the factor-sixteen risk comparison or genie convergence.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys

from verify_blind_upper_components import DECLARATION, FORBIDDEN, sha, strip_comments, validate_reports
from verify_entropy_tail_components import dependency_order

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
MAINS = [LEAN / "ThresholdHC/StoppingProgram/BellmanTheorem.lean"]
NEW_MODULES = {"PolicyFlow", "BellmanFlow", "PrefixInformation", "InformationBellman",
    "InformationFiniteness", "InformationIncrement", "BellmanTheorem"}
REQUIRED = {"ThresholdHC.StoppingProgram." + name for name in (
    "informationRatio_bellman", "informationRatio_top_iff", "informationRatio_increment_identity",
    "flowScore_maximum", "policyFlow_cone", "flowInformation_raw")}
EXACT = r"""
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    0 < N → informationRatio μ N Q ≠ ⊤ →
    informationRatio μ N Q = ENNReal.ofReal (bellmanRatio μ N Q) ∧
    (∀ κ : ℝ, rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work) κ (N-1) = 0 ↔
      κ = (informationRatio μ N Q).toReal) ∧
    ∃ p : ℕ → ℕ → ℝ, (∀ n k, p n k = 0 ∨ p n k = 1) ∧ p 0 0 = 0 ∧
      (∀ k, k ≤ N → p N k = 1) ∧ FlowCone (policyFlow N p) ∧ intensity (policyFlow N p) = 1 ∧
      flowInformation μ Q (policyFlow N p)/
        ENNReal.ofReal (countMean μ Q.work (policyFlow N p).continueWeight) = informationRatio μ N Q :=
  informationRatio_bellman
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors), 0 < N →
    (informationRatio μ N Q = ⊤ ↔ ∃ n k, n ≤ N ∧ k ≤ n ∧
      prefixCoefficient μ Q.variance n k = 0 ∧
      prefixCoefficient μ Q.high n k ≠ prefixCoefficient μ Q.low n k) := informationRatio_top_iff
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    0 < N → informationRatio μ N Q ≠ ⊤ → ∀ f : Flow N, FlowCone f →
    (∀ n k, n < N → k ≤ n → 0 ≤ informationIncrement μ Q n k) ∧
    (flowInformation μ Q f).toReal = ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n+1),
      rawArray f.continueWeight n k*informationIncrement μ Q n k := informationRatio_increment_identity
example : ∀ (μ : Measure Gap) (N : ℕ) (Q : FourPriors),
    Continuous (fun κ => rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work) κ (N-1)) ∧
    StrictAnti (fun κ => rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work) κ (N-1)) := by
  intro μ N Q
  exact ⟨continuous_rootBellman _ _ _,rootBellman_strictAnti _ _ (prefixCoefficient_nonneg μ Q.work) _⟩
example : ∀ (r w : ℕ → ℕ → ℝ) (κ : ℝ) {N : ℕ}, 0 < N → w 0 0 = 1 →
    (∀ f : Flow N, FlowCone f → intensity f = 1 → rawFlowScore f r w κ ≤ rootBellman r w κ (N-1)) ∧
    ∃ f : Flow N, FlowCone f ∧ intensity f = 1 ∧ rawFlowScore f r w κ = rootBellman r w κ (N-1) :=
  flowScore_maximum
"""


def validate_sources():
    ordered = dependency_order(MAINS)
    paths = [p for p in ordered if p.parent.name == "StoppingProgram"]
    roots = set()
    for path in paths:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape: " + str(path))
        for name in DECLARATION.findall(source):
            root = "ThresholdHC.StoppingProgram." + name
            if root in roots:
                raise ValueError("Duplicate root: " + root)
            roots.add(root)
    if REQUIRED - roots:
        raise ValueError("Missing exact target or required dependency: " + ", ".join(sorted(REQUIRED - roots)))
    if FORBIDDEN.search(strip_comments(EXACT)):
        raise ValueError("Forbidden exact audit source")
    return ordered, paths, roots


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--cached-dependencies", action="store_true")
    args = parser.parse_args()
    ordered, paths, roots = validate_sources()
    rebuilt = [p for p in paths if p.stem in NEW_MODULES] if args.cached_dependencies else ordered
    protected = set(ordered) | {Path(__file__).resolve(), ROOT / "tools/verify_blind_upper_components.py",
        ROOT / "tools/verify_entropy_tail_components.py", ROOT / "tools/verify_tier6.py",
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml"}
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT / ".runtime/information-bellman" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/InformationBellman.lean"
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    source += EXACT + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = dict(valid=False, scope="Actual count-flow information/work ratio: deterministic Bellman attainment, unique price zero, continuity and strict monotonicity, exact singular-state criterion, and nonnegative information-increment identity.",
        full_stopping_program_verified=False, information_bellman_verified=False,
        information_increment_verified=False, finite_risk_certificate_verified=False,
        full_genie_convergence_verified=False, entropy_tail_lower_verified=False,
        local_dependency_rebuild_performed=not args.cached_dependencies,
        module_count=len(paths), declaration_count=len(roots), exact_types_checked=0,
        rebuilt_local_modules=len(rebuilt), source_sha256=hashes, roots=sorted(roots), commands=[],
        audit_source_sha256=audit_hash)

    def save():
        (output / "status.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")

    save()
    commands = []
    for path in rebuilt:
        rel = path.relative_to(LEAN)
        obj = Path(".lake/build/lib/lean") / rel.with_suffix(".olean")
        (LEAN / obj).parent.mkdir(parents=True, exist_ok=True)
        commands.append([args.lake, "env", "lean", "-j", "1", "-o", str(obj), str(rel)])
    commands.append([args.lake, "env", "lean", "-j", "1", str(audit.relative_to(LEAN))])
    for n, command in enumerate(commands, 1):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
        report = result.stdout + result.stderr
        (output / f"{n:03d}.log").write_text(report, encoding="utf-8")
        status["commands"].append(dict(command=command, exit_code=result.returncode))
        save()
        print(f"{n}/{len(commands)} {command[-1]}: exit {result.returncode}", flush=True)
        if result.returncode:
            print(report, flush=True)
            return result.returncode
    status["axioms"] = validate_reports(report, result.returncode, roots)
    if any(sha(ROOT / p) != h for p, h in hashes.items()) or sha(audit) != audit_hash:
        raise ValueError("Source changed during audit")
    status.update(valid=True, exact_types_checked=5, information_bellman_verified=True,
        information_increment_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
