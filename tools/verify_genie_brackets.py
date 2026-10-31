"""Audit monotone genie brackets, Bellman certificates and the residual error bound.

Default rebuilds every local dependency. --cached-dependencies rebuilds the
nine latent-reveal modules and records other dependency source hashes.
Residual convergence and optimized genie convergence are not yet claimed.
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
MAINS = [LEAN / "ThresholdHC/Genie/RevealTruncation.lean", LEAN / "ThresholdHC/Genie/RevealBellman.lean",
    LEAN / "ThresholdHC/Genie/RevealResidual.lean"]
NEW_MODULES = {"PerspectiveIntegral", "RevealReward", "ExtendedFlowConservation", "FlowTruncation",
    "RevealProgram", "RevealTruncation", "RevealFiniteness", "RevealBellman", "RevealResidual"}
REQUIRED = {"ThresholdHC.Genie." + name for name in (
    "infiniteInformationRatio_le_genie", "genieInformationRatio_antitone", "genie_information_error",
    "genieInformationRatio_bellman_attained", "genieInformationRatio_bellman_certificate",
    "genieInformationRatio_top_iff", "prefixInformation_le_revealReward", "perspective_integral_le",
    "revealResidual_eq_sub", "genieFlowInformation_fullCap")}

EXACT = r"""
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (N : ℕ), 0 < N → ∀ Q : FourPriors,
    infiniteInformationRatio μ Q ≤ genieInformationRatio μ N Q := infiniteInformationRatio_le_genie
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors),
    Antitone (fun N : ℕ => genieInformationRatio μ (N+1) Q) := genieInformationRatio_antitone
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    latentDivergence μ Q ≠ ⊤ → genieInformationRatio μ N Q-informationRatio μ N Q ≤
      latentDivergence μ Q-terminalInformation μ Q N := genie_information_error
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    0 < N → latentDivergence μ Q ≠ ⊤ →
    genieInformationRatio μ N Q = ENNReal.ofReal (genieBellmanRatio μ N Q) ∧
    let f := bellmanFlow (genieReward μ Q N) (prefixCoefficient μ Q.work) (genieBellmanRatio μ N Q) N
    FlowCone f ∧ intensity f = 1 ∧ genieFlowInformation μ Q f /
      ENNReal.ofReal (countMean μ Q.work f.continueWeight) = genieInformationRatio μ N Q :=
  genieInformationRatio_bellman_attained
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    0 < N → latentDivergence μ Q ≠ ⊤ → ∀ κ : ℝ, 0 ≤ κ →
    (genieInformationRatio μ N Q ≤ ENNReal.ofReal κ ↔
      rootBellman (genieReward μ Q N) (prefixCoefficient μ Q.work) κ (N-1) ≤ 0) :=
  genieInformationRatio_bellman_certificate
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ), 0 < N → ∀ Q : FourPriors,
    (genieInformationRatio μ N Q = ⊤ ↔ latentDivergence μ Q = ⊤) := genieInformationRatio_top_iff
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors) (n k : ℕ),
    prefixInformation μ Q n k ≤ revealReward μ Q n k := prefixInformation_le_revealReward
example : ∀ (μ : Measure Gap) (Q : FourPriors) (N : ℕ),
    genieFlowInformation μ Q (fullCapFlow N) = latentDivergence μ Q := genieFlowInformation_fullCap
"""


def validate_sources():
    ordered = dependency_order(MAINS)
    paths = [p for p in ordered if p.parent.name == "Genie"]
    roots = set()
    for path in paths:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape: " + str(path))
        for name in DECLARATION.findall(source):
            root = "ThresholdHC.Genie." + name
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
    output = args.output_dir or ROOT / ".runtime/genie-brackets" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/GenieBrackets.lean"
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    source += EXACT + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = dict(valid=False, scope="Extended latent-reveal ratio brackets, monotonicity, finite-divergence residual bound, exact Bellman certificate and deterministic attainment. Residual convergence, optimized genie convergence and entropy-tail statistical lower bound are not claimed.",
        genie_brackets_verified=False, genie_error_bound_verified=False,
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
    status.update(valid=True, exact_types_checked=8, genie_brackets_verified=True, genie_error_bound_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
