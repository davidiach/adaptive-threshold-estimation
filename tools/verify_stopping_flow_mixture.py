"""Audit finite flow conservation, Bellman bounds, decision mixtures and observable calls.

Default: rebuild every local dependency. --cached-dependencies: rebuild the
ten flow and policy modules and record all other dependency source hashes.
Neither mode claims statistical flow realization or the risk certificate.
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
MAINS = [LEAN / "ThresholdHC/StoppingProgram" / name for name in ("FlowMixture.lean", "FlowPotential.lean", "TableCall.lean")]
NEW_MODULES = {"PascalFlow", "PrefixCoefficients", "FlowConservation", "FlowPotential", "PolicyWeights",
    "DecisionMixture", "DecisionIndependence", "PolicyMixture", "FlowMixture", "TableCall"}
REQUIRED = {"ThresholdHC.StoppingProgram." + name for name in (
    "flow_mixture_weights", "flow_mixture_probability", "flow_mixture_supported_tables",
    "flowScore_le_rootBellman", "countMean_stop_eq_intensity", "tableCall", "tableCost_eq_iff")}
EXACT = r"""
open MeasureTheory
open scoped BigOperators
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)
example : ∀ {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (f : Flow N),
    FlowCone f → countMean μ q f.stopWeight = intensity f := countMean_stop_eq_intensity
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → ∀ (r w : ℕ → ℕ → ℝ) (κ : ℝ), w 0 0 = 1 →
    (∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1),
      (rawArray f.stopWeight n k*r n k-κ*rawArray f.continueWeight n k*w n k)) ≤
        intensity f*rootBellman r w κ (N-1) := flowScore_le_rootBellman
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → ∀ s : CountState N,
    (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b*
      (policyArrival (intensity f) (countDecision b) s.1.val s.2.val*countDecision b s.1.val s.2.val)) =
        rawArray f.stopWeight s.1.val s.2.val ∧
    (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b*
      (policyArrival (intensity f) (countDecision b) s.1.val s.2.val*(1-countDecision b s.1.val s.2.val))) =
        rawArray f.continueWeight s.1.val s.2.val := flow_mixture_weights
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → 0 < N →
    (∀ b, 0 ≤ decisionWeight (flowDecisionParameters f) b) ∧
    (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b) = 1 ∧
    ∀ b : CountState N → Bool, 0 < decisionWeight (flowDecisionParameters f) b →
      b (rootState N) = false ∧ ∀ s : CountState N, s.1.val = N → b s = true := by
  intro N f hf hN
  exact ⟨(flow_mixture_probability f hf).1,(flow_mixture_probability f hf).2,
    fun b hb => flow_mixture_supported_tables f hf hN b hb⟩
example : ∀ {N : ℕ} (hN : 0 < N) (b : CountState N → Bool) (y : CountState N → ℝ),
    ∀ ω : ℕ → Bool, (tableCall hN b y).cost ω ≤ N ∧
      (tableCall hN b y).value ω = y (tableStoppedState b ω) ∧
      ‖(tableCall hN b y).value ω‖ ≤ ∑ s, ‖y s‖ := by
  intro N hN b y ω
  exact ⟨tableCall_cost_le hN b y ω,tableValue_eq b y ω,tableValue_bounded b y ω⟩
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
    output = args.output_dir or ROOT / ".runtime/stopping-flow-mixture" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/StoppingFlowMixture.lean"
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    source += EXACT + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = dict(valid=False, scope="Count-flow conservation, Bellman potential upper bounds, exact finite decision-table mixture weights, positive-weight root/cap decisions, and actual bounded observable calls. Statistical moment identities and the risk theorem remain separate.",
        full_stopping_program_verified=False, finite_policy_mixture_verified=False,
        observable_finite_calls_verified=False,
        statistical_flow_realization_verified=False, finite_risk_certificate_verified=False,
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
    status.update(valid=True, exact_types_checked=5, finite_policy_mixture_verified=True,
        observable_finite_calls_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
