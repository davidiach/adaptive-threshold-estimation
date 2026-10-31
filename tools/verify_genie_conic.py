"""Audit the optimized direct risk certificate and finite atom genie SOCP.

Default rebuilds every local dependency. --cached-dependencies rebuilds the
eleven new direct-certificate/conic modules and hashes all other dependencies.
The entropy-tail statistical lower bound is outside this audit.
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
MAINS = [LEAN / "ThresholdHC/Genie/DirectRisk.lean", LEAN / "ThresholdHC/Genie/AtomConicRealization.lean"]
NEW_MODULES = {"DirectRiskOptimization", "DirectRisk", "BellmanEnvelope", "FiniteReveal",
    "FinitePriors", "FiniteConicEnvelope", "FiniteConicPrice", "ScalarPrice", "FiniteConicValue",
    "AtomConicModel", "AtomConicRealization"}
REQUIRED = {"ThresholdHC.Genie." + name for name in (
    "directRiskProfile_greatest", "directRiskProfile_square", "genie_direct_squared_risk",
    "genie_bellman_direct_squared_risk", "finiteGenieCones_iff_price",
    "finiteGenieCones_objective_attained", "atomConic_realization",
    "atomConicValue_eq_genieSquared", "atomConicVariableCount_bound")}

EXACT = r"""
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ t x : ℝ, 0 ≤ t → 0 ≤ x →
    IsGreatest ((directRiskProfile t x) '' Set.Icc (0:ℝ) 1)
      (directRiskProfile t x (directRiskScale x)) := directRiskProfile_greatest
example : ∀ t x : ℝ, 0 ≤ x →
    (directRiskProfile t x (directRiskScale x))^2 =
      if x ≤ 4/3 then t^2/4*(1-x/4)^2 else 4*t^2/(27*x) := directRiskProfile_square
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 ≤ ρ → 0 ≤ B →
    ∀ Q : FourPriors, Admissible μ ρ Q → signMean μ Q.low.val ≤ signMean μ Q.high.val →
    ∀ N : ℕ, 0 < N → ∀ κ : ℝ, 0 ≤ κ → genieInformationRatio μ N Q ≤ ENNReal.ofReal κ →
    ENNReal.ofReal (directRiskSquared ((signMean μ Q.high.val-signMean μ Q.low.val)/3) (B*κ)) ≤
      rareMinimaxRisk μ ρ B ^ 2 := genie_direct_squared_risk
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 ≤ ρ → 0 ≤ B →
    ∀ Q : FourPriors, Admissible μ ρ Q → signMean μ Q.low.val ≤ signMean μ Q.high.val →
    latentDivergence μ Q ≠ ⊤ → ∀ N : ℕ, 0 < N → ∀ κ : ℝ, 0 ≤ κ →
    rootBellman (genieReward μ Q N) (prefixCoefficient μ Q.work) κ (N-1) ≤ 0 →
    ENNReal.ofReal (directRiskSquared ((signMean μ Q.high.val-signMean μ Q.low.val)/3) (B*κ)) ≤
      rareMinimaxRisk μ ρ B ^ 2 := genie_bellman_direct_squared_risk
variable {I : Type*} [Fintype I]
example : ∀ (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 < w i) → μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) →
    ∀ Q : FourPriors, 0 < N → ∀ α η : ℝ, 0 < α → 0 ≤ η →
    ((∃ X rp rm, FiniteGenieCones (N := N) μ w d Q α η X rp rm) ↔
      genieInformationRatio μ N Q ≤ ENNReal.ofReal (4*η/α^2)) := finiteGenieCones_iff_price
example : ∀ (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 < w i) → μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) →
    ∀ B : ℝ, 0 < B → ∀ Q : FourPriors, 0 < N →
    ∃ (α η : ℝ) (X : CountState N → ℝ) (rp rm : I → ℝ), 0 ≤ α ∧ 0 ≤ η ∧
      FiniteGenieCones μ w d Q α η X rp rm ∧
      ENNReal.ofReal (α*(signMean μ Q.high.val-signMean μ Q.low.val)-α^2-η*B) = genieDualRatio μ B N Q :=
    finiteGenieCones_objective_attained
example : ∀ {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 ≤ w i) → μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) → Function.Injective d →
    ∀ ρ B : ℝ, 0 ≤ ρ → ∀ v : AtomConicPoint I N, AtomConicFeasible w d ρ v →
    ∃ Q : FourPriors, Admissible μ ρ Q ∧
      FiniteGenieCones μ w d Q v.scale v.price v.bellman v.revealPlus v.revealMinus ∧
      atomConicObjective w B v ≤ v.scale*(signMean μ Q.high.val-signMean μ Q.low.val)-v.scale^2-v.price*B :=
    atomConic_realization
example : ∀ (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 < w i) → μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) → Function.Injective d →
    ∀ ρ B : ℝ, 0 ≤ ρ → 0 < B → 0 < N →
    atomConicValue N w d ρ B = genieSquared μ ρ B N := atomConicValue_eq_genieSquared
example : ∀ (I : Type*) [Fintype I] (N : ℕ),
    atomConicVariableCount I N ≤ 3+6*Fintype.card I+(N+1)^2 := atomConicVariableCount_bound
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
    output = args.output_dir or ROOT / ".runtime/genie-conic" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/GenieConic.lean"
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    source += EXACT + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = dict(valid=False, scope="Optimized direct squared minimax certificate and exact finite-support genie SOCP, including zero scales and singular references. Entropy-tail statistical lower bound and infinite-divergence counterexample are outside this audit.",
        direct_certificate_verified=False, finite_atom_socp_verified=False, entropy_tail_lower_verified=False,
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
    status.update(valid=True, exact_types_checked=9, direct_certificate_verified=True, finite_atom_socp_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
