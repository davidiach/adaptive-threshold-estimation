"""Audit the arbitrary seeded ordered-flow aggregation and local Hellinger/work bound.

Default: rebuild every local dependency. --cached-dependencies: rebuild the
eleven ordered-experiment modules and record all other dependency source hashes.
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
MAINS = [LEAN / "ThresholdHC/StoppingProgram/OrderedInformationBound.lean"]
NEW_MODULES = {"OrderedPrefix", "RawFlowConstruction", "OrderedWeights", "FlowCostMoment",
    "OrderedStoppedLaw", "OrderedAffinity", "OrderedRewards", "OrderedWork", "MidpointInformation",
    "OrderedHellinger", "OrderedInformationBound"}
REQUIRED = {"ThresholdHC.StoppingProgram." + name for name in (
    "ordered_stopped_hellinger_work", "orderedFlow_actual_work", "orderedFlow_cone",
    "orderedFlow_midpoint_hellinger", "original_stopped_word_affinity", "midpoint_informationRatio_finite")}
EXACT = r"""
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 (Gap SignLaw)
example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E],
    ∀ (ν : Measure R) [IsFiniteMeasure ν] (A : StoppedProcedure R E) (N : ℕ),
    (∀ z, A.stop z ≤ N) → FlowCone (orderedFlow ν A N) := orderedFlow_cone
example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν],
    ∀ (q : SignLaw) (A : StoppedProcedure R E) (N : ℕ), (∀ z, A.stop z ≤ N) →
    populationExpectedWork μ ν (gapParameter false) (gapParameter true) (signUnit q) A =
      ENNReal.ofReal (countMean μ q (orderedFlow ν A N).continueWeight) := orderedFlow_actual_work
example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν],
    ∀ (q r : SignLaw) (A : StoppedProcedure R E) (N : ℕ), (∀ z, A.stop z ≤ N) →
    4*stoppedHellinger μ ν q r A N ≤ (flowInformation μ (midpointFourPriors q r) (orderedFlow ν A N)).toReal ∧
    (flowInformation μ (midpointFourPriors q r) (orderedFlow ν A N)).toReal ≤ 8*stoppedHellinger μ ν q r A N :=
  orderedFlow_midpoint_hellinger
example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν],
    ∀ (q r : SignLaw) (A : StoppedProcedure R E) (N : ℕ), (∀ z, A.stop z ≤ N) →
    1-(hellingerAffinity
      (cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit q) A N)
      (cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit r) A N)).toReal ≤
      ((informationRatio μ N (midpointFourPriors q r)).toReal/4)*
      (populationExpectedWork μ ν (gapParameter false) (gapParameter true)
        (signUnit (ThresholdHC.StoppingProgram.midpointPrior q r)) A).toReal := ordered_stopped_hellinger_work
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
    output = args.output_dir or ROOT / ".runtime/ordered-information" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/OrderedInformation.lean"
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n" for p in paths)
    source += EXACT + "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = dict(valid=False, scope="Arbitrary measurable seeds and order-dependent capped stopping rules aggregate to count flows with exact actual work; stopped-transcript Hellinger distance is within factors four and eight of midpoint information and is at most K times midpoint work divided by four.",
        full_stopping_program_verified=False, ordered_flow_aggregation_verified=False,
        local_hellinger_work_verified=False, finite_risk_certificate_verified=False,
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
    status.update(valid=True, exact_types_checked=4, ordered_flow_aggregation_verified=True,
        local_hellinger_work_verified=True)
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots), evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
