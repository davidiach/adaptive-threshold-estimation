"""Rebuild and audit the completed rare-event work, excluding the entropy-tail lower bound.

Every local dependency is rebuilt. Independent modules may compile concurrently;
a module is launched only after all of its local dependencies succeed. The
separate component verifiers supply their exact statements and axiom registries.
Evidence is written to a new directory and all protected sources are rehashed.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from datetime import datetime, timezone
import importlib
import json
from pathlib import Path
import subprocess
import sys

from verify_blind_upper_components import FORBIDDEN, imports, module_path, sha, strip_comments, validate_reports
from verify_entropy_tail_components import dependency_order

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
COMPONENTS = (
    "entropy_tail_upper", "stopping_components", "stopping_dual", "rarity_support",
    "finite_stopping_program", "stopping_flow_mixture", "stopping_program_upper",
    "reference_absorption", "information_bellman", "ordered_information",
    "adaptive_information", "finite_risk_certificate", "infinite_cap_dual",
    "genie_brackets", "genie_convergence", "genie_conic", "genie_counterexample",
    "entropy_tail_bridge",
)


def collect():
    paths, roots, exact, tool_paths = set(), set(), [], set()
    for component in COMPONENTS:
        tool = importlib.import_module("verify_" + component)
        validated = tool.validate_sources()
        paths.update(validated[-2])
        roots.update(validated[-1])
        part = getattr(tool, "EXACT", getattr(tool, "EXACT_CHECKS", ""))
        part += "\n" + "".join(f"example : {target} := {root}\n"
            for root, target in getattr(tool, "TARGETS", {}).items())
        if not part.strip() or FORBIDDEN.search(strip_comments(part)):
            raise ValueError("Missing or unsafe exact statements: " + component)
        exact.append(f"namespace Audit_{component}\n{part}\nend Audit_{component}\n")
        tool_paths.add(Path(tool.__file__).resolve())
    assembly = importlib.import_module("verify_entropy_tail_assembly")
    exact.append("namespace Audit_assembly\n" + assembly.EXACT_CHECKS + "\nend Audit_assembly\n")
    tool_paths.add(Path(assembly.__file__).resolve())
    ordered = dependency_order(sorted(paths))
    # No local source may bypass the compiler using an admitted declaration.
    for path in ordered:
        if FORBIDDEN.search(strip_comments(path.read_text(encoding="utf-8"))):
            raise ValueError("Forbidden local proof escape: " + str(path))
    source = "".join("import " + ".".join(p.relative_to(LEAN).with_suffix("").parts) + "\n"
        for p in sorted(paths)) + "\n" + "\n".join(exact)
    source += "\n" + "".join("#print axioms " + root + "\n" for root in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    return ordered, paths, roots, source, tool_paths


def local_dependencies(ordered):
    available = set(ordered)
    graph = {p: {module_path(name) for name in imports(strip_comments(p.read_text(encoding="utf-8")))
        if name.startswith("ThresholdHC.")} for p in ordered}
    if any(not deps <= available for deps in graph.values()):
        raise ValueError("Incomplete local dependency closure")
    return graph


def ready_paths(pending, completed, graph):
    return [p for p in pending if graph[p] <= completed]


def port_dependents(ordered, graph):
    changed = {p for p in ordered if p.parent.name in
               {"EntropyTail", "EntropyTailQuantile", "EntropyTailBridge"}}
    while True:
        expanded = changed | {p for p in ordered if graph[p] & changed}
        if expanded == changed:
            return changed
        changed = expanded


def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--lean", help="Lean executable in an already initialized `lake env`")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--cached-dependencies", action="store_true",
        help="Rebuild both interfaces and every transitive dependent; hash other cached sources")
    args = parser.parse_args()
    compiler = [args.lean] if args.lean else [args.lake, "env", "lean"]
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    ordered, paths, roots, source, tool_paths = collect()
    graph = local_dependencies(ordered)
    rebuilt = port_dependents(ordered, graph) if args.cached_dependencies else set(ordered)
    protected = set(ordered) | tool_paths | {
        Path(__file__).resolve(), ROOT / "tools/test_rare_event_completion.py",
        ROOT / "tools/verify_blind_upper_components.py", ROOT / "tools/verify_entropy_tail_components.py",
        ROOT / "tools/verify_tier6.py", ROOT / "tools/entropy_tail_specification_freeze.json",
        ROOT / "tools/entropy_tail_quantile_original_freeze.json", ROOT / "tools/verify_entropy_tail.py",
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml"}
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    output = args.output_dir or ROOT / ".runtime/rare-event-completion" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/RareEventCompletion.lean"
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    status = dict(valid=False, scope="Deterministic quantile comparison, observable entropy-tail/quantile upper bounds, stopping programs, identification, infinite-cap dual and genie certificates, with exact compatibility with the canonical frozen interface. The entropy-tail statistical lower bound and hence two-sided statistical quantile characterization are excluded.",
        entropy_tail_lower_verified=False, closed_quantile_minimax_verified=False,
        local_dependency_rebuild_performed=not args.cached_dependencies, rebuilt_local_modules=0,
        cached_dependency_module_count=len(ordered)-len(rebuilt),
        rebuild_scope="both entropy-tail interfaces and all transitive dependents" if args.cached_dependencies else "all local dependencies",
        dependency_module_count=len(ordered), module_count=len(paths), declaration_count=len(roots),
        exact_types_checked=0, exact_types_requested=source.count("example :"),
        source_sha256=hashes, audit_source_sha256=sha(audit), roots=sorted(roots),
        component_verifiers=list(COMPONENTS), parallel_jobs=args.jobs, commands=[])

    def save():
        (output / "status.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")

    def run(path):
        rel = path.relative_to(LEAN)
        obj = Path(".lake/build/lib/lean") / rel.with_suffix(".olean")
        (LEAN / obj).parent.mkdir(parents=True, exist_ok=True)
        command = compiler + ["-j","1","-o",str(obj),str(rel)]
        result = subprocess.run(command,cwd=LEAN,capture_output=True,text=True,encoding="utf-8")
        return command,result

    save()
    pending = [p for p in ordered if p in rebuilt]
    completed, active = set(ordered)-rebuilt, {}
    rebuilt_count = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or active:
            for p in ready_paths(pending,completed,graph)[:args.jobs-len(active)]:
                pending.remove(p)
                active[pool.submit(run,p)] = p
            if not active:
                raise ValueError("No ready module; invalid dependency graph")
            finished, _ = wait(active,return_when=FIRST_COMPLETED)
            for future in finished:
                p = active.pop(future)
                command,result = future.result()
                index = len(status["commands"])+1
                report = result.stdout+result.stderr
                (output/f"{index:03d}.log").write_text(report,encoding="utf-8")
                status["commands"].append(dict(command=command,exit_code=result.returncode))
                save()
                print(f"{index}/{len(rebuilt)+1} {p.relative_to(LEAN)}: exit {result.returncode}",flush=True)
                if result.returncode:
                    print(report,flush=True)
                    return result.returncode
                completed.add(p)
                rebuilt_count += 1
                status["rebuilt_local_modules"] = rebuilt_count
                save()
    command = compiler + ["-j","1",str(audit.relative_to(LEAN))]
    result = subprocess.run(command,cwd=LEAN,capture_output=True,text=True,encoding="utf-8")
    report = result.stdout+result.stderr
    (output/f"{len(rebuilt)+1:03d}.log").write_text(report,encoding="utf-8")
    status["commands"].append(dict(command=command,exit_code=result.returncode))
    save()
    if result.returncode:
        print(report,flush=True)
        return result.returncode
    status["axioms"] = validate_reports(report,result.returncode,roots)
    if any(sha(ROOT/p) != h for p,h in hashes.items()) or sha(audit) != status["audit_source_sha256"]:
        raise ValueError("Protected source changed during audit")
    status.update(valid=True,exact_types_checked=status["exact_types_requested"])
    save()
    print(json.dumps(dict(valid=True,rebuilt=rebuilt_count,declarations=len(roots),evidence=str(output))),flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
