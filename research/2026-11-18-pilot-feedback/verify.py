"""Rebuild the comparison and its adaptive witness against compiled project imports."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PILOT = HERE.parent / "2026-11-17-rms-constants"
sys.dont_write_bytecode = True
sys.path.insert(0, str(PILOT))
from verify_cap import AXIOMS, digest, run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("built_repo", type=Path)
    parser.add_argument("--lean", default="lean")
    args = parser.parse_args()
    repo = args.built_repo.resolve()
    cache = repo / "lean/.lake"
    lean = shutil.which(args.lean) or str(Path(args.lean).resolve())
    version = run([lean, "--version"], cwd=HERE)
    prefix = Path(run([lean, "--print-prefix"], cwd=HERE))
    checker = prefix / "bin" / ("leanchecker.exe" if os.name == "nt" else "leanchecker")
    pilot_audit = json.loads((PILOT / "pilot-audit.json").read_text())
    sources = [PILOT / (m + ".lean") for m in pilot_audit["kernel_replay"]]
    for source in sources:
        if digest(source) != pilot_audit["source_sha256"][source.name]:
            raise ValueError(f"Pilot source differs from its audit: {source.name}")
    new_modules = ["FeedbackTable", "FeedbackRisk", "FeedbackComparison", "FeedbackSeparation",
                   "OrderedPolicy", "OrderedExperiment", "OrderedCounts", "OrderedBayes",
                   "OrderedReduction", "OrderedPopulation"]
    sources.extend(HERE / (m + ".lean") for m in new_modules)
    expected = {"all_rows", "worstFour_lower", "strict_separation",
                "Ordered.ordered_reduction", "Ordered.counts_marginal",
                "Ordered.original_lower", "Ordered.original_separation"}
    built_tree = run(["git", "rev-parse", "HEAD:lean"], cwd=repo)
    proof_tree = run(["git", "rev-parse", "HEAD:lean"], cwd=HERE)

    with tempfile.TemporaryDirectory() as scratch:
        tmp = Path(scratch)
        libs = [tmp, cache / "build/lib/lean", *(cache / "packages").glob("*/.lake/build/lib/lean")]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libs)))
        for source in sources:
            print(f"Building {source.stem}", file=sys.stderr, flush=True)
            shutil.copyfile(source, tmp / source.name)
            run([lean, "-j2", "-DwarningAsError=true", "-o", source.stem + ".olean", source.name],
                cwd=tmp, env=env)
        audit = HERE / "AuditFeedback.lean"
        shutil.copyfile(audit, tmp / audit.name)
        reports = run([lean, "-j2", "-DwarningAsError=true", audit.name], cwd=tmp, env=env)
        axioms = dict(re.findall(r"'PilotFeedback\.([\w.]+)' depends on axioms: \[([^\]]*)\]", reports))
        if set(axioms) != expected or any(set(names.split(", ")) - AXIOMS for names in axioms.values()):
            raise ValueError(f"Unexpected theorem or axiom report\n{reports}")
        def replay(name):
            print(f"Replaying {name}", file=sys.stderr, flush=True)
            run([str(checker), name], cwd=tmp, env=env)
        with ThreadPoolExecutor(max_workers=2) as pool:
            list(pool.map(replay, new_modules))
    print(json.dumps({
        "compiler": version,
        "built_lean_tree": built_tree,
        "proof_checkout_lean_tree": proof_tree,
        "existing_dependencies": "Compiled repository and Mathlib modules",
        "rebuilt_pilot": pilot_audit["kernel_replay"],
        "pilot_source_audit_sha256": digest(PILOT / "pilot-audit.json"),
        "new_source_sha256": {p.name: digest(p) for p in [*sources[-len(new_modules):], audit]},
        "axioms": {k: v.split(", ") for k, v in axioms.items()},
        "kernel_replay": new_modules,
    }, indent=2))


if __name__ == "__main__":
    main()
