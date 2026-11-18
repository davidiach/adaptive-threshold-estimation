"""Rebuild the audited research dependencies and replay the two-update proof."""
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
FEEDBACK = HERE.parent / "2026-11-18-pilot-feedback"
SCHEDULED = HERE.parent / "2026-11-18-scheduled-update"
sys.dont_write_bytecode = True
sys.path.insert(0, str(PILOT))
from verify_cap import AXIOMS, digest, run

MODULES = ["TwoUpdateBellman", "TwoUpdatePolicy", "TwoUpdateBayes", "TwoUpdateCertificate", "TwoUpdatePopulation"]
THEOREMS = {"certified", "total", "expect", "four_lower", "rms_lower", "rms_separation"}


def audited_sources(record, key):
    data = json.loads(record.read_text())
    sources = [record.parent / (m + ".lean") for m in data["kernel_replay"]]
    for source in sources:
        if digest(source) != data[key][source.name]:
            raise ValueError(f"Source differs from its audit: {source}")
    return sources


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
    pilot = PILOT / "pilot-audit.json"
    feedback = FEEDBACK / "audit.json"
    deps = audited_sources(pilot, "source_sha256") + audited_sources(feedback, "new_source_sha256")
    scheduled = SCHEDULED / "audit.json"
    deps.extend(p for p in audited_sources(scheduled, "source_sha256")
                if p.stem == "FixedHorizonRisk")
    sources = [HERE / (m + ".lean") for m in MODULES]
    audit = HERE / "AuditTwoUpdates.lean"
    with tempfile.TemporaryDirectory() as scratch:
        tmp = Path(scratch)
        libs = [tmp, cache / "build/lib/lean", *(cache / "packages").glob("*/.lake/build/lib/lean")]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libs)))
        for source in [*deps, *sources, audit]:
            print(f"Building {source.stem}", file=sys.stderr, flush=True)
            shutil.copyfile(source, tmp / source.name)
            reports = run([lean, "-j2", "-DwarningAsError=true", "-o", source.stem + ".olean",
                           source.name], cwd=tmp, env=env)
        axioms = dict(re.findall(r"'PilotFeedback\.TwoUpdates\.(\w+)' depends on axioms: \[([^\]]*)\]", reports))
        for name in re.findall(r"'PilotFeedback\.TwoUpdates\.(\w+)' does not depend on any axioms", reports):
            axioms[name] = ""
        axioms = {name: value.split(", ") if value else [] for name, value in axioms.items()}
        if set(axioms) != THEOREMS or any(set(names) - AXIOMS for names in axioms.values()):
            raise ValueError(f"Unexpected theorem or axiom report\n{reports}")

        def replay(name):
            print(f"Replaying {name}", file=sys.stderr, flush=True)
            run([str(checker), name], cwd=tmp, env=env)

        with ThreadPoolExecutor(max_workers=2) as pool:
            list(pool.map(replay, MODULES))
    print(json.dumps({
        "compiler": version,
        "built_lean_tree": run(["git", "rev-parse", "HEAD:lean"], cwd=repo),
        "proof_checkout_lean_tree": run(["git", "rev-parse", "HEAD:lean"], cwd=HERE),
        "dependency_audit_sha256": {r.parent.name: digest(r) for r in [pilot, feedback, scheduled]},
        "rebuilt_dependencies": [p.stem for p in deps],
        "source_sha256": {p.name: digest(p) for p in [*sources, audit]},
        "axioms": axioms,
        "kernel_replay": MODULES,
        "independent_calculation": run([sys.executable, str(HERE / "check.py")], cwd=HERE),
    }, indent=2))


if __name__ == "__main__":
    main()
