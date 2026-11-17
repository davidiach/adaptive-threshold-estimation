"""Replay the two cap theorems against a built checkout of the research repo.

python verify_cap.py PATH/TO/REPOSITORY [--lean PATH/TO/lean]
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
THEOREMS = {"square_root_cap_factor", "four_ninths_cap"}


def run(args, *, cwd, env=None):
    result = subprocess.run(args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, encoding="utf-8")
    if result.returncode:
        raise RuntimeError(f"{args[0]} exited {result.returncode}\n{result.stdout}")
    return result.stdout.strip()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("--lean", default="lean")
    args = parser.parse_args()
    repo = args.repo.resolve()
    lean_dir = repo / "lean"
    cache = lean_dir / ".lake"
    compiler = shutil.which(args.lean) or str(Path(args.lean).resolve())
    prefix = Path(run([compiler, "--print-prefix"], cwd=lean_dir))
    checker = prefix / "bin" / ("leanchecker.exe" if os.name == "nt" else "leanchecker")
    libs = [cache / "build/lib/lean"]
    libs.extend(path for path in (cache / "packages").glob("*/.lake/build/lib/lean"))
    if not (libs[0] / "ThresholdHC/GenieRate/Flow.olean").is_file():
        raise RuntimeError("Build ThresholdHC.GenieRate.Flow and ThresholdHC.Genie.OptimizedBrackets in this checkout first.")

    with tempfile.TemporaryDirectory() as scratch:
        tmp = Path(scratch)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [tmp, *libs])))
        for name in ("SharpCap.lean", "AuditSharpCap.lean"):
            shutil.copyfile(HERE / name, tmp / name)
        run([compiler, "-j2", "-DwarningAsError=true", "-o", "SharpCap.olean", "SharpCap.lean"], cwd=tmp, env=env)
        report = run([compiler, "-j2", "-DwarningAsError=true", "AuditSharpCap.lean"], cwd=tmp, env=env)
        reports = re.findall(r"'ThresholdHC\.CapReview\.(\w+)' depends on axioms: \[([^\]]*)\]", report)
        if len(reports) != len(THEOREMS) or {name for name, _ in reports} != THEOREMS:
            raise ValueError(f"Missing or unexpected axiom reports\n{report}")
        if any(set(names.split(", ")) != AXIOMS for _, names in reports):
            raise ValueError(f"Unexpected transitive axioms\n{report}")
        run([str(checker), "SharpCap"], cwd=tmp, env=env)

    result = {
        "compiler": run([compiler, "--version"], cwd=lean_dir),
        "imported_checkout_commit": run(["git", "rev-parse", "HEAD"], cwd=repo),
        "lean_source_tree": run(["git", "rev-parse", "HEAD:lean"], cwd=repo),
        "source_sha256": {name: digest(HERE / name) for name in ("SharpCap.lean", "AuditSharpCap.lean")},
        "fresh_compilation": "SharpCap",
        "exact_type_checks": sorted(THEOREMS),
        "transitive_axioms": {name: names.split(", ") for name, names in reports},
        "kernel_replay": "SharpCap passed",
        "dependencies": "Existing compiled project and Mathlib imports",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
