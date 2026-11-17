"""Compile, exact-type check and kernel-replay the sharp RMS proof components.

python verify_sharp_rms.py PATH/TO/BUILT/REPOSITORY [--lean PATH/TO/lean]
"""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import tempfile

from verify_cap import AXIOMS, HERE, digest, run

MODULES = ("SharpAttainment", "SharpEntropy", "SharpTranscript", "SharpInformation", "SharpPrefixCost",
           "SharpWeakRisk", "SharpWeakPopulation", "SharpSimulation", "SharpSmallBudget",
           "SharpSmallPrefix", "SharpBayesBudget", "SharpFourBudget")
THEOREMS = {"four_flips_budget", "four_flips_squared_risk", "endpoint_minimax_upper",
            "three_bias_risk", "creation_tilt", "creation_wald", "creation_paired_cost",
            "weak_gap_minimax_lower", "critical_step_kernel", "posterior_lattice_gap",
            "four_budget_minimax_lower", "endpoint_minimax_eq"}
AUDIT = "AuditSharpRMS"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("--lean", default="lean")
    args = parser.parse_args()
    repo = args.repo.resolve()
    lean_dir = repo / "lean"
    tree = run(["git", "rev-parse", "HEAD:lean"], cwd=repo)
    if tree != run(["git", "rev-parse", "HEAD:lean"], cwd=HERE):
        raise ValueError("The build checkout and the proof checkout have different Lean source trees.")
    compiler = shutil.which(args.lean) or str(Path(args.lean).resolve())
    prefix = Path(run([compiler, "--print-prefix"], cwd=lean_dir))
    checker = prefix / "bin" / ("leanchecker.exe" if os.name == "nt" else "leanchecker")
    cache = lean_dir / ".lake"
    libs = [cache / "build/lib/lean", *(cache / "packages").glob("*/.lake/build/lib/lean")]
    files = [f"{module}.lean" for module in (*MODULES, AUDIT)]
    with tempfile.TemporaryDirectory() as scratch:
        tmp = Path(scratch)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [tmp, *libs])))
        for name in files:
            shutil.copyfile(HERE / name, tmp / name)
        hashes = {name: digest(tmp / name) for name in files}
        for module in MODULES:
            run([compiler, "-j2", "-DwarningAsError=true", "-o", f"{module}.olean",
                 f"{module}.lean"], cwd=tmp, env=env)
        report = run([compiler, "-j2", "-DwarningAsError=true", f"{AUDIT}.lean"], cwd=tmp, env=env)
        reports = re.findall(r"'ThresholdHC\.SharpRMS\.(\w+)' depends on axioms: \[([^\]]*)\]", report)
        if len(reports) != len(THEOREMS) or {name for name, _ in reports} != THEOREMS:
            raise ValueError(f"Unexpected axiom report\n{report}")
        if any(set(names.split(", ")) - AXIOMS for _, names in reports):
            raise ValueError(f"Unexpected transitive axioms\n{report}")
        for module in MODULES:
            run([str(checker), module], cwd=tmp, env=env)

    print(json.dumps({
        "compiler": run([compiler, "--version"], cwd=lean_dir),
        "imported_checkout_commit": run(["git", "rev-parse", "HEAD"], cwd=repo),
        "lean_source_tree": tree,
        "source_sha256": hashes,
        "exact_type_checks": sorted(THEOREMS),
        "transitive_axioms": {name: names.split(", ") for name, names in reports},
        "kernel_replay": list(MODULES),
        "dependencies": "Existing compiled project and Mathlib imports",
        "scope": "All gap laws at budgets up to four, exact endpoint minimax risk, weak critical single-gap lower bound, finite-prefix information and local simulation",
    }, indent=2))


if __name__ == "__main__":
    main()
