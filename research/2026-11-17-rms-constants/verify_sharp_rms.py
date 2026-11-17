"""Compile, exact-type check and kernel-replay the sharp RMS proof components.

python verify_sharp_rms.py PATH/TO/BUILT/REPOSITORY [--lean PATH/TO/lean]
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import shutil
import tempfile

from verify_cap import AXIOMS, HERE, digest, run

MODULES = ("SharpAttainment", "SharpEntropy", "SharpTranscript", "SharpInformation", "SharpPrefixCost",
           "SharpWeakRisk", "SharpWeakPopulation", "SharpSimulation", "SharpSmallBudget",
           "SharpSmallPrefix", "SharpBayesBudget", "SharpFourBudget", "SharpScore", "SharpFisher",
           "SharpBarrier", "SharpAdaptivePrice", "SharpPriceBounds", "SharpCriticalBudget")
THEOREMS = {"four_flips_budget", "four_flips_squared_risk", "endpoint_minimax_upper",
            "three_bias_risk", "creation_tilt", "creation_wald", "creation_paired_cost",
            "weak_gap_minimax_lower", "critical_step_kernel", "posterior_lattice_gap",
            "four_budget_minimax_lower", "endpoint_minimax_eq", "adaptive_fisher_price",
            "near_perfect_integral", "minimax_from_tapered_price", "near_perfect_minimax_lower"}
AUDIT = "AuditSharpRMS"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--window", action="store_true", help="Check the intermediate-bias integer certificate and real cover.")
    args = parser.parse_args()
    modules = ("SharpWindow", "SharpWindowReal") if args.window else MODULES
    theorems = {"checked_window", "real_window"} if args.window else THEOREMS
    audit = "AuditSharpWindow" if args.window else AUDIT
    namespace = "ThresholdHC.SharpRMS.Window" if args.window else "ThresholdHC.SharpRMS"
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
    files = [f"{module}.lean" for module in (*modules, audit)]
    with tempfile.TemporaryDirectory() as scratch:
        tmp = Path(scratch)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [tmp, *libs])))
        for name in files:
            shutil.copyfile(HERE / name, tmp / name)
        hashes = {name: digest(tmp / name) for name in files}
        for module in modules:
            run([compiler, "-j6" if module == "SharpWindow" else "-j2", "-DwarningAsError=true", "-o", f"{module}.olean",
                 f"{module}.lean"], cwd=tmp, env=env)
        report = run([compiler, "-j2", "-DwarningAsError=true", f"{audit}.lean"], cwd=tmp, env=env)
        reports = re.findall(rf"'{re.escape(namespace)}\.(\w+)' depends on axioms: \[([^\]]*)\]", report)
        if len(reports) != len(theorems) or {name for name, _ in reports} != theorems:
            raise ValueError(f"Unexpected axiom report\n{report}")
        if any(set(names.split(", ")) - AXIOMS for _, names in reports):
            raise ValueError(f"Unexpected transitive axioms\n{report}")
        with ThreadPoolExecutor(max_workers=2) as pool:
            list(pool.map(lambda module: run([str(checker), module], cwd=tmp, env=env), modules))

    print(json.dumps({
        "compiler": run([compiler, "--version"], cwd=lean_dir),
        "imported_checkout_commit": run(["git", "rev-parse", "HEAD"], cwd=repo),
        "lean_source_tree": tree,
        "source_sha256": hashes,
        "exact_type_checks": sorted(theorems),
        "transitive_axioms": {name: names.split(", ") for name, names in reports},
        "kernel_replay": list(modules),
        "dependencies": "Existing compiled project and Mathlib imports",
        "scope": ("Integer certificate and rescaled real-bias coverage of its upper sums" if args.window else
                  "All gap laws at budgets up to four, exact endpoint minimax risk, weak and near-perfect critical single-gap lower bounds, tapered Fisher-information reduction, and local simulation"),
    }, indent=2))


if __name__ == "__main__":
    main()
