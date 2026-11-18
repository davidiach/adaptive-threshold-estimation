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


def local_dependencies(module):
    """Collect the research imports in dependency order, excluding the audit itself."""
    ordered = {}
    def visit(name):
        if name in ordered:
            return
        for dependency in re.findall(r"^import (\w+)$", (HERE / f"{name}.lean").read_text(encoding="utf-8-sig"), re.M):
            if (HERE / f"{dependency}.lean").is_file():
                visit(dependency)
        ordered[name] = None
    visit(module)
    return tuple(name for name in ordered if name != module)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("--lean", default="lean")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--window", action="store_true", help="Check all critical point masses.")
    modes.add_argument("--unrestricted", action="store_true", help="Check the sharp theorem for every ordinary gap law.")
    modes.add_argument("--oracles", action="store_true", help="Include the revealed- and selected-magnitude experiments.")
    modes.add_argument("--large-budget", action="store_true", help="Check the improved logarithmic bound in all three models.")
    modes.add_argument("--revisit", action="store_true", help="Check the adaptive 25-flip upper witness.")
    modes.add_argument("--pilot", action="store_true", help="Check the 18-flip pilot and seven adaptive follow-up choices.")
    modes.add_argument("--multi-bias", action="store_true", help="Check the five symmetric bias pairs and their uniform lower bounds.")
    args = parser.parse_args()
    window_modules = ("SharpGridArithmetic", "SharpWindow", "SharpWindowReal",
                      "SharpInterpolation", "SharpRectangles", "SharpGridPrices",
                      "SharpGridIntegral", "SharpGridSum", "SharpMiddleBudget")
    transfer_modules = ("SharpHeterogeneous", "SharpWordSimulation", "SharpAdaptiveSimulation",
                        "SharpCausal", "SharpArrayLaw", "SharpTapeLaw", "SharpTapeMixture",
                        "SharpSingleTape", "SharpPopulationTransfer", "SharpReduction")
    oracle_modules = ("SharpOracleTapes", "SharpOracleLaw", "SharpOracleReduction", "SharpOracleBounds",
                      "SharpFreshLabels", "SharpOracleAttainment")
    unrestricted = args.unrestricted or args.oracles
    window = args.window or unrestricted
    modules = (*MODULES, *window_modules) if window else MODULES
    theorems = ({"checked_window", "real_window", "middle_minimax_lower", "critical_minimax_lower"}
                if args.window else THEOREMS)
    audit = "AuditSharpWindow" if args.window else AUDIT
    namespace = r"ThresholdHC\.SharpRMS(?:\.Window)?" if args.window else r"ThresholdHC\.SharpRMS"
    if unrestricted:
        modules = (*modules, *transfer_modules, "SharpUnrestricted")
        theorems = {"unrestricted_minimax_lower", "universal_coefficient_iff", "large_budget_minimax_lower",
                    "critical_gap_reduction", "simulation_rms", "simulation_expected_work"}
        audit = "AuditSharpUnrestricted"
    if args.oracles:
        modules = (*modules, *oracle_modules)
        audit = "AuditSharpOracles"
        theorems = {"oracle_minimax_lower", "oracle_large_budget_lower", "oracle_endpoint_eq", "oracle_gap_reduction"}
    if args.large_budget:
        audit = "AuditLargeBudget"
        modules = local_dependencies(audit)
        namespace = r"ThresholdHC\.SharpRMS\.LargeBudget"
        theorems = {"adaptive_reverse_cost", "log_tests", "logarithmic_lower", "lower_25", "lower_100",
                    "twenty_five_budget", "twenty_five_squared_risk", "upper_25", "coefficient_upper"}
    if args.revisit:
        audit = "AuditRevisit"
        modules = local_dependencies(audit)
        namespace = r"ThresholdHC\.SharpRMS\.Revisit"
        theorems = {"revisit_cap", "revisit_budget", "revisit_squared_risk", "revisit_upper_25", "revisit_coefficient_upper"}
    if args.pilot:
        audit = "AuditPilot"
        modules = local_dependencies(audit)
        namespace = r"ThresholdHC\.SharpRMS\.Pilot"
        theorems = {"pilot_worst_squared", "pilot_cap", "pilot_budget", "pilot_squared_risk", "pilot_upper_25", "pilot_coefficient_upper"}
    if args.multi_bias:
        audit = "AuditMultiBias"
        modules = local_dependencies(audit)
        namespace = r"ThresholdHC\.SharpRMS\.MultiBias"
        theorems = {"scalar_test", "lower_of_price", "lower_curve", "lower_25", "lower_100"}
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
        def compile_module(module):
            jobs = "-j6" if module == "SharpWindow" else "-j2"
            run([compiler, jobs, "-DwarningAsError=true", "-o", f"{module}.olean",
                 f"{module}.lean"], cwd=tmp, env=env)

        def replay(module):
            run([str(checker), module], cwd=tmp, env=env)

        def check_integer_window():
            compile_module("SharpWindow")
            replay("SharpWindow")

        if window:
            # Compile and independently replay the costly integer proof while building the statistical modules.
            compile_module("SharpGridArithmetic")
            with ThreadPoolExecutor(max_workers=1) as pool:
                certificate = pool.submit(check_integer_window)
                for module in (*MODULES, "SharpInterpolation", "SharpRectangles", "SharpGridPrices",
                               "SharpGridIntegral", "SharpGridSum"):
                    compile_module(module)
                if unrestricted:
                    for module in transfer_modules:
                        compile_module(module)
                certificate.result()
            compile_module("SharpWindowReal")
            compile_module("SharpMiddleBudget")
            if unrestricted:
                compile_module("SharpUnrestricted")
            if args.oracles:
                for module in oracle_modules:
                    compile_module(module)
        else:
            for module in modules:
                compile_module(module)
        report = run([compiler, "-j2", "-DwarningAsError=true", f"{audit}.lean"], cwd=tmp, env=env)
        reports = re.findall(rf"'{namespace}\.(\w+)' depends on axioms: \[([^\]]*)\]", report)
        if len(reports) != len(theorems) or {name for name, _ in reports} != theorems:
            raise ValueError(f"Unexpected axiom report\n{report}")
        if any(set(names.split(", ")) - AXIOMS for _, names in reports):
            raise ValueError(f"Unexpected transitive axioms\n{report}")
        with ThreadPoolExecutor(max_workers=2) as pool:
            list(pool.map(replay, (module for module in modules if module != "SharpWindow")))

    print(json.dumps({
        "compiler": run([compiler, "--version"], cwd=lean_dir),
        "imported_checkout_commit": run(["git", "rev-parse", "HEAD"], cwd=repo),
        "lean_source_tree": tree,
        "source_sha256": hashes,
        "exact_type_checks": sorted(theorems),
        "transitive_axioms": {name: names.split(", ") for name, names in reports},
        "kernel_replay": list(modules),
        "dependencies": "Existing compiled project and Mathlib imports",
        "scope": ("Five symmetric sign-bias pairs, a budget-dependent lower bound, and explicit coefficients for B >= 25 and B >= 100 in all three models" if args.multi_bias else
                  "Eighteen fresh flips and seven adaptive choices, pathwise work cap, uniform squared risk, and ordinary large-budget coefficient upper bound" if args.pilot else
                  "Adaptive 20-plus-5 revisit rule, uniform work cap, squared risk for every sign law, and ordinary large-budget coefficient upper bound" if args.revisit else
                  "Symmetric adaptive entropy cost, exact three-bias test, and improved uniform constants for B >= 25 and B >= 100 in all three models, and an ordinary 25-flip upper witness" if args.large_budget else
                  "Both magnitude oracles: all gap laws, stronger large-budget bound, and exact endpoint attainment" if args.oracles else
                  "Sharp universal ordinary-model coefficient, stronger large-budget bound, and exact adaptive simulation identities" if args.unrestricted else
                  "All critical point masses, including the continuous intermediate window and its exact integer certificate" if args.window else
                  "All gap laws at budgets up to four, exact endpoint minimax risk, weak and near-perfect critical single-gap lower bounds, tapered Fisher-information reduction, and local simulation"),
    }, indent=2))


if __name__ == "__main__":
    main()
