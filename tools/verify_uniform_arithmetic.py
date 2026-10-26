"""Kernel-check the seven unscored scalar lemmas supporting the paper bound."""
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
NAMES = {"error_prefactor_lt", "geometric_second_moment_factor_lt",
         "fourth_root_three_lt", "second_moment_scalar_lt", "survival_coefficients",
         "work_scalar_lt", "product_of_moment_bounds"}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    result = subprocess.run(["lake", "env", "lean", "../proposals/constants/UniformArithmetic.lean"],
                            cwd=ROOT / "lean", capture_output=True, text=True)
    output = result.stdout + result.stderr
    (ROOT / "results/constants_uniform_lean_audit.log").write_text(output, encoding="utf-8")
    pattern = r"'ThresholdHC\.PaperConstants\.(\w+)'\s+(depends on axioms:\s*\[(.*?)\]|does not depend on any axioms)"
    reports = {}
    for match in re.finditer(pattern, output, re.S):
        axioms = [] if match[3] is None else [s.strip() for s in match[3].split(',') if s.strip()]
        reports[match[1]] = axioms
    ok = result.returncode == 0 and set(reports) == NAMES and all(set(a) <= ALLOWED for a in reports.values())
    summary = dict(valid=ok, exit_code=result.returncode, reports=reports,
                   scope="scalar inequalities only; full probability theorem is not formalized")
    (ROOT / "results/constants_uniform_lean_status.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Scalar Lean audit: valid={ok}, reports={len(reports)}/7, exit={result.returncode}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
