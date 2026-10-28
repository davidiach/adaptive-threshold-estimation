"""Kernel-check the seven unscored scalar lemmas supporting the paper bound."""
import json
from pathlib import Path
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, SORRY_WARNING, strip_comments

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "proposals/constants/UniformArithmetic.lean"
NAMES = {"error_prefactor_lt", "geometric_second_moment_factor_lt",
         "fourth_root_three_lt", "second_moment_scalar_lt", "survival_coefficients",
         "work_scalar_lt", "product_of_moment_bounds"}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(r"'ThresholdHC\.PaperConstants\.(\w+)'\s+"
                    r"(depends on axioms:\s*\[(.*?)\]|does not depend on any axioms)", re.S)


def check(output, returncode):
    """Return (valid, reports). A lemma reported twice or a sorry warning is invalid."""
    reports = {}
    duplicate = False
    for match in REPORT.finditer(output):
        duplicate |= match[1] in reports
        reports[match[1]] = [] if match[3] is None else [s.strip() for s in match[3].split(',') if s.strip()]
    ok = (returncode == 0 and not duplicate and not SORRY_WARNING.search(output)
          and set(reports) == NAMES and all(set(a) <= ALLOWED for a in reports.values()))
    return ok, reports


def main():
    if FORBIDDEN.search(strip_comments(SOURCE.read_text(encoding="utf-8"))):
        raise SystemExit("Forbidden proof escape in " + SOURCE.name)
    result = subprocess.run(["lake", "env", "lean", "../proposals/constants/UniformArithmetic.lean"],
                            cwd=ROOT / "lean", capture_output=True, text=True, encoding="utf-8")
    output = result.stdout + result.stderr
    (ROOT / "results/constants_uniform_lean_audit.log").write_text(output, encoding="utf-8")
    ok, reports = check(output, result.returncode)
    summary = dict(valid=ok, exit_code=result.returncode, reports=reports,
                   scope="scalar inequalities only; full theorem audited separately by verify_uniform713.py")
    (ROOT / "results/constants_uniform_lean_status.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Scalar Lean audit: valid={ok}, reports={len(reports)}/7, exit={result.returncode}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
