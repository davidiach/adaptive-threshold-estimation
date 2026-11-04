"""Build the direct finite-law proof components and check their transitive axioms."""
import argparse
from pathlib import Path
import subprocess

from verify_blind_upper_components import DECLARATION, strip_comments, validate_reports

LEAN = Path(__file__).resolve().parents[1] / "lean"
SOURCE = LEAN / "ThresholdHC" / "FiniteQuantile"
PREFIX = "ThresholdHC.FiniteQuantile."
AUDIT = SOURCE / "Audit.lean"


def validate_audit(report: str, exit_code: int) -> None:
    roots = {
        PREFIX + name
        for path in SOURCE.glob("*.lean") if path != AUDIT
        for name in DECLARATION.findall(strip_comments(path.read_text(encoding="utf-8")))
    }
    if not roots:
        raise ValueError("Empty finite-quantile audit")
    validate_reports(report, exit_code, roots)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    subprocess.run([args.lake, "build", PREFIX + "Audit"], cwd=LEAN, check=True)
    check = subprocess.run([args.lake, "env", "lean", str(AUDIT.relative_to(LEAN))],
                           cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
    report = check.stdout + check.stderr
    print(report, end="")
    validate_audit(report, check.returncode)


if __name__ == "__main__":
    main()
