"""Build the direct finite-law proof components and check their transitive axioms."""
import argparse
import hashlib
from pathlib import Path
import subprocess

from verify_blind_upper_components import DECLARATION, FORBIDDEN, strip_comments, validate_reports
from verify_entropy_tail_components import dependency_order

LEAN = Path(__file__).resolve().parents[1] / "lean"
SOURCE = LEAN / "ThresholdHC" / "FiniteQuantile"
PREFIX = "ThresholdHC.FiniteQuantile."
AUDIT = SOURCE / "Audit.lean"
SPEC_SHA256 = "16ef75f25f8448133af321d7016e5db8bc1a8d5ac7569deefec884dcf920d16a"


def validate_sources() -> set[str]:
    if hashlib.sha256((SOURCE / "Specification.lean").read_bytes()).hexdigest() != SPEC_SHA256:
        raise ValueError("Direct finite-law target differs from the statement at 5557334")
    closure = dependency_order([AUDIT])
    excluded = {"EntropyTail/Lower.lean", "EntropyTail/Law.lean", "ClosedQuantile/Full.lean",
                "EntropyTailLower/CertificateLower.lean"}
    for path in closure:
        if path.relative_to(LEAN / "ThresholdHC").as_posix() in excluded:
            raise ValueError(f"Direct proof imports a general statistical lower result: {path}")
        if FORBIDDEN.search(strip_comments(path.read_text(encoding="utf-8"))):
            raise ValueError(f"Forbidden proof escape in {path}")
    if set(SOURCE.glob("*.lean")) - set(closure):
        raise ValueError("Unregistered finite-quantile module")
    roots = {
        PREFIX + name
        for path in SOURCE.glob("*.lean") if path != AUDIT
        for name in DECLARATION.findall(strip_comments(path.read_text(encoding="utf-8")))
    }
    if PREFIX + "direct_finite_law" not in roots:
        raise ValueError("Missing explicit finite-law theorem")
    return roots


def validate_audit(report: str, exit_code: int) -> None:
    validate_reports(report, exit_code, validate_sources())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    validate_sources()
    subprocess.run([args.lake, "build", PREFIX + "Audit"], cwd=LEAN, check=True)
    check = subprocess.run([args.lake, "env", "lean", str(AUDIT.relative_to(LEAN))],
                           cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
    report = check.stdout + check.stderr
    print(report, end="")
    validate_audit(report, check.returncode)


if __name__ == "__main__":
    main()
