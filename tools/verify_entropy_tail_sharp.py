"""Build and audit the explicit entropy-tail comparison for arbitrary probability laws."""
import argparse
import json
from pathlib import Path
import subprocess

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, sha, strip_comments, validate_dependency_freeze, validate_reports,
)
from verify_entropy_tail_components import dependency_order
from verify_entropy_tail import FREEZE, FROZEN

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
SOURCE = LEAN / "ThresholdHC" / "EntropyTailSharp"
PREFIX = "ThresholdHC.EntropyTailSharp."
AUDIT = SOURCE / "Audit.lean"
SPEC_SHA256 = "2e131950f38ef4f7ebb1810cb2df99a35e4cd6c3c1092a4377bf5231af02fa8f"


def validate_sources() -> set[str]:
    if sha(SOURCE / "Specification.lean") != SPEC_SHA256:
        raise ValueError("Changed explicit law statement from b05fead")
    freeze = json.loads(FREEZE.read_text(encoding="utf-8"))
    if freeze["source_sha256"] != FROZEN or any(sha(ROOT / p) != h for p, h in FROZEN.items()):
        raise ValueError("Changed original entropy-tail specification")
    validate_dependency_freeze(LEAN / "ThresholdHC/EntropyTail/Specification.lean", freeze)
    closure = dependency_order([AUDIT])
    paths = set(SOURCE.rglob("*.lean"))
    if not paths.issubset(closure):
        raise ValueError("Unregistered explicit entropy-tail module")
    for path in closure:
        if FORBIDDEN.search(strip_comments(path.read_text(encoding="utf-8"))):
            raise ValueError(f"Forbidden proof escape in {path}")
    roots = [PREFIX + n for p in paths
             for n in DECLARATION.findall(strip_comments(p.read_text(encoding="utf-8")))]
    required = {PREFIX + n for n in ("entropy_tail_explicit_law", "paper_comparison",
                                      "estimator_entropy_tail_lower", "closed_quantile_lower_explicit",
                                      "quantile_tail_lower_general")}
    if len(set(roots)) != len(roots) or not required.issubset(roots):
        raise ValueError("Duplicate or missing explicit entropy-tail declaration")
    return set(roots)


def audit_input(roots: set[str]) -> str:
    return ("import " + PREFIX + "Audit\n\n"
            + f"example : {PREFIX}ExplicitLawStatement := {PREFIX}entropy_tail_explicit_law\n\n"
            + "".join(f"#print axioms {name}\n" for name in sorted(roots)))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    roots = validate_sources()
    subprocess.run([args.lake, "build", PREFIX + "Audit"], cwd=LEAN, check=True)
    run = subprocess.run([args.lake, "env", "lean", "--stdin"], input=audit_input(roots),
                         cwd=LEAN, text=True, capture_output=True, encoding="utf-8")
    report = run.stdout + run.stderr
    print(report, end="")
    validate_reports(report, run.returncode, roots)


if __name__ == "__main__":
    main()
