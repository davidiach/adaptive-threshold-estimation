"""Check quarter smoothing in both KL directions for arbitrary probability measures."""

import subprocess

from verify_blind_upper_components import LEAN, sha, validate_reports


PREFIX = "ThresholdHC.ConfidenceTransfer."
SOURCES = LEAN / "ThresholdHC/ConfidenceTransfer"
SPEC_HASH = "22c8206aaf7fcc0164716e087f9211c0bd32d71b0c809aa92adacad0d76af503"
AFFINITY_HASH = "5a4b8bb5bf4cd2645df2292a121741e4b8eb7abf62a4b627a8bbb77f54ccf422"


def audit_input():
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed quarter-smoothing statement from 491dfc2")
    if sha(LEAN / "ThresholdHC/CriticalEntropy/HellingerModel.lean") != AFFINITY_HASH:
        raise ValueError("Changed Hellinger normalization")
    roots = {PREFIX + name for name in (
        "quarterMix", "QuarterSmoothingStatement", "quarter_kl_density",
        "quarter_smoothing", "quarter_smoothing_both",
    )}
    source = "\n".join([
        "import ThresholdHC.ConfidenceTransfer.Quarter",
        "open MeasureTheory InformationTheory ThresholdHC.ConfidenceTransfer",
        "open scoped NNReal ENNReal",
        "example : QuarterSmoothingStatement := quarter_smoothing_both",
        "example {Ω : Type} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]",
        "    [IsProbabilityMeasure Q] :",
        "    let A := (3/4 : ℝ≥0) • P + (1/4 : ℝ≥0) • Q",
        "    let C := (1/4 : ℝ≥0) • P + (3/4 : ℝ≥0) • Q",
        "    max (klDiv A C) (klDiv C A) ≤ ENNReal.ofReal",
        "      ((8/3) * (1 - (ThresholdHC.CriticalEntropy.hellingerAffinity P Q).toReal)) := by",
        "  simpa only [quarterMix, add_comm ((3/4 : ℝ≥0) • Q)] using",
        "    (quarter_smoothing_both P Q)",
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    return source, roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", PREFIX + "Quarter"], cwd=LEAN, check=True)
    run = subprocess.run(
        ["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
        text=True, encoding="utf-8", capture_output=True,
    )
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
