"""Check the critical gap law, the policy-uniform pair, and the minimax confidence rate."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ConfidenceTransfer.CriticalRate
noncomputable section
open MeasureTheory ThresholdHC.ConfidenceTransfer ThresholdHC.CriticalEntropy
open ThresholdHC.Tier6
open scoped ENNReal
example : criticalPositiveLaw.map (Subtype.val : Gap → ℝ) =
    (volume.restrict (Set.Ioc (0 : ℝ) (1/4))).withDensity (fun d => ENNReal.ofReal (32*d)) :=
  criticalPositiveLaw_map
example : ∃ a : ℝ, 0 < a ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1/4 →
    CommonPairBound criticalPositiveLaw ρ (ρ/32) (a*(ρ*criticalLogFactor ρ)) :=
  critical_common_pair_bound
example : ∃ c : ℝ, 0 < c ∧ ∀ ρ B δ : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal (c * min ρ (Real.sqrt
      (ρ*((1+Real.log (1/ρ))*(1+Real.log (1+Real.log (1/ρ))))*Real.log (1/δ)/B))) ≤
      rareConfidenceRadius criticalPositiveLaw ρ B δ := critical_confidence_lower
""".lstrip()
    names = {
        "ThresholdHC.ConfidenceTransfer." + name for name in [
            "criticalPositiveLaw", "criticalPositiveLaw_map", "criticalPositiveLaw_probability",
            "critical_parameter_law", "criticalSign", "critical_sign_mean", "critical_local_transfer",
            "CriticalConfidenceLowerStatement", "critical_common_pair_bound", "critical_confidence_lower",
            "minimax_confidence_rate_of_common_pair",
        ]
    }
    names.add("ThresholdHC.CriticalEntropy.critical_common_capped_pair")
    return source + "".join("#print axioms " + n + "\n" for n in sorted(names)), names


def main():
    source, names = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ConfidenceTransfer.CriticalRate"], cwd=LEAN, check=True)
    result = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                            text=True, encoding="utf-8", capture_output=True)
    output = result.stdout + result.stderr
    print(output, end="")
    validate_reports(output, result.returncode, names)
    print(f"Verified {len(names)} transitive axiom reports")


if __name__ == "__main__":
    main()
