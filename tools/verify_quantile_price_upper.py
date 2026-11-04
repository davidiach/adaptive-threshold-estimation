"""Audit the 31/20 upper bound on the original general-law selection functional."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports
from verify_quantile_selection import audit_input as original_audit


def audit_input():
    # Include the earlier 8/5 statements after sharing their pointwise reduction.
    old, roots = original_audit(["Interaction", "SeparatedCost", "Full"])
    names = {"ThresholdHC.QuantilePrice." + n for n in [
        "weight", "weight_pos", "weight_mass", "weight_coefficient", "weight_band",
        "price_quartic", "scalar_price", "separated_cost", "quantile_le_31_20_selection",
    ]}
    new = """
open MeasureTheory Real ThresholdHC.Tier6
open scoped ENNReal
example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ} (hr : 0 < ρ)
    (hr' : ρ ≤ 1/4) (hb : 0 < B) :
    ThresholdHC.EntropyTail.selection μ ρ B ≤ ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ∧
    ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B ≤
      ENNReal.ofReal (31/20)*ThresholdHC.EntropyTail.selection μ ρ B :=
  ThresholdHC.QuantilePrice.quantile_le_31_20_selection μ hr hr' hb
example (Z : Measure Gap) [IsFiniteMeasure Z] {t : ℝ} (ht : 0 < t)
    (hs : ∀ᵐ d : Gap ∂Z, t ≤ (d:ℝ)) :
    ThresholdHC.EntropyTailQuantile.measureCostEntropy Z ≤
      ENNReal.ofReal (((16/9)/t)*∫ d : Gap, (d:ℝ)⁻¹ ∂Z) := ThresholdHC.QuantilePrice.separated_cost Z ht hs
""".strip()
    commands = ["import ThresholdHC.QuantilePrice.Full", old, new]
    commands.extend("#print axioms " + name for name in sorted(names))
    return "\n".join(commands) + "\n", roots | names


def main():
    src, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.QuantilePrice.Full"], cwd=LEAN, check=True)
    r = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=src, text=True,
                       encoding="utf-8", capture_output=True)
    output = r.stdout + r.stderr
    print(output, end="")
    validate_reports(output, r.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
