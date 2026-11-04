"""Audit the uniform finite-cap bounds for the original optimized stopping programs."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.GenieRate.Full
noncomputable section
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie ThresholdHC.GenieRate
open scoped ENNReal
variable (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}
variable (hr : 0 < ρ) (hu : ρ ≤ 1/2) (hb : 0 < B) (N : ℕ)
example (k : ℝ) (hk : 1 < k) (hn : B ≤ N*(1-1/k)^2*(k^2-1)) :
    programValue μ ρ B N ≤ ENNReal.ofReal k * genieValue μ ρ B N :=
  optimized_cap_factor μ hr hu hb hk N hn
example (hn : 4*B/3 ≤ N) :
    programValue μ ρ B N ≤ 2*genieValue μ ρ B N ∧
    ThresholdHC.RareAboveTwo.rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
    programValue μ ρ B N ≤ 16*ThresholdHC.RareAboveTwo.rareMinimaxRisk μ ρ B :=
  linear_cap_risk_certificate μ hr hu hb N hn
example (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1) (hn : B ≤ N*t^3) :
    programValue μ ρ B N ≤ ENNReal.ofReal (1+2*t)*genieValue μ ρ B N :=
  cubic_cap_factor μ hr hu hb ht ht' N hn
""".lstrip()
    roots = {"ThresholdHC.GenieRate." + name for name in [
        "regularized_reveal_word", "terminal_mass_work", "mixedReferences", "mixedReferences_admissible",
        "mixed_genie_price", "optimized_cap_factor", "linear_cap_risk_certificate", "cubic_cap_factor",
    ]}
    roots.update({"ThresholdHC.Genie.genie_stopping_certificate", "ThresholdHC.StoppingProgram.strong_four_prior_duality"})
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.GenieRate.Full"], cwd=LEAN, check=True)
    result = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                            text=True, encoding="utf-8", capture_output=True)
    output = result.stdout + result.stderr
    print(output, end="")
    validate_reports(output, result.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
