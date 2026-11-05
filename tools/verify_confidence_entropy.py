"""Audit the sharper general-law entropy-tail confidence coefficient."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ConfidenceEntropy.Full
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory InformationTheory Set Real
open scoped ENNReal NNReal
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier4
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.ConfidenceTransfer
open ThresholdHC.ConfidenceEntropy ThresholdHC.FiniteQuantile ThresholdHC.Genie
open ThresholdHC.EntropyTailLower ThresholdHC.EntropyTailSharp ThresholdHC.EntropyTailQuantile
open ThresholdHC.ConfidenceProgram

example : ∀ {n : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B t : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (ht : 0 < t)
    (hbefore : ∀ j < n, t ≤ bandEdge j)
    (hlarge : 262144 < prefixCoreEntropy μ n)
    (hcut : 32*(65536*(sqrt ρ/sqrt (prefixCoreEntropy μ n))) ≤ t),
    min ρ (sqrt (ρ*prefixCoreEntropy μ n/B)) ≤
      (16*10^14)*(infiniteProgramValue μ ρ B).toReal :=
  @ThresholdHC.ConfidenceEntropy.core_program_bound

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4),
    ENNReal.ofReal ((10 : ℝ)⁻¹^17)*closedQuantileValue μ ρ (B/Real.log (1/δ)) ≤
      rareConfidenceRadius μ ρ B δ :=
  @ThresholdHC.ConfidenceEntropy.closed_quantile_confidence_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4),
    ENNReal.ofReal ((10 : ℝ)⁻¹^17)*EntropyTail.selection μ ρ (B/Real.log (1/δ)) ≤
      rareConfidenceRadius μ ρ B δ :=
  @ThresholdHC.ConfidenceEntropy.entropy_tail_confidence_lower_explicit

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {ρ B δ ε : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) (hε : 0 ≤ ε)
    (hw : RareBudget μ A ρ B)
    (hc : ∀ q : SignLaw, RarePrior μ ρ q →
      ThresholdHC.Confidence.failureProbability μ A q ε ≤ ENNReal.ofReal δ),
    ENNReal.ofReal ((10 : ℝ)⁻¹^17)*EntropyTail.selection μ ρ (B/Real.log (1/δ)) ≤ ENNReal.ofReal ε :=
  @ThresholdHC.ConfidenceEntropy.estimator_confidence_lower_explicit

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4),
    let K := EntropyTail.selection μ ρ (B/Real.log (1/δ))
    ENNReal.ofReal ((10 : ℝ)⁻¹^17)*K ≤ rareConfidenceRadius μ ρ B δ ∧
      rareConfidenceRadius μ ρ B δ ≤ hardConfidenceRadius μ ρ B δ ∧
      hardConfidenceRadius μ ρ B δ ≤ 750000*K :=
  @ThresholdHC.ConfidenceEntropy.general_confidence_law_explicit

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B),
    ENNReal.ofReal (30*(10:ℝ)⁻¹^17)*closedQuantileValue μ ρ B ≤ infiniteProgramValue μ ρ B :=
  @ThresholdHC.ConfidenceEntropy.closed_quantile_program
""".lstrip()
    roots = {
        'ThresholdHC.ConfidenceEntropy.closed_quantile_confidence_lower',
        'ThresholdHC.ConfidenceEntropy.closed_quantile_program',
        'ThresholdHC.ConfidenceEntropy.core_program_bound',
        'ThresholdHC.ConfidenceEntropy.entropy_tail_confidence_lower_explicit',
        'ThresholdHC.ConfidenceEntropy.estimator_confidence_lower_explicit',
        'ThresholdHC.ConfidenceEntropy.general_confidence_law_explicit',
    }
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ConfidenceEntropy.Full"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
