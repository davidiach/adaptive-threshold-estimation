"""Audit observed-state proof components and their concrete experiment."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ObservedState.Experiment
import ThresholdHC.ObservedState.Garbling
import ThresholdHC.ObservedState.Rounding
noncomputable section
open MeasureTheory ProbabilityTheory Set ThresholdHC.ObservedState
open ThresholdHC.Tier6
open scoped ENNReal

example {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ) :
    (∫ s, target w s ∂signLaw q) = ∑ i, w i * (q i : ℝ) := target_mean q w

example {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ) :
    variance (target w) (signLaw q) = ∑ i, (w i) ^ 2 * (q i : ℝ) * (1 - (q i : ℝ)) :=
  target_variance q w

example {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ) {r : ℝ} (hr : 0 < r) :
    (signLaw q) {s | r < |target w s - ∑ i, w i * (q i : ℝ)|} ≤
      ENNReal.ofReal ((∑ i, (w i) ^ 2) / (4 * r ^ 2)) := target_concentration q w hr

example (b d : Gap) (hd : (d : ℝ) ≤ b) (s : Bool) :
    ((bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter s b)).prod
      (bernoulliMeasure true false (noiseRate b d hd))).map (fun z => Bool.xor z.1 z.2) =
        bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter s d) :=
  garbling_law b d hd s

example {m : ℕ} {R : Type} [MeasurableSpace R] (A : Estimator m R)
    (d : Fin m → Gap) (q : Fin m → unitInterval) : IsProbabilityMeasure (bayesLaw A d q) :=
  bayesLaw_probability A d q

example {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (q : Fin m → unitInterval) (B : ℝ)
    (hw : ∀ s, ThresholdHC.ObservedState.expectedWork A d s ≤ ENNReal.ofReal B) :
    (∫⁻ z, ThresholdHC.Tier3.totalProcessWork z.2 ∂bayesLaw A d q) ≤ ENNReal.ofReal B :=
  bayes_work_le A d q B hw

example (h : Gap) :
    ∃ T : Gap → Gap, Measurable T ∧ (Set.range T).Finite ∧
      (∀ d : Gap, d ≤ T d) ∧
      (∀ d : Gap, clippedGap h d ≤ 2 * clippedGap h (T d)) :=
  finite_upward_rounding h

example (μ : Measure Gap) (T : Gap → Gap) (hm : Measurable T)
    (hup : ∀ d, d ≤ T d) (x : ℝ) :
    (μ.map T) {d : Gap | (d : ℝ) ≤ x} ≤ μ {d : Gap | (d : ℝ) ≤ x} :=
  rounded_cdf_le μ T hm hup x

example (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap) (T : Gap → Gap) (hm : Measurable T)
    (hb : ∀ d, clippedGap h d ≤ 2 * clippedGap h (T d)) :
    modulus μ h / 2 ≤ modulus (μ.map T) h := rounded_modulus_lower μ h T hm hb
""".lstrip()
    roots = {"ThresholdHC.ObservedState." + name for name in [
        "target_memLp", "target_mean", "target_variance", "target_variance_le", "target_concentration",
        "garbled_parameter", "garbling_law", "measurable_observation", "modelLaw_probability",
        "signLaw_total", "bayesLaw_probability", "bayes_work_le", "measurable_raiseGap",
        "raiseGap_bounds", "raiseGap_clipped", "finite_upward_rounding",
        "rounded_cdf_le", "rounded_modulus_lower",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ObservedState.Experiment",
                    "ThresholdHC.ObservedState.Garbling", "ThresholdHC.ObservedState.Rounding"],
                   cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
