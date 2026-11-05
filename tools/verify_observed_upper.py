"""Audit the fresh-outer-state transfer to the population estimator."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ContinuousObserved.StateParameter
import ThresholdHC.ContinuousObserved.SampledPolicy
noncomputable section
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState
open ThresholdHC.ContinuousObserved ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

example {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = μ) :
    μ.withDensity (fun d => ENNReal.ofReal ((conditionalSign μ D s).val d)) = positiveGapLaw D s :=
  conditionalSign_density μ D s hl

example {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = μ)
    (F : Gap → ℝ) (hF : Measurable F) :
    (∫ d, (conditionalSign μ D s).val d * F d ∂μ) =
      ∫ u in {u : unitInterval | s (D.cell u) = true}, F (D.gap u) :=
  conditionalSign_positive_integral μ D s hl F hF

example {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = μ) :
    volume.map (stateParameter D s) =
      populationParameterLaw μ (gapParameter false) (gapParameter true) (signUnit (conditionalSign μ D s)) :=
  state_parameter_law μ D s hl

example {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = μ) :
    signMean μ (conditionalSign μ D s).val = stateTarget D.cell s := conditionalSign_target μ D s hl

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) :
    (sampledStateEstimator A).randomLaw = A.randomLaw.prod outerSequenceLaw := rfl

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (z : (R × (ℕ → unitInterval)) × ProcessTape) :
    (sampledStateEstimator A).output z = A.output (z.1.1,z.2) := rfl
""".lstrip()
    roots = {"ThresholdHC.ContinuousObserved." + name for name in [
        "positiveGapLaw_finite", "positiveGapLaw_le", "conditionalSign_density",
        "conditionalSign_positive_integral", "positiveState_measurable", "measurable_stateParameter",
        "conditionalSign_target", "state_parameter_law", "outerSequenceLaw_probability", "sampledStateEstimator",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ContinuousObserved.StateParameter",
                    "ThresholdHC.ContinuousObserved.SampledPolicy"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
