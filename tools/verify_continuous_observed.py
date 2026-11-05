"""Audit the adaptive noise simulation for observed-state queries."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ContinuousObserved.Word
import ThresholdHC.ContinuousObserved.LowerReduction
import ThresholdHC.ContinuousObserved.FreshObservation
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6
open ThresholdHC.ObservedState ThresholdHC.ContinuousObserved
open ThresholdHC.CriticalEntropy

example (g : List Bool → Bool → Bool) (x : ProcessTape) (n : ℕ) :
    processHistory (decodeTape g x) n = decode g (processHistory x n) :=
  decodeTape_history g x n

example (g : List Bool → Bool → Bool) (x : ProcessTape) :
    totalProcessWork (decodeTape g x) = totalProcessWork x := decodeTape_work g x

example (b d : Gap) (hd : (d : ℝ) ≤ b) (s : Bool) :
    ((bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter s b)).prod uniformUnitMeasure).map
      (fun z => Bool.xor z.1 (uniformCoinFlip (noiseRate b d hd) z.2)) =
        bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter s d) :=
  uniform_garbling_law b d hd s

example :
    MeasurePreserving (fun v : ℕ → ℝ => (v 0,uniformTail v)) uniformTapeMeasure
      (uniformUnitMeasure.prod uniformTapeMeasure) := uniform_head_tail_preserving

example {N : ℕ} {R : Type} [MeasurableSpace R] (D : QueryDesign N) (A : StateEstimator R)
    (s : Fin N → Bool) : IsProbabilityMeasure (queryLaw D A s) := queryLaw_probability D A s

example {N : ℕ} {R : Type} [MeasurableSpace R] (D : QueryDesign N) (A : StateEstimator R)
    (s : Fin N → Bool) :
    (∫⁻ z, totalProcessWork z.2 ∂queryLaw D A s) =
      ThresholdHC.ObservedState.expectedWork (reduction D A) D.cap s := reduction_work D A s

example {N : ℕ} {R : Type} [MeasurableSpace R] (D : QueryDesign N) (A : StateEstimator R)
    (s : Fin N → Bool) (r θ : ℝ) :
    queryLaw D A s {z | r < |A.output z - θ|} =
      modelLaw (reduction D A) D.cap s {z | r < |(reduction D A).output z - θ|} :=
  reduction_error D A s r θ

example (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap)
    {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1 / 8) (D : CellDesign μ h δ)
    {R : Type} [MeasurableSpace R] (A : StateEstimator R) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ s, (∫⁻ z, totalProcessWork z.2 ∂queryLaw (CellDesign.queryDesign μ h δ D) A s) ≤ ENNReal.ofReal B)
    (hc : ∀ s, queryLaw (CellDesign.queryDesign μ h δ D) A s
      {z | cellDelta D.cap D.cell h / 4 < |A.output z - stateTarget D.cell s|} ≤ ENNReal.ofReal δ) :
    (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B :=
  simulated_confidence_lower μ h hδ hd D A hB hw hc

example {N : ℕ} (D : QueryDesign N) (c : List Bool → Bool)
    (q : List Bool → unitInterval) (n : ℕ) (v : ℕ → ℝ) (raw : Fin N → ℕ → Bool) :
    noisyWord D c q n v raw =
      decodePrefix (stepNoise D q v) (populationSimulation (rawPolicy D c q v) n raw).2 :=
  noisyWord_decode D c q n v raw

example {N : ℕ} (cap : Fin N → Gap) (s : Fin N → Bool)
    (j : Fin N) (d : Gap) (hd : (d : ℝ) ≤ cap j) :
    MeasurePreserving
      (fun z : (ℕ → ℝ) × (Fin N → ℕ → Bool) =>
        (Bool.xor (z.2 j 0) (uniformCoinFlip (noiseRate (cap j) d hd) (z.1 0)),
          (uniformTail z.1,Function.update z.2 j (tapeDrop 1 (z.2 j)))))
      (uniformTapeMeasure.prod (Measure.pi (fun i =>
        Tier2.tapeMeasure (ThresholdHC.ObservableSimulation.gapParameter (s i) (cap i)))))
      ((bernoulliMeasure true false (ThresholdHC.ObservableSimulation.gapParameter (s j) d)).prod
        (uniformTapeMeasure.prod (Measure.pi (fun i =>
          Tier2.tapeMeasure (ThresholdHC.ObservableSimulation.gapParameter (s i) (cap i)))))) :=
  fresh_observation_preserving cap s j d hd
""".lstrip()
    roots = {"ThresholdHC.ContinuousObserved." + name for name in [
        "decode_length", "decode_append", "decode_append_singleton", "measurable_decode",
        "decodeTape_isSome", "processHistory_succ", "decodeTape_history", "decodeTape_work",
        "measurable_decodeTape", "measurable_noiseRate", "uniform_garbling_law",
        "measurable_perturb", "measurable_decoded", "queryLaw_probability", "reduction_work",
        "reduction_error", "simulated_confidence_lower", "measurable_uniformTail", "uniformTail_map",
        "uniform_head_tail_independent", "uniform_head_tail_preserving", "decodePrefix_processPrefix",
        "decodePrefix_none", "decodePrefix_cons_none", "decodePrefix_cons_some",
        "stepNoise_shift", "rawPolicy_shift", "noisyWord_decode",
        "fresh_pair_preserving", "fresh_observation_preserving",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ContinuousObserved.Word",
                    "ThresholdHC.ContinuousObserved.LowerReduction",
                    "ThresholdHC.ContinuousObserved.FreshObservation"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
