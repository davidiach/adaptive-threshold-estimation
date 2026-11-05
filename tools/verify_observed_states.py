"""Audit observed-state proof components and their concrete experiment."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ObservedState.FiniteLower
import ThresholdHC.ObservedState.Replication
import ThresholdHC.ObservedState.Garbling
import ThresholdHC.ObservedState.Rounding
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set ThresholdHC ThresholdHC.ObservedState
open ThresholdHC.Tier3 ThresholdHC.Tier4
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

example {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Tier6.Gap) (q : Fin m → unitInterval) :
    RealizesPrefixes A.randomLaw (bayesLaw A d q) Prod.fst Prod.snd A.policy
      (fun i => d i) (fun i => q i) :=
  bayes_realizes A d q

example {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (η : Fin m → ℝ)
    (qp qm : Fin m → unitInterval)
    (hp : ∀ i, (qp i : ℝ) = 1 / 2 + η i) (hm : ∀ i, (qm i : ℝ) = 1 / 2 - η i)
    {B h : ℝ} (hh : 0 < h) (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1 / 8)
    (hd : ∀ i, (d i : ℝ) * η i ≤ h / 8)
    (hw : ∀ s, ThresholdHC.ObservedState.expectedWork A d s ≤ ENNReal.ofReal B) :
    klDiv (bayesLaw A d qp) (bayesLaw A d qm) ≤
      ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2 * B) :=
  bayes_information_bound A d η qp qm hp hm hh hη hd hw

example {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Set Ω) (hE : MeasurableSet E) {e : ℝ} (he : 0 < e) (he1 : e < 1 / 2)
    (hP : 1 - e ≤ P.real E) (hQ : Q.real E ≤ e) :
    ENNReal.ofReal (klB (1 - e) e) ≤ klDiv P Q :=
  event_information_lower P Q E hE he he1 hP hQ

example {m : ℕ} {R : Type} [MeasurableSpace R]
    (A : Estimator m R) (d : Fin m → Gap) (w η : Fin m → ℝ)
    (qp qm : Fin m → unitInterval)
    (hp : ∀ i, (qp i : ℝ) = 1 / 2 + η i) (hm : ∀ i, (qm i : ℝ) = 1 / 2 - η i)
    {B h Δ δ : ℝ} (hB : 0 ≤ B) (hh : 0 < h) (hΔ : 0 < Δ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1 / 8)
    (hd : ∀ i, (d i : ℝ) * η i ≤ h / 8)
    (hsep : (∑ i, w i * (qp i : ℝ)) - (∑ i, w i * (qm i : ℝ)) = Δ)
    (hweights : (∑ i, (w i) ^ 2) ≤ δ * Δ ^ 2 / 16)
    (hw : ∀ s, ThresholdHC.ObservedState.expectedWork A d s ≤ ENNReal.ofReal B)
    (hc : ThresholdHC.ObservedState.UniformConfidence A d w (Δ / 4) δ) :
    (225 / (128 * h ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B :=
  finite_confidence_lower A d w η qp qm hp hm hB hh hΔ hδ hδ1 hη hd hsep hweights hw hc

example {I : Type} [Fintype I] (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : (∑ i, w i) = 1)
    {M : ℕ} (hM : 0 < M) :
    (∑ i : I × Fin M, (replicatedWeight w M i) ^ 2) ≤ 1 / M :=
  replicated_square_le w hw hs hM

example {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ 1 / (M : ℝ) ≤ δ * Δ ^ 2 / 16 :=
  replication_count hΔ hδ
""".lstrip()
    roots = {"ThresholdHC.ObservedState." + name for name in [
        "target_memLp", "target_mean", "target_variance", "target_variance_le", "target_concentration",
        "garbled_parameter", "garbling_law", "measurable_observation", "modelLaw_probability",
        "signLaw_total", "bayesLaw_probability", "bayes_work_le", "measurable_raiseGap",
        "raiseGap_bounds", "raiseGap_clipped", "finite_upward_rounding",
        "rounded_cdf_le", "rounded_modulus_lower",
        "fixed_word_law", "model_prefix_integral", "signLaw_singleton", "measurable_pathProb_policy",
        "bayes_realizes", "bayes_information_bound", "event_information_lower", "bayes_event_bound",
        "small_weights_concentrate", "finite_confidence_lower", "replicated_sum", "replicated_moment",
        "replicated_square_sum", "replicated_square_le", "replication_count",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ObservedState.FiniteLower", "ThresholdHC.ObservedState.Replication",
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
